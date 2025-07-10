with Interfaces; use Interfaces;
package body Sign
  with Spark_Mode => On
is

   procedure Keypair_Internal (PK   :    out Bytes_PK;
                               SK   :    out Bytes_SK;
                               Seed : in     Bytes_Seed)
   is
      KeyPair_Seed : Bytes_KeyPair_Seed;
      Rho, Key     : Bytes_Seed;
      Rho_Prime    : Bytes_Crh;
      Mat          : Polyvec_Matrix;
      S1           : Valid_Eta_Polyvec_L;
      S1_Hat       : Polyvec_L;
      S2           : Valid_Eta_Polyvec_K;
      T0, T1, T2   : Polyvec_K;
      TR           : Bytes_Tr;
   begin
      SHAKE256 (KeyPair_Seed, Seed & U8'(K) & U8'(L));

      -- 1 .. 32
      Rho := KeyPair_Seed (1 .. SEEDBYTES);

      -- 33 .. 96
      Rho_Prime := KeyPair_Seed (SEEDBYTES + 1 .. SEEDBYTES + CRHBYTES);

      -- 97 .. 128
      Key := KeyPair_Seed (SEEDBYTES + CRHBYTES + 1 .. KeyPair_Seed'Last);

      Matrix_Expand (Mat, Rho);

      -- MLDSA_MODE=3, so K=6 and L=5, so we need 11 useful
      -- Poly's and one dummy to make up the numbers
      declare
         V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11 : Valid_Eta_Poly;
         Dummy : Valid_Eta_Poly;
      begin
         Poly_Uniform_Eta_4x (V1,
                              V2,
                              V3,
                              V4,
                              Rho_Prime,
                              0, 1, 2, 3);

         Poly_Uniform_Eta_4x (V5,
                              V6,
                              V7,
                              Dummy,
                              Rho_Prime,
                              4, 5, 6, 16#FF#);

         Poly_Uniform_Eta_4x (V8,
                              V9,
                              V10,
                              V11,
                              Rho_Prime,
                              7, 8, 9, 10);

         S1 := Valid_Eta_Polyvec_L'(Vec => Poly_L'(V1, V2, V3, V4, V5));
         S2 := Valid_Eta_Polyvec_K'(Vec => Poly_K'(V6, V7, V8, V9, V10, V11));
      end;

      --  Matrix-Vector multiplication
      S1_Hat := S1;
      NTTL (S1_Hat);
      Matrix_Pointwise_Montgomery (T1, Mat, S1_Hat);
      Reduce (T1);
      Inv_NTTK (T1);
      --  Add error vector S2
      Add (T1, S2);

      --  Extract T1 and write public key
      CAddQ (T1);
      Power2Round (T2, T0, T1); -- RCC de-alias
      Pack_PK (PK, Rho, T2);
      SHAKE256 (Tr, PK);
      Pack_SK (SK, Rho, Tr, Key, T0, S1, S2);
   end Keypair_Internal;


   procedure Signature_Internal (Sig    :    out Bytes_Crypto;
                                 OK     :    out Boolean;
                                 M      : in     Byte_Seq;
                                 Prefix : in     Byte_Seq;
                                 Rnd    : in     Bytes_Rnd;
                                 SK     : in     Bytes_SK;
                                 ExtMu  : in     Boolean)
   is
      Rho      : Bytes_Seed;
      Tr       : Bytes_Tr;
      Key      : Bytes_Seed;
      Mu       : Bytes_Crh;
      RhoPrime : Bytes_Crh;

      S1, Z, Y              : Polyvec_L;
      T0, S2, W2, W1, W0, H : Polyvec_K;

      Mat             : Polyvec_Matrix;
      Packed_W1       : Bytes_Packed_W1;
      Challenge_Bytes : Bytes_CTilde;

      CP        : Poly;
      Nonce     : U16;
      Num_Hints : U32;
   begin
      OK := True;
      Nonce := 0;
      Unpack_SK (Rho, Tr, Key, T0, S1, S2, SK);
      if ExtMu then
         Mu := M (1 .. CRHBYTES);
      else
         SHAKE256 (Mu, Tr, Prefix, M);
      end if;
      SHAKE256 (Rhoprime, Key, Rnd, Mu);

      Matrix_Expand (Mat, Rho);
      NTTL (S1);
      NTTK (S2);
      NTTK (T0);

      loop
         pragma Loop_Invariant (Nonce <= Nonce_UB);
         if Nonce = Nonce_UB then
            Sig := (others => 0);
            OK  := False;
            return;
         end if;

         Uniform_Gamma1 (Y, RhoPrime, Nonce);
         Nonce := Nonce + 1;

         Z := Y;
         NTTL (Z);
         pragma Assert (Mat in Polyvec_Matrix);
         Matrix_Pointwise_Montgomery (W1, Mat, Z);

         Reduce (W1);
         Inv_NTTK (W1);

         CAddQ (W1);
         Decompose (W2, W0, W1);
         Pack_W1 (Packed_W1, W2);

         Shake256 (Challenge_Bytes, Mu, Packed_W1);
         Challenge (CP, Challenge_Bytes);
         NTT (CP);

         Pointwise_Poly_Montgomery (Z, CP, S1);
         Inv_NTTL (Z);

         Add (Z, Y);
         Reduce (Z);

         if Chknorm (Z, GAMMA1 - BETA) then

            -- If Z is OK, then it meets the pre-condition of Pack_Sig()
            pragma Assert (Z in Valid_Gamma1_Polyvec_L);

            Pointwise_Poly_Montgomery (H, CP, S2);
            Inv_NTTK (H);

            pragma Assert (W0 in Valid_Decomposed_V0_Polyvec_K);
            pragma Assert (H in Valid_INTT_Polyvec_K);
            Sub (W0, H);
            Reduce (W0);

            if Chknorm (W0, GAMMA2 - BETA) then
               Pointwise_Poly_Montgomery (H, CP, T0);
               Inv_NTTK (H);
               Reduce (H);
               if Chknorm (H, GAMMA2) then

                  pragma Assert (W0 in Valid_Gamma2_Polyvec_K);
                  pragma Assert (H  in Valid_Gamma2_Polyvec_K);
                  --  All coeffs in -261887 .. 261887
                  Add (W0, H);
                  Make_Hint (H, Num_Hints, W0, W2);
                  if Num_Hints <= Omega then
                     Pack_Sig (Sig, Challenge_Bytes, Z, H, Num_Hints);
                     exit;
                  end if;
               end if;
            end if;
         end if;
      end loop;
   end Signature_Internal;

   function Verify_Internal (Sig    : in Bytes_Crypto;
                             M      : in Byte_Seq;
                             Prefix : in Byte_Seq;
                             PK     : in Bytes_PK;
                             ExtMu  : in Boolean) return Boolean
   is
      Rho : Bytes_Seed;
      T1  : Polyvec_K;
      T2  : Polyvec_K;
      C   : Bytes_CTilde;
      C2  : Bytes_CTilde;
      Z   : Polyvec_L;
      H   : Polyvec_K;
      Sig_OK : Boolean;

      Tr  : Bytes_Tr;
      Mu  : Bytes_Crh;
      CP  : Poly;
      Mat : Polyvec_Matrix;
      W1  : Reduce32_Domain_Polyvec_K;
      W2  : Valid_Decomposed_V1_Polyvec_K;

      Buf : Bytes_Packed_W1;
   begin
      Unpack_PK (Rho, T1, PK);
      Unpack_Sig (C, Z, H, Sig_OK, Sig);
      if Sig_OK then

         pragma Assert (Z in Valid_Gamma1_Polyvec_L);
         pragma Assert (H in Valid_Hint_Polyvec_K);

         if Chknorm (Z, GAMMA1 - BETA) then
            if ExtMu then
               Mu := M (1 .. CRHBYTES);
            else
               Shake256(Tr, PK);
               Shake256(Mu, Tr, Prefix, M);
            end if;

            Challenge (CP, C);
            Matrix_Expand(Mat, Rho);

            NTTL (Z);

            pragma Assert (Z in Valid_NTT_Polyvec_L); -- From post of NTTL - all in -NTT_BOUND .. NTT_BOUND
                                                      -- NTT_BOUND is 9Q-1
            pragma Assert (Mat in Polyvec_Matrix); -- All Natural 0 .. QM1
            Matrix_Pointwise_Montgomery (W1, Mat, Z);

            -- All Coeffs in W1 should be result of a montgomery_reduce()
            NTT (CP);

            ShiftL (T1);
            NTTK (T1);
            Pointwise_Poly_Montgomery (T2, CP, T1); -- RCC de-alias

            pragma Assert (W1 in Valid_Signed_Polyvec_K);
            pragma Assert (T2 in Valid_Signed_Polyvec_K);
            Sub (W1, T2);
            Reduce (W1);

            Inv_NTTK (W1);

            CAddQ (W1);
            Use_Hint (W2, W1, H); -- RCC de-alias
            Pack_W1 (Buf, W2);

            SHAKE256 (C2, Mu, Buf);

            for I in Ctildebytes_Index loop
               if C (I) /= C2 (I) then
                  return False;
               end if;
            end loop;

            return True;
         else
            return False;
         end if;
      else
         return False;
      end if;
   end Verify_Internal;



end Sign;

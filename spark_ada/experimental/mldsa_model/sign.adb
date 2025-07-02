with Interfaces; use Interfaces;
package body Sign
  with Spark_Mode => On
is

   procedure Signature_Internal (Sig    :    out Bytes_Crypto;
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
            pragma Assert (Z in Valid_Gamma_Polyvec_L);

            Pointwise_Poly_Montgomery (H, CP, S2);
            Inv_NTTK (H);
            Sub (W0, H);
            Reduce (W0);

            if Chknorm (W0, GAMMA2 - BETA) then
               Pointwise_Poly_Montgomery (H, CP, T0);
               Inv_NTTK (H);
               Reduce (H);
               if Chknorm (H, GAMMA2) then
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

      Buf : Bytes_Packed_W1;
   begin
      Unpack_PK (Rho, T1, PK);
      Unpack_Sig (C, Z, H, Sig_OK, Sig);
      if Sig_OK then

         pragma Assert (Z in Valid_Gamma_Polyvec_L);
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

--            pragma Assert (CP in Challenge_Poly);
--            pragma Assert (CP in Valid_Signed_Poly);

            NTT (CP);

--            pragma Assert (T1 in Valid_PK_Polyvec_K); -- OK all in 0 .. 1023
            ShiftL (T1);

--            pragma Assert (T1 in Valid_Natural_Polyvec_K);
--            pragma Assert (T1 in Valid_Signed_Polyvec_K);
            NTTK (T1);

            Pointwise_Poly_Montgomery (T2, CP, T1); -- RCC de-alias

            -- All T2 in -QM1 .. QM1
            pragma Assert (T2 in Valid_Signed_Polyvec_K); -- from above

            -- All W1 coeffs in I32'First .. REDUCE32_DOMAIN_MAX;
            -- REDUCE32_DOMAIN_MAX = (I32'Last - (2 ** 22) - 1);
            pragma Assert (W1 in Reduce32_Domain_Polyvec_K);

            Sub (W1, T2);
            Reduce (W1);
            Inv_NTTK (W1);

            CAddQ (W1);
            Use_Hint (W1, W1, H);
            Pack_W1 (Buf, W1);

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

with Interfaces; use Interfaces;
package MLDSA
  with SPARK_Mode => On
is
   SEEDBYTES : constant := 32;
   CRHBYTES : constant := 64;
   KEYPAIR_SEEDBYTES : constant := 2 * SEEDBYTES + CRHBYTES;

   TRBYTES  : constant := 64;
   RNDBYTES  : constant := 32;
   N   : constant := 256;
   Q   : constant := 8380417;
   QM1 : constant := Q - 1;
   D   : constant := 13;

   NTT_BOUND : constant := (Q * 9) - 1;
   INTT_BOUND : constant := 4_211_138;

   K : constant := 6;
   L : constant := 5;

   ETA      : constant := 4;
   TAU      : constant := 49;
   BETA     : constant := 196;
   GAMMA1   : constant := 2 ** 19;
   GAMMA1M1 : constant := GAMMA1 - 1;
   GAMMA2   : constant := (QM1 / 32); -- 261888
   GAMMA2M1 : constant := GAMMA2 - 1; -- 261887
   OMEGA    : constant := 55;


   CTILDEBYTES : constant := 48;
   POLYW1_PACKEDBYTES  : constant := 128;
   POLYETA_PACKEDBYTES : constant := 128;
   POLYZ_PACKEDBYTES   : constant := 640;

   POLYT0_PACKEDBYTES   : constant := 416;
   POLYT1_PACKEDBYTES   : constant := 320;
   POLYVECH_PACKEDBYTES : constant := OMEGA + K;

   CRYPTO_SECRETKEYBYTES : constant :=
     (2 * SEEDBYTES + TRBYTES + L * POLYETA_PACKEDBYTES +
      K * POLYETA_PACKEDBYTES + K * POLYT0_PACKEDBYTES);

   CRYPTO_PUBLICKEYBYTES : constant :=
     SEEDBYTES + K * POLYT1_PACKEDBYTES;

   CRYPTO_BYTES : constant :=
     (CTILDEBYTES + L * POLYZ_PACKEDBYTES + POLYVECH_PACKEDBYTES);

   subtype U8  is Unsigned_8;
   subtype U16 is Unsigned_16;
   subtype U32 is Unsigned_32;
   subtype I32 is Integer_32;
   subtype I64 is Integer_64;

   Nonce_UB : constant U16 := ((U16'Last - L) / L);

   REDUCE32_DOMAIN_MAX : constant I32 := (I32'Last - (2 ** 22) - 1);
   REDUCE32_RANGE_MAX  : constant I32 := 6283009;

   type Byte_Seq is array (Natural range <>) of U8;

   type I32_Seq is array (Natural range <>) of I32;

   subtype SeedBytes_Index is Positive range 1 .. SEEDBYTES;
   subtype KeyPair_SeedBytes_Index is Positive range 1 .. KEYPAIR_SEEDBYTES;
   subtype CTildeBytes_Index is Positive range 1 .. CTILDEBYTES;
   subtype RndBytes_Index is Positive range 1 .. RNDBYTES;
   subtype TrBytes_Index is Positive range 1 .. TRBYTES;
   subtype CrhBytes_Index is Positive range 1 .. CRHBYTES;
   subtype SK_Index is Positive range 1 .. CRYPTO_SECRETKEYBYTES;
   subtype PK_Index is Positive range 1 .. CRYPTO_PUBLICKEYBYTES;
   subtype Crypto_Index is Positive range 1 .. CRYPTO_BYTES;

   subtype Packed_W1_Index is Positive range 1 .. (K * POLYW1_PACKEDBYTES);

   subtype Bytes_Rnd is Byte_Seq (RndBytes_Index);
   subtype Bytes_Seed is Byte_Seq (SeedBytes_Index);
   subtype Bytes_KeyPair_Seed is Byte_Seq (KeyPair_SeedBytes_Index);
   subtype Bytes_CTilde is Byte_Seq (CTildeBytes_Index);
   subtype Bytes_Tr is Byte_Seq (TrBytes_Index);
   subtype Bytes_Crh is Byte_Seq (CrhBytes_Index);
   subtype Bytes_SK is Byte_Seq (SK_Index);
   subtype Bytes_PK is Byte_Seq (PK_Index);
   subtype Bytes_Crypto is Byte_Seq (Crypto_Index);
   subtype Bytes_Packed_W1 is Byte_Seq (Packed_W1_Index);

   subtype N_Index is Positive range 1 .. N;
   subtype L_Index is Positive range 1 .. L;
   subtype K_Index is Positive range 1 .. K;

   subtype I32_N is I32_Seq (N_Index);

   type Poly is record
      Coeffs : I32_N;
   end record;

   type Poly_K is array (K_Index) of Poly;
   type Poly_L is array (L_Index) of Poly;

   type Polyvec_L is record
      Vec : Poly_L;
   end record;

   type Polyvec_K is record
      Vec : Poly_K;
   end record;

   subtype Valid_SK_Coeff is I32 range -(2**(D - 1)) + 1 .. (2**(D - 1));
   subtype Valid_Natural_SK_Coeff is I32 range 0 .. 2**D - 1;
   subtype Valid_PK_Coeff is I32 range 0 .. 1023;
   subtype Valid_Natural_Coeff is I32 range 0 .. QM1;
   subtype Valid_Signed_Coeff is I32 range -QM1 .. QM1;
   subtype Valid_NTT_Coeff is I32 range -NTT_BOUND .. NTT_BOUND;
   subtype Valid_INTT_Coeff is I32 range -INTT_BOUND .. INTT_BOUND;
   subtype Valid_Gamma1_Coeff is I32 range -GAMMA1M1 .. GAMMA1M1;

      subtype Valid_Gamma2_Coeff is I32 range -GAMMA2M1 .. GAMMA2M1;
   subtype Valid_Eta_Coeff is I32 range -ETA .. ETA;
   subtype Hint_Coeff is I32 range 0 .. 1;

   subtype Packed_W1_Coeff is I32 range 0 .. ((Q - 1) / (2 * GAMMA2)) - 1;

   subtype Valid_Decomposed_V1_Coeff is I32
     range 0 .. ((Q - 1) / (2 * GAMMA2)) - 1;

   subtype Valid_Decomposed_V0_Coeff is I32
     range -GAMMA2 .. GAMMA2;

   subtype Challenge_Coeff is I32 range -1 .. 1;

   subtype Reduce32_Domain is I32 range I32'First .. REDUCE32_DOMAIN_MAX;
   subtype Reduce32_Range  is I32 range -REDUCE32_RANGE_MAX .. (REDUCE32_RANGE_MAX - 1);

   subtype Valid_SK_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_SK_Poly.Coeffs (I) in Valid_SK_Coeff);

   subtype Valid_Natural_SK_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_Natural_SK_Poly.Coeffs (I) in Valid_Natural_SK_Coeff);

   subtype Valid_PK_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_PK_Poly.Coeffs (I) in Valid_PK_Coeff);

   subtype Valid_Natural_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_Natural_Poly.Coeffs (I) in Valid_Natural_Coeff);

   subtype Valid_Signed_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_Signed_Poly.Coeffs (I) in Valid_Signed_Coeff);

   subtype Valid_NTT_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_NTT_Poly.Coeffs (I) in Valid_NTT_Coeff);

   subtype Valid_INTT_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_INTT_Poly.Coeffs (I) in Valid_INTT_Coeff);

   subtype Valid_Gamma1_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_Gamma1_Poly.Coeffs (I) in Valid_Gamma1_Coeff);

   subtype Valid_Gamma2_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_Gamma2_Poly.Coeffs (I) in Valid_Gamma2_Coeff);

   subtype Valid_Eta_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_Eta_Poly.Coeffs (I) in Valid_Eta_Coeff);

   subtype Valid_Decomposed_V0_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_Decomposed_V0_Poly.Coeffs (I) in Valid_Decomposed_V0_Coeff);

   subtype Valid_Decomposed_V1_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Valid_Decomposed_V1_Poly.Coeffs (I) in Valid_Decomposed_V1_Coeff);


   subtype Reduce32_Domain_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Reduce32_Domain_Poly.Coeffs (I) in Reduce32_Domain);

   subtype Reduce32_Range_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Reduce32_Range_Poly.Coeffs (I) in Reduce32_Range);

   subtype Packed_W1_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Packed_W1_Poly.Coeffs (I) in Packed_W1_Coeff);

   subtype Hint_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
          Hint_Poly.Coeffs (I) in Hint_Coeff);

   subtype Valid_SK_Polyvec_L is Polyvec_L
     with Dynamic_Predicate => (for all I in L_Index =>
          Valid_SK_Polyvec_L.Vec (I) in Valid_SK_Poly);

   subtype Valid_Natural_Polyvec_L is Polyvec_L
     with Dynamic_Predicate => (for all I in L_Index =>
          Valid_Natural_Polyvec_L.Vec (I) in Valid_Natural_Poly);

   subtype Valid_Natural_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_Natural_Polyvec_K.Vec (I) in Valid_Natural_Poly);

   subtype Valid_Signed_Polyvec_L is Polyvec_L
     with Dynamic_Predicate => (for all I in L_Index =>
          Valid_Signed_Polyvec_L.Vec (I) in Valid_Signed_Poly);

   subtype Valid_Gamma1_Polyvec_L is Polyvec_L
     with Dynamic_Predicate => (for all I in L_Index =>
          Valid_Gamma1_Polyvec_L.Vec (I) in Valid_Gamma1_Poly);

   subtype Valid_Gamma2_Polyvec_L is Polyvec_L
     with Dynamic_Predicate => (for all I in L_Index =>
          Valid_Gamma2_Polyvec_L.Vec (I) in Valid_Gamma2_Poly);

   subtype Valid_Gamma2_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_Gamma2_Polyvec_K.Vec (I) in Valid_Gamma2_Poly);

   subtype Valid_Eta_Polyvec_L is Polyvec_L
     with Dynamic_Predicate => (for all I in L_Index =>
          Valid_Eta_Polyvec_L.Vec (I) in Valid_Eta_Poly);

   subtype Valid_Eta_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_Eta_Polyvec_K.Vec (I) in Valid_Eta_Poly);

   subtype Valid_Signed_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_Signed_Polyvec_K.Vec (I) in Valid_Signed_Poly);

   subtype Valid_NTT_Polyvec_L is Polyvec_L
     with Dynamic_Predicate => (for all I in L_Index =>
          Valid_NTT_Polyvec_L.Vec (I) in Valid_NTT_Poly);

   subtype Valid_NTT_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_NTT_Polyvec_K.Vec (I) in Valid_NTT_Poly);

   subtype Valid_INTT_Polyvec_L is Polyvec_L
     with Dynamic_Predicate => (for all I in L_Index =>
          Valid_INTT_Polyvec_L.Vec (I) in Valid_INTT_Poly);

   subtype Valid_INTT_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_INTT_Polyvec_K.Vec (I) in Valid_INTT_Poly);

   subtype Valid_SK_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_SK_Polyvec_K.Vec (I) in Valid_SK_Poly);

   subtype Valid_Natural_SK_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_Natural_SK_Polyvec_K.Vec (I) in Valid_Natural_SK_Poly);

   subtype Valid_PK_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_PK_Polyvec_K.Vec (I) in Valid_PK_Poly);

   subtype Valid_Decomposed_V0_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_Decomposed_V0_Polyvec_K.Vec (I) in Valid_Decomposed_V0_Poly);

   subtype Valid_Decomposed_V1_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_Decomposed_V1_Polyvec_K.Vec (I) in Valid_Decomposed_V1_Poly);

   subtype Valid_Hint_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Valid_Hint_Polyvec_K.Vec (I) in Hint_Poly);

   procedure Unpack_SK (Rho :    out Bytes_Seed;
                        Tr  :    out Bytes_Tr;
                        Key :    out Bytes_Seed;
                        T0  :    out Valid_SK_Polyvec_K;
                        S1  :    out Valid_SK_Polyvec_L;
                        S2  :    out Valid_SK_Polyvec_K;
                        SK  : in     Bytes_SK)
     with Always_Terminates, Global => null;

   procedure Pack_SK (SK  :    out Bytes_SK;
                      Rho : in     Bytes_Seed;
                      Tr  : in     Bytes_Tr;
                      Key : in     Bytes_Seed;
                      T0  : in     Valid_SK_Polyvec_K;
                      S1  : in     Valid_SK_Polyvec_L;
                      S2  : in     Valid_SK_Polyvec_K)
     with Always_Terminates, Global => null;

   procedure Unpack_PK (Rho :    out Bytes_Seed;
                        T1  :    out Valid_PK_Polyvec_K;
                        PK  : in     Bytes_PK)
     with Always_Terminates, Global => null;

   procedure Pack_PK (PK  :    out Bytes_PK;
                      Rho : in     Bytes_Seed;
                      T1  : in     Valid_PK_Polyvec_K)
     with Always_Terminates, Global => null;


   procedure Unpack_Sig (C : out Bytes_CTilde;
                         Z : out Polyvec_L;
                         H : out Polyvec_K;
                         OK : out Boolean;
                         Sig : in Bytes_Crypto)
     with Always_Terminates,
          Global => null,
          Post => (OK = (Z in Valid_Gamma1_Polyvec_L and H in Valid_Hint_Polyvec_K)); -- RCC Stronger

   procedure SHAKE256 (R : out Byte_Seq;
                       D1 : in Byte_Seq)
     with Always_Terminates, Global => null;

   procedure SHAKE256 (R : out Byte_Seq;
                       D1 : in Byte_Seq;
                       D2 : in Byte_Seq)
     with Always_Terminates, Global => null;

   procedure SHAKE256 (R : out Byte_Seq;
                       D1 : in Byte_Seq;
                       D2 : in Byte_Seq;
                       D3 : in Byte_Seq)
     with Always_Terminates, Global => null;


   type Polyvec_Matrix is array (K_Index) of Valid_Natural_Polyvec_L;

   procedure Matrix_Expand (Mat : out Polyvec_Matrix;
                            Rho : in Bytes_Seed)
     with Always_Terminates, Global => null;

   procedure NTTL (V : in out Polyvec_L)
     with Always_Terminates, Global => null,
          Pre    => V in Valid_Signed_Polyvec_L,
          Post   => V in Valid_NTT_Polyvec_L;

   procedure NTTK (V : in out Polyvec_K)
     with Always_Terminates, Global => null,
          Pre    => V in Valid_Signed_Polyvec_K,
          Post   => V in Valid_NTT_Polyvec_K;

   procedure NTT (V : in out Poly)
     with Always_Terminates, Global => null,
          Pre    => V in Valid_Signed_Poly,
          Post   => V in Valid_NTT_Poly;

   procedure Inv_NTTL (V : in out Polyvec_L) -- RCC stronger postcondition
     with Always_Terminates,
          Global => null,
          Pre    => V in Valid_Signed_Polyvec_L,
          Post   => V in Valid_INTT_Polyvec_L;

   procedure Inv_NTTK (V : in out Polyvec_K) -- RCC stronger postcondition
     with Always_Terminates,
          Global => null,
          Pre    => V in Valid_Signed_Polyvec_K,
          Post   => V in Valid_INTT_Polyvec_K;

   procedure Uniform_Gamma1 (V     :    out Polyvec_L;
                             Seed  : in     Bytes_Crh;
                             Nonce : in     U16)
     with Always_Terminates, Global => null,
          Pre    => Nonce <= Nonce_UB,
          Post   => V in Valid_Gamma1_Polyvec_L;

   procedure Poly_Uniform_Eta_4x (R0, R1, R2, R3                 :    out Valid_Eta_Poly;
                                  Seed                           : in     Bytes_Crh;
                                  Nonce0, Nonce1, Nonce2, Nonce3 : in     U8)
     with Always_Terminates, Global => null;

   subtype Reduce32_Domain_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Reduce32_Domain_Polyvec_K.Vec (I) in Reduce32_Domain_Poly);

   subtype Reduce32_Range_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Reduce32_Range_Polyvec_K.Vec (I) in Reduce32_Range_Poly);

   procedure Matrix_Pointwise_Montgomery
      (T   :    out Valid_Signed_Polyvec_K; -- RCC Updated
       Mat : in     Polyvec_Matrix;
       V   : in     Valid_NTT_Polyvec_L)
     with Always_Terminates, Global => null;


   procedure Reduce (V : in out Polyvec_K)
     with Always_Terminates, Global => null,
          Pre    => V in Reduce32_Domain_Polyvec_K,
          Post   => V in Reduce32_Range_Polyvec_K;

   subtype Reduce32_Domain_Polyvec_L is Polyvec_L
     with Dynamic_Predicate => (for all I in L_Index =>
          Reduce32_Domain_Polyvec_L.Vec (I) in Reduce32_Domain_Poly);

   subtype Reduce32_Range_Polyvec_L is Polyvec_L
     with Dynamic_Predicate => (for all I in L_Index =>
          Reduce32_Range_Polyvec_L.Vec (I) in Reduce32_Range_Poly);

   procedure Reduce (V : in out Polyvec_L)
     with Always_Terminates, Global => null,
          Pre    => V in Reduce32_Domain_Polyvec_L,
          Post   => V in Reduce32_Range_Polyvec_L; -- RCC ???

   procedure CAddQ (V : in out Polyvec_K)
     with Always_Terminates, Global => null,
          Pre => V in Valid_Signed_Polyvec_K,
          Post => V in Valid_Natural_Polyvec_K;


   procedure Decompose (V1 : out Polyvec_K;
                        V0 : out Polyvec_K;
                        V  : in Polyvec_K)
     with Always_Terminates, Global => null,
          Pre => V in Valid_Natural_Polyvec_K,
          Post => V0 in Valid_Decomposed_V0_Polyvec_K and
                  V1 in Valid_Decomposed_V1_Polyvec_K;

   subtype Packed_W1_Polyvec_K is Polyvec_K
     with Dynamic_Predicate => (for all I in K_Index =>
          Packed_W1_Polyvec_K.Vec (I) in Packed_W1_Poly);

   procedure Pack_W1 (R : out Bytes_Packed_W1;
                      W1 : in Packed_W1_Polyvec_K)
     with Always_Terminates, Global => null;


   subtype Challenge_Poly is Poly
     with Dynamic_Predicate => (for all I in N_Index =>
                                  Challenge_Poly.Coeffs (I) in Challenge_Coeff);

   procedure Challenge (C    :    out Challenge_Poly;
                        Seed : in     Bytes_CTilde)
     with Always_Terminates, Global => null;


   procedure Pointwise_Poly_Montgomery (R : out Valid_Signed_Polyvec_L; -- RCC stronger
                                        A : in Poly;
                                        V : in Polyvec_L)
     with Always_Terminates, Global => null;

   procedure Pointwise_Poly_Montgomery (R : out Valid_Signed_Polyvec_K; -- RCC stronger
                                        A : in Poly;
                                        V : in Polyvec_K)
     with Always_Terminates, Global => null;

   procedure Add (U : in out Polyvec_L;
                  V : in     Polyvec_L)
     with Always_Terminates, Global => null,
          Pre => (U in Valid_INTT_Polyvec_L and
                  V in Valid_Gamma1_Polyvec_L) and then -- RCC subtypes first AND THEN check overflow
                 (for all K0 in L_Index =>
                   (for all K1 in N_Index =>
                     (U.Vec (K0).Coeffs (K1) + V.Vec (K0).Coeffs (K1)) in Reduce32_Domain)),
          Post => U in Reduce32_Domain_Polyvec_L;

   procedure Add (U : in out Polyvec_K;
                  V : in     Polyvec_K)
     with Always_Terminates, Global => null,
          Pre => (U in Valid_INTT_Polyvec_K and V in Valid_Gamma2_Polyvec_K) and then
                 ((for all K0 in K_Index =>
                    (for all K1 in N_Index =>
                      I64 (U.Vec (K0).Coeffs (K1)) +
                      I64 (V.Vec (K0).Coeffs (K1)) <= I64 (I32'Last))) and
                  (for all K0 in K_Index =>
                    (for all K1 in N_Index =>
                      I64 (U.Vec (K0).Coeffs (K1)) +
                      I64 (V.Vec (K0).Coeffs (K1)) >= I64 (I32'First)))),
          Post => U in Valid_Signed_Polyvec_K;

   procedure Sub (U : in out Polyvec_K;
                  V : in     Polyvec_K)
     with Always_Terminates, Global => null,
          Pre => (U in Valid_Signed_Polyvec_K and
                  V in Valid_Signed_Polyvec_K) and then
                 (for all K0 in L_Index =>
                   (for all K1 in N_Index =>
                     (U.Vec (K0).Coeffs (K1) - V.Vec (K0).Coeffs (K1)) in Reduce32_Domain)),
          Post => U in Reduce32_Domain_Polyvec_K;

   --  True means V is OK
   function Chknorm (V : in Polyvec_L;
                     B : in I32) return Boolean
     with Global => null,
          Pre    => B >= 0 and
                    B <= (Q - 1) / 8 and
                    V in Reduce32_Range_Polyvec_L,
          Post   => (Chknorm'Result = (for all I in L_Index => -- RCC Stronger
                      (for all K in N_Index => (V.Vec (I).Coeffs (K) > -B and V.Vec (I).Coeffs (K) < B))));

   --  True means V is OK
   function Chknorm (V : in Polyvec_K;
                     B : in I32) return Boolean
     with Global => null,
          Pre    => B >= 0 and
                    B <= (Q - 1) / 8 and
                    V in Reduce32_Range_Polyvec_K,
          Post   => (Chknorm'Result = (for all I in K_Index =>
                      (for all K in N_Index => (V.Vec (I).Coeffs (K) > -B and V.Vec (I).Coeffs (K) < B))));


   procedure Make_Hint (H : out Valid_Hint_Polyvec_K; -- RCC stronger
                        R : out U32;
                        V0 : in Polyvec_K;
                        V1 : in Polyvec_K)
     with Always_Terminates, Global => null,
          Post   => R <= N * K;


   procedure Use_Hint (W :    out Valid_Decomposed_V1_Polyvec_K;
                       V : in     Valid_Natural_Polyvec_K;
                       H : in     Valid_Hint_Polyvec_K)
     with Always_Terminates, Global => null;

   procedure Pack_Sig (Sig : out Bytes_Crypto;
                       C   : in Bytes_Ctilde;
                       Z   : in Valid_Gamma1_Polyvec_L;
                       H   : in Valid_Hint_Polyvec_K;
                       Number_Of_Hints : in U32)
     with Always_Terminates, Global => null,
          Pre    => Number_Of_Hints <= OMEGA;


   procedure ShiftL (V : in out Polyvec_K)
     with Always_Terminates,
          Global => null,
          Pre    => V in Valid_PK_Polyvec_K, -- all in 0 .. 1023 - RCC Stronger
          Post   => V in Valid_Natural_Polyvec_K; -- all in 0 .. Q-1


   -- Polyvec_K_Power2Round
   procedure Power2Round (V1 :    out Polyvec_K; -- unsigned in 0 .. 1023
                          V0 :    out Polyvec_K; -- signed in -4095 .. 4096
                          V  : in     Valid_Natural_Polyvec_K)
     with Always_Terminates,
          Global => null,
          Post   => V0 in Valid_SK_Polyvec_K and
                    V1 in Valid_PK_Polyvec_K;
end MLDSA;

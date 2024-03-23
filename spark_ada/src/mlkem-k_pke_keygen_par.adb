-----------------------------------------------------------
--  This is a parallel implementation.
--
--  Local tasks are use to parallelize the computation
--  of A_Hat, S_Hat, and E_Hat
-----------------------------------------------------------

separate (MLKEM)
--  Algorithm 12, FIPS 203 5.1
function K_PKE_KeyGen (Random_D : in Bytes_32) return PKE_Key
is
   D_Hash : Bytes_64;
   Rho    : Bytes_32;
   Sigma  : Bytes_32;

   A_Hat  : NTT_Poly_Matrix;
   S      : Poly_Zq_Vector;
   E      : Poly_Zq_Vector;
   S_Hat  : NTT_Poly_Zq_Vector;
   E_Hat  : NTT_Poly_Zq_Vector;
   T_Hat  : NTT_Poly_Zq_Vector;
   EK     : PKE_Encryption_Key;
   DK     : PKE_Decryption_Key;

   task type Compute_A_Hat;
   task type Compute_S_Hat;
   task type Compute_E_Hat;

   task body Compute_A_Hat
   is
   begin
      Rho     := D_Hash (0 .. 31);
      Generate_A_Hat_Matrix (Rho, A_Hat);
   end Compute_A_Hat;

   task body Compute_S_Hat
   is
   begin
      Generate_Poly_Zq_Vector_With_Eta_1 (Sigma, 0, S);
      S_Hat := NTT (S);
   end Compute_S_Hat;

   task body Compute_E_Hat
   is
   begin
      Generate_Poly_Zq_Vector_With_Eta_1 (Sigma, K, E);
      E_Hat := NTT (E);
   end Compute_E_Hat;

begin

   D_Hash := G (Random_D);
   Sigma  := D_Hash (32 .. 63);

   declare
      T1 : Compute_A_Hat;
      T2 : Compute_S_Hat;
      T3 : Compute_E_Hat;
   begin
      null;
      --  Original task waits here until the three sub-tasks above
      --  are all terminated.
   end;

   T_Hat := A_Hat * S_Hat + E_Hat;

   EK := ByteEncode12 (T_Hat) & Rho; --  calls _memcpy()
   DK := ByteEncode12 (S_Hat);

   return PKE_Key'(EK, DK); --  calls _memcpy() (twice)
end K_PKE_KeyGen;

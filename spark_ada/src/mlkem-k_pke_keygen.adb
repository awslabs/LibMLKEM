-----------------------------------------------------------
--  This is sequential and reference implementation,
--  designed to match the text of FIPS 203 as closely
--  as possible.
--
--  This is separate subunit of MLKEM, so that alternative
--  (possibly parallel) implementations may be supplied
--  and selected by the build system.
-----------------------------------------------------------

separate (MLKEM)
--  Algorithm 13, FIPS 203 5.1
function K_PKE_KeyGen (Random_D : in Bytes_32) return PKE_Key
is
   D_Hash : constant Bytes_64 := G (Random_D & K);
   Rho    : constant Bytes_32 := D_Hash (0 .. 31);
   Sigma  : constant Bytes_32 := D_Hash (32 .. 63);

   A_Hat  : NTT_Poly_Matrix;
   S      : Poly_Zq_Vector;
   E      : Poly_Zq_Vector;
   S_Hat  : NTT_Poly_Zq_Vector;
   E_Hat  : NTT_Poly_Zq_Vector;
   T_Hat  : NTT_Poly_Zq_Vector;
   EK     : PKE_Encryption_Key;
   DK     : PKE_Decryption_Key;
begin
   Generate_A_Hat_Matrix (Rho, A_Hat);
   Generate_Poly_Zq_Vector_With_Eta_1 (Sigma, 0, S);
   Generate_Poly_Zq_Vector_With_Eta_1 (Sigma, K, E);

   S_Hat := NTT (S);
   E_Hat := NTT (E);

   T_Hat := A_Hat * S_Hat + E_Hat;

   EK := ByteEncode12 (T_Hat) & Rho; --  calls _memcpy()
   DK := ByteEncode12 (S_Hat);

   return PKE_Key'(EK, DK); --  calls _memcpy() (twice)
end K_PKE_KeyGen;

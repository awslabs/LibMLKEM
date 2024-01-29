package MLKEM.Tests
  with SPARK_Mode => Off
is
   --  Exhaustive test of the "*" and ModQ functions for Zq.T
   procedure MulTest;

   --  Generates lookup table for Zeta_Exp (BitRev7 (K))
   --  for all K in 0 .. 127
   --  Prints constant table aggreate to stdout
   procedure Gen_Zeta_Exp_Table;

   --  Generates lookup table for Gamma =
   --    Zeta_Exp (2 * BitRev7 (SU7 (I)) + 1)
   --  for I in 0 .. 127
   procedure Gen_Gamma_Table;

end MLKEM.Tests;

--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

with Ada.Text_IO; use Ada.Text_IO;

with Interfaces; use Interfaces;

with MLKEM;       use MLKEM;

with Ada.Numerics.Discrete_Random;

procedure TValidation
is
   package RB is new Ada.Numerics.Discrete_Random (Byte);
   use RB;

   RBG : Generator;

   procedure RInit (X : out Bytes_32);

   procedure RInit (X : out Bytes_32)
   is
   begin
      for I in X'Range loop
         X (I) := Random (RBG);
      end loop;
   end RInit;

   D, D2, Z, M : Bytes_32;
   K1 : MLKEM_Key;
   K2 : MLKEM_Key;
begin
   Reset (RBG);
   RInit (D);
   RInit (Z);
   RInit (M);

   K1 := MLKEM_KeyGen (D, Z);
   K2 := K1;

   if Key_Pair_Check_With_Seed (K2, D, Z, M) then
      Put_Line ("Good key check       - PASS");
   else
      Put_Line ("Good key check       - FAIL");
   end if;

   --  Corrupt K2.EK and try again
   K2.EK (1) := K2.EK (1) + 1;
   if Key_Pair_Check_With_Seed (K2, D, Z, M) then
      Put_Line ("Corrupt EK check     - FAIL");
   else
      Put_Line ("Corrupt EK check     - PASS");
   end if;

   --  Corrupt K2.EK and try again
   K2 := K1;
   K2.DK (1) := K2.DK (1) + 1;
   if Key_Pair_Check_With_Seed (K2, D, Z, M) then
      Put_Line ("Corrupt DK check     - FAIL");
   else
      Put_Line ("Corrupt DK check     - PASS");
   end if;

   --  Corrupt the seed and try again
   K2 := K1;
   D2 := D;
   D2 (1) := D2 (1) + 1;
   if Key_Pair_Check_With_Seed (K2, D2, Z, M) then
      Put_Line ("Corrupt D Seed check - FAIL");
   else
      Put_Line ("Corrupt D Seed check - PASS");
   end if;

   --  Verify valid EK
   K2 := K1;
   if EK_Valid_For_Encaps (K2.EK) then
      Put_Line ("Valid EK check       - PASS");
   else
      Put_Line ("Valid EK check       - FAIL");
   end if;

   --  Corrupt EK - to defeat ByteDecode12 test on EK, we have
   --  to REALLY corrupt it...
   K2.EK := (others => 255);
   if EK_Valid_For_Encaps (K2.EK) then
      Put_Line ("Corrupt EK check     - FAIL");
   else
      Put_Line ("Corrupt EK check     - PASS");
   end if;

   --  Verify valid DK
   K2 := K1;
   if DK_Valid_For_Decaps (K2.DK) then
      Put_Line ("Valid DK check       - PASS");
   else
      Put_Line ("Valid DK check       - FAIL");
   end if;

   --  Corrupt DK
   K2 := K1;
   K2.DK (384 * K) := not K2.DK (384 * K);
   if DK_Valid_For_Decaps (K2.DK) then
      Put_Line ("Corrupt DK check     - FAIL");
   else
      Put_Line ("Corrupt DK check     - PASS");
   end if;

end TValidation;

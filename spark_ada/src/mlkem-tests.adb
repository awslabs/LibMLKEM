with Ada.Text_IO; use Ada.Text_IO;

package body MLKEM.Tests
  with SPARK_Mode => Off
is
   use Zq;

   procedure MulTest
   is
      R1 : Zq.T;
      R2 : U32;
      R3 : U16;
   begin
      --  Exhaustive test of "*" for Zq.T
      for I in Zq.T loop
         for J in Zq.T loop
            R1 := I * J;
            R2 := (U32 (I) * U32 (J)) mod 3329;
            if U32 (R1) /= R2 then
               Put (I'Img & " *" & J'Img & " =" & R1'Img);
               Put_Line (" /=" & R2'Img & ", Fail");
               raise Program_Error;
            end if;
         end loop;
      end loop;

      --  Exhaustive test of ModQ for all U16
      for K in U16_12Bits loop
         R1 := ModQ (K);
         R3 := K mod Q;
         Put (K'Img & " mod Q =");
         if U16 (R1) = R3 then
            Put_Line (R1'Img & ", Pass");
         else
            Put_Line (R1'Img & " /=" & R3'Img & ", Fail");
            raise Program_Error;
         end if;
      end loop;

   end MulTest;

   function BitRev7 (X : SU7) return SU7
   is
      C : Byte := X;
      R : Byte := 0;
   begin
      --  This a simple-minded, but readable implementation
      --  a 7-bit reverse. Faster, but less readable alternative
      --  is in Hacker's Delight section 7.1, or a simple
      --  look-up table could be pre-computed.
      for I in 1 .. 7 loop
         R := R * 2;
         R := R or (C and 1);
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Invariant (R <= 2**I - 1);
         C := C / 2;
      end loop;

      pragma Assert (R >= 0);
      pragma Assert (R <= 2**7 - 1);

      return SU7 (R);
   end BitRev7;

   function Zeta_Exp (K : in Byte) return Zq.T
   is
      type Local_Zq is mod Q;
      Zeta_C : constant Local_Zq := 17;
   begin
      --  This call to "**" will generate a call to the Ada
      --  runtime library, which might not be a constant-time
      --  implementation.
      return Zq.T (Zeta_C ** Natural (K)); -- Implicitly mod Q
   end Zeta_Exp;

   procedure Gen_Zeta_Exp_Table
   is
   begin
      Put_Line ("   Zeta_Exp : constant Zeta_Exp_Table_Type := ");
      for K in SU7 loop
         declare
            KI : constant String := K'Img;
            R  : constant Zq.T   := Zeta_Exp (BitRev7 (K));
         begin
            Put ("     ");
            Put ((if K = SU7'First then "(" else " "));
            Put (KI (2 .. KI'Last) & " =>" & R'Img);
            if K = SU7'Last then
               Put_Line (");");
            else
               Put_Line (",");
            end if;
         end;
      end loop;
   end Gen_Zeta_Exp_Table;

   procedure Gen_Gamma_Table
   is
   begin
      Put_Line ("   Gamma_Table : constant Gamma_Table_Type := ");
      for I in Index_128 loop
         declare
            II : constant String := I'Img;
            R  : constant Zq.T   := Zeta_Exp (2 * BitRev7 (SU7 (I)) + 1);
         begin
            Put ("     ");
            Put ((if I = Index_128'First then "(" else " "));
            Put (II (2 .. II'Last) & " =>" & R'Img);
            if I = Index_128'Last then
               Put_Line (");");
            else
               Put_Line (",");
            end if;
         end;
      end loop;
   end Gen_Gamma_Table;

end MLKEM.Tests;

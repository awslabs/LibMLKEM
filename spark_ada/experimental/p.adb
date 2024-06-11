package body P
  with SPARK_Mode => On
is
   function Div1 (X : in Zq_Product) return U32
     with SPARK_Mode => Off
   is
   begin
      --  Allow the compiler to implement as it sees fit.
      --  At -O0 through -O3, the compiler should use the Montgomery division trick
      --  to turn this into a mukltiply/shift sequence.
      --  At -Os, it generates a single "divide" instruction.
      return X / Q;
   end Div1;

   C : constant := 2**37;
   M : constant := (C / Q) + 1;

   function Div2 (X : in Zq_Product) return U32
     with SPARK_Mode => Off
   is
      T : U64;
   begin
      --  Explicit Montgomery-style division, using the magic numbers defined
      --  above. Note that with X restricted to Zq_Product, the error bound
      --  is sufficiently small that this can be done with a _single_ multiplication
      --  and a _single_ shift, so faster than the compiler manages in the general case above.
      T := (U64 (X) * M) / C;
      return U32 (T);
   end Div2;

   function Negate (X : in Zq) return Zq
     with SPARK_Mode => Off
   is
      R : U32;
   begin
      --  This generates 4 instructions (5 including the "ret")
      --  with -O3 -gnatp
      R := Q - U32 (X);
      R := R * (Boolean'Pos (R /= Q));
      return Zq (R);

      --  This generates 6 instructions including the "ret" with same switches.
      --  return -X;
   end Negate;

   function Equal (X, Y : in Byte_Seq) return Boolean
   is
      Arrays_Match : Boolean := True;
      I : N32 := X'First;
   begin
      loop
         Arrays_Match := Arrays_Match and (X (I) = Y (I));
         pragma Loop_Invariant
           (I >= X'First and I <= X'Last and
            (Arrays_Match = (for all J in N32 range X'First .. I => X (J) = Y (J))));
         exit when I = X'Last;
         I := I + 1;
      end loop;
      return Arrays_Match;
   end Equal;

   --  Needs --level=1 or above to prove with CVC5
   procedure Conditional_Copy (Dest      : in out Byte_Seq;
                               Src       : in     Byte_Seq;
                               Dont_Copy : in     Boolean)
   is
      Mask : constant U8 := 16#FF# * Boolean'Pos (not Dont_Copy);
   begin
      for I in Dest'Range loop
         Dest (I) := Dest (I) xor ((Dest (I) xor Src (I)) and Mask);

                  pragma Loop_Invariant (for all J in N32 range Dest'First .. I =>
                                  Dest (J) = (if Dont_Copy then Dest'Loop_Entry (J) else Src (J)));
      end loop;
   end Conditional_Copy;

   procedure Conditional_Unpad (Dest : in out Byte_Seq;
                                Src  : in     Byte_Seq)
   is
      subtype Src_Slice is Byte_Seq (Dest'Range);

      First_Padding_Byte_Index : constant N32 := 2;
      First_Data_Byte_Index    : constant N32 := Src'Last - Dest'Last;
      Zero_Byte_Index          : constant N32 := First_Data_Byte_Index - 1;
      Last_Padding_Byte_Index  : constant N32 := Zero_Byte_Index - 1;
      Dont_Copy                : U8;
   begin
      Dont_Copy := Src (0) or (Src (1) xor 16#02#);
      Dont_Copy := Dont_Copy or Src (Zero_Byte_Index);

      for I in N32 range First_Padding_Byte_Index .. Last_Padding_Byte_Index loop
         pragma Loop_Optimize (No_Unroll, No_Vector);
         Dont_Copy := Dont_Copy or Src (I);
      end loop;

      Conditional_Copy (Dest,
                        Src_Slice (Src (First_Data_Byte_Index .. Src'Last)),
                        Dont_Copy > 0);
   end Conditional_Unpad;

end P;

with Interfaces; use Interfaces;
package P
  with SPARK_Mode => On
is
   Q : constant := 3329;

   type Zq is mod Q;

   subtype U64 is Unsigned_64;
   subtype U32 is Unsigned_32;
   subtype N32 is Integer_32 range 0 .. Integer_32'Last;
   subtype U16 is Unsigned_16;
   subtype U8 is Unsigned_8;

   subtype Zq_Product is U32 range 0 .. (Q - 1)**2;

   type Byte_Seq is array (N32 range <>) of U8;

   function Div1 (X : in Zq_Product) return U32;

   function Div2 (X : in Zq_Product) return U32;

   function Negate (X : in Zq) return Zq
     with Post => (Negate'Result = -X);

   function Equal (X, Y : in Byte_Seq) return Boolean
     with Global => null,
          Pre    => X'First = Y'First and
                    X'Last  = Y'Last and
                    X'Length >= 1 and
                    Y'Length >= 1 and
                    X'Length = Y'Length,
          Post   => Equal'Result =
                      (for all I in X'Range => X (I) = Y (I));

   procedure Conditional_Copy (Dest      : in out Byte_Seq;
                               Src       : in     Byte_Seq;
                               Dont_Copy : in     Boolean)
     with No_Inline,
          Global => null,
          Pre => Dest'First = Src'First and then
                 Dest'Last  = Src'Last and then
                 Dest'Length = Src'Length,
          Post => (if Dont_Copy then Dest = Dest'Old else Dest = Src);

   -- test cases Dest (0 .. 0), Src (0 .. 3)
   procedure Conditional_Unpad (Dest : in out Byte_Seq;
                                Src  : in     Byte_Seq)
     with No_Inline,
          Global => null,
          Pre => Dest'First = 0 and then
                 Src'First  = 0 and then
                 Src'Last   >= 0 and then
                 Dest'Last  >= 0 and then
                 Src'Last   > Dest'Last and then
                 Src'Length >= Dest'Length + 3 and then
                 Src'Last - Dest'Last >= 3;

end P;

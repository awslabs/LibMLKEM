package body P
is
   function Div1 (X : in Zq_Product) return U32
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

end P;

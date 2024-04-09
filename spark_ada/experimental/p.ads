with Interfaces; use Interfaces;
package P
is
   Q : constant := 3329;

   type Zq is mod Q;

   subtype U64 is Unsigned_64;
   subtype U32 is Unsigned_32;
   subtype U16 is Unsigned_16;

   subtype Zq_Product is U32 range 0 .. (Q - 1)**2;

   function Div1 (X : in Zq_Product) return U32;

   function Div2 (X : in Zq_Product) return U32;

end P;

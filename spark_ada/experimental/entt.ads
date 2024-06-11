with Interfaces; use Interfaces;
package ENTT
  with SPARK_Mode => On
is
   -- =================================
   -- Experimental NTT implementations
   -- =================================

   Q    : constant := 3329;
   QINV : constant := -3327;

   subtype Byte is Unsigned_8;
   subtype I32  is Integer_32;
   subtype N32  is I32 range 0 .. I32'Last;

   type Zq is mod Q;

   --  Unconstrained (aka "Size Polymorphic") array of bytes
   type Byte_Seq is array (N32 range <>) of Byte;

   subtype Index_256 is I32 range 0 .. 255;

   type UPoly is array (Index_256 range <>) of Zq;
   subtype Poly_Zq is UPoly (Index_256);

   --  Standard CT-based NTT implemented as per FIPS 203
   function NTT (F : in Poly_Zq) return Poly_Zq
     with Global => null,
          No_Inline;

   --  As per standard, but outer loop unrolled
   function NTTu (F : in Poly_Zq) return Poly_Zq
     with Global => null,
          No_Inline;

   --  Sequential, recursive, functional interface
   function NTTsr (F : in Poly_Zq) return Poly_Zq
     with Global => null,
          No_Inline;

   --  Sequential, recursive, in-place procedural interface.
   procedure NTTir (F : in out Poly_Zq)
     with Global => null,
          No_Inline;

   --  Tree-parallel/tasking, in-place
   procedure NTTtir (F : in out Poly_Zq)
     with Global => null,
          No_Inline;

end ENTT;

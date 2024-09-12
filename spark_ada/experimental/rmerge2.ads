with Interfaces; use Interfaces;
package RMerge2
  with SPARK_Mode => On
is
   pragma Linker_Options ("ntt.o");

   Q      : constant := 3329;
   QM1    : constant := Q - 1; --  Q Minus 1
   QINV   : constant := -3327;
   Half_Q : constant := 1664;

   subtype Byte is Unsigned_8;
   subtype I16  is Integer_16;
   subtype I32  is Integer_32;
   subtype N32  is I32 range 0 .. I32'Last;

   type Zq is mod Q;

   --  Unconstrained (aka "Size Polymorphic") array of bytes
   type Byte_Seq is array (N32 range <>) of Byte;

   subtype Index_256 is I32 range 0 .. 255;

   type UPoly is array (Index_256 range <>) of I16;
   subtype Poly_Zq is UPoly (Index_256);

   subtype BRange is Integer_16 range -Half_Q .. Half_Q;


   --  Standard CT-based NTT implemented as per FIPS 203
   procedure NTT (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in BRange),
          Post => (for all K in Index_256 => F (K) in BRange);

   --  Standard CT-based NTT implemented as per FIPS 203, C version
   procedure CNTT (F : in out Poly_Zq)
     with Global => null,
          Import,
          Convention => C,
          External_Name => "poly_ntt",
          No_Inline;

end RMerge2;

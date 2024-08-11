with Interfaces; use Interfaces;
package ENTTRef
  with SPARK_Mode => On
is
   pragma Linker_Options ("ntt.o");

   Q    : constant := 3329;
   QM1  : constant := Q - 1; --  Q Minus 1
   QINV : constant := -3327;

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

   Zeta_Min : constant := -1659;
   Zeta_Max : constant :=  1653;
   subtype Zeta_Range is I16 range Zeta_Min .. Zeta_Max;



   ------------------------
   --  Montgomery reduction
   ------------------------
   subtype Mont_Domain is I32 range -Q * 32768 .. Q * 32768 - 1;
   subtype Mont_Range is I16 range -QM1 .. QM1;
   function Montgomery_Reduce (X : in Mont_Domain) return Mont_Range
     with Global => null,
          Inline_Always;

   subtype Mont_Range2 is I16 range -2 * QM1 .. 2 * QM1;
   subtype Mont_Range3 is I16 range -3 * QM1 .. 3 * QM1;
   subtype Mont_Range4 is I16 range -4 * QM1 .. 4 * QM1;
   subtype Mont_Range5 is I16 range -5 * QM1 .. 5 * QM1;
   subtype Mont_Range6 is I16 range -6 * QM1 .. 6 * QM1;
   subtype Mont_Range7 is I16 range -7 * QM1 .. 7 * QM1;
   subtype Mont_Range8 is I16 range -8 * QM1 .. 8 * QM1;



   function FQMul (Z : in Zeta_Range; --  First parameter is always Zeta
                   B : in I16) return Mont_Range
     with Global => null,
          Inline_Always;

   function RCount return Natural;

   --  Standard CT-based NTT implemented as per FIPS 203
   procedure NTT (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range);

   --  Standard CT-based NTT implemented as per FIPS 203, Unrolled outer loop
   procedure NTTu (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range);

   --  Standard CT-based NTT implemented as per FIPS 203, C versio
   procedure CNTT (F : in out Poly_Zq)
     with Global => null,
          Import,
          Convention => C,
          External_Name => "pqcrystals_kyber768_ref_ntt",
          No_Inline;

end ENTTRef;

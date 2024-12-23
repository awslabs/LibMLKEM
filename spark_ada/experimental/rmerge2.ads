with Interfaces; use Interfaces;
package RMerge2
  with SPARK_Mode => On
is
   pragma Linker_Options ("ntt.o");

   Q      : constant := 3329;
   QM1    : constant := Q - 1; --  Q Minus 1
   Half_Q : constant := 1664;

   subtype Byte is Unsigned_8;
   subtype U16  is Unsigned_16;
   subtype I16  is Integer_16;
   subtype I32  is Integer_32;
   subtype N32  is I32 range 0 .. I32'Last;

   type Zq is mod Q;

   --  Unconstrained (aka "Size Polymorphic") array of bytes
   type Byte_Seq is array (N32 range <>) of Byte;

   subtype Index_256 is I32 range 0 .. 255;

   type UPoly is array (Index_256 range <>) of I16;
   subtype Poly_Zq is UPoly (Index_256);

   subtype Mont_Range is I16 range -QM1 .. QM1;
   subtype Mont_Range2 is I16 range -2 * QM1 .. 2 * QM1;
   subtype Mont_Range3 is I16 range -3 * QM1 .. 3 * QM1;
   subtype Mont_Range4 is I16 range -4 * QM1 .. 4 * QM1;
   subtype Mont_Range5 is I16 range -5 * QM1 .. 5 * QM1;
   subtype Mont_Range6 is I16 range -6 * QM1 .. 6 * QM1;
   subtype Mont_Range7 is I16 range -7 * QM1 .. 7 * QM1;
   subtype Mont_Range8 is I16 range -8 * QM1 .. 8 * QM1;

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

private

   Zeta_Min : constant := -1659;
   Zeta_Max : constant :=  1653;
   subtype Zeta_Range is I16 range Zeta_Min .. Zeta_Max;

   subtype SU7 is I32 range 0 .. 127;

   type Zeta_Exp_Table_Type is array (SU7) of Zeta_Range;

   Zeta_ExpC : constant Zeta_Exp_Table_Type :=
     (-1044, -- NOT USED

      --  Layer 1
      -758,

      --  Layer 2
      -359, -1517,

      --  Layer 3
      1493,  1422,   287, 202,

      --  Layer 4
      -171,   622,  1577,   182,   962, -1202, -1474,  1468,

      --  Layer 5
       573, -1325,   264,   383,  -829,  1458, -1602,  -130,
      -681,  1017,   732,   608, -1542,   411,  -205, -1571,

      --  Layer 6
      1223,   652,  -552,  1015, -1293,  1491,  -282, -1544,
       516,    -8,  -320,  -666, -1618, -1162,   126,  1469,
      -853,   -90,  -271,   830,   107, -1421,  -247,  -951,
      -398,   961, -1508,  -725,   448, -1065,   677, -1275,

      --  Layer 7
     -1103,   430,   555,   843, -1251,   871,  1550,   105,
       422,   587,   177,  -235,  -291,  -460,  1574,  1653,
      -246,   778,  1159,  -147,  -777,  1483,  -602,  1119,
     -1590,   644,  -872,   349,   418,   329,  -156,   -75,
       817,  1097,   603,   610,  1322, -1285, -1465,   384,
     -1215,  -136,  1218, -1335,  -874,   220, -1187, -1659,
     -1185, -1530, -1278,   794, -1510,  -854,  -870,   478,
      -108,  -308,   996,   991,   958, -1460,  1522,  1628);


   function Barrett_Reduce (A : in Integer_16) return BRange
     with Global => null,
          Inline_Always;

   function FQMul (Z : in Zeta_Range; --  First parameter is always Zeta
                   B : in I16) return Mont_Range
     with Global => null,
          Inline_Always;

end RMerge2;

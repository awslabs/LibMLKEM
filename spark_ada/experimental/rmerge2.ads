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


   ----------------------------------------
   --  Zeta constants for layers 1, 2 and 3
   ----------------------------------------

   L1Zeta1 : constant Zeta_Range := -758;
   L2Zeta2 : constant Zeta_Range := -359;
   L2Zeta3 : constant Zeta_Range := -1517;
   L3Zeta4 : constant Zeta_Range := 1493;
   L3Zeta5 : constant Zeta_Range := 1422;
   L3Zeta6 : constant Zeta_Range := 287;
   L3Zeta7 : constant Zeta_Range := 202;

   ----------------------------------
   --  Zeta tables for merged layer54
   ----------------------------------
   subtype L4_Zeta_Index is I32 range 0 .. 7;

   type L54_Zeta_Table_Type is array (L4_Zeta_Index) of Zeta_Range;
   --  Zeta values for layer 4, originally occupying
   --  positions 8 .. 15 in the full Zeta table.
   L4_Zetas_Table : constant L54_Zeta_Table_Type :=
     (-171, 622, 1577, 182, 962, -1202, -1474, 1468);

   --  Zeta values for layer 5, originally occupying "even"
   --  positions 16,18,20,22,24,26,28,30 in the full Zeta table.
   L5_Even_Zetas_Table : constant L54_Zeta_Table_Type :=
     (573, 264, -829, -1602, -681, 732, -1542, -205);

   --  Zeta values for layer 5, originally occupying "odd"
   --  positions 17,19,21,23,25,27,29,31 in the full Zeta table.
   L5_Odd_Zetas_Table : constant L54_Zeta_Table_Type :=
     (-1325, 383, 1458, -130, 1017, 608, 411, -1571);


   ----------------------------------
   --  Zeta table for layer 6
   ----------------------------------
   subtype L6_Zeta_Index is I32 range 0 .. 31;

   type L6_Zeta_Table_Type is array (L6_Zeta_Index) of Zeta_Range;
   L6_Zetas_Table : constant L6_Zeta_Table_Type :=
     (1223,   652,  -552,  1015, -1293,  1491,  -282, -1544,
       516,    -8,  -320,  -666, -1618, -1162,   126,  1469,
      -853,   -90,  -271,   830,   107, -1421,  -247,  -951,
      -398,   961, -1508,  -725,   448, -1065,   677, -1275);

--  As L6_Zetas_Table, but reverse order for inverse NTT.
--  Potentially saves a single "-" operator in Layer6, but
--  appears to be slower at -O3 with GCC 14.2.0 on AArch64
--
--   L6_Inverse_Zetas_Table : constant L6_Zeta_Table_Type :=
--     (-1275,   677, -1065,   448, -725, -1508, 961, -398,
--       -951,  -247, -1421,   107,  830,  -271, -90, -853,
--       1469,   126, -1162, -1618, -666,  -320,  -8,  516,
--      -1544,  -282,  1491, -1293, 1015,  -552, 652, 1223);

   ----------------------------------
   --  Zeta table for layer 6
   ----------------------------------
   subtype L7_Zeta_Index is I32 range 0 .. 63;

   type L7_Zeta_Table_Type is array (L7_Zeta_Index) of Zeta_Range;
   L7_Zetas_Table : constant L7_Zeta_Table_Type :=
     (-1103,   430,   555,   843, -1251,   871,  1550,   105,
        422,   587,   177,  -235,  -291,  -460,  1574,  1653,
       -246,   778,  1159,  -147,  -777,  1483,  -602,  1119,
      -1590,   644,  -872,   349,   418,   329,  -156,   -75,
        817,  1097,   603,   610,  1322, -1285, -1465,   384,
      -1215,  -136,  1218, -1335,  -874,   220, -1187, -1659,
      -1185, -1530, -1278,   794, -1510,  -854,  -870,   478,
       -108,  -308,   996,   991,   958, -1460,  1522,  1628);

   ----------------------------------------------------
   --  Functions common to both forward and inverse NTT
   ----------------------------------------------------

   function Barrett_Reduce (A : in Integer_16) return BRange
     with Global => null,
          Inline_Always;

   function FQMul (Z : in Zeta_Range; --  First parameter is always Zeta
                   B : in I16) return Mont_Range
     with Global => null,
          Inline_Always;

end RMerge2;

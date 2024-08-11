--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

--  with Ada.Text_IO; use Ada.Text_IO;
package body NTT32
  with SPARK_Mode => On
is
--   subtype NTT_Len_Bit_Index is Natural range 0 .. 6;

   --  A power of 2 between 1 and 64. Used in NTT and NTT_Inv
--   subtype Count_T is Index_256
--      with Dynamic_Predicate =>
--         (for some I in NTT_Len_Bit_Index => Count_T = 2**I);

   --  A power of 2 between 4 and 256
--   subtype NTT_Slice_Length is I32
--      with Dynamic_Predicate =>
--         (for some I in 2 .. 8 => NTT_Slice_Length = 2**I);

   subtype SU7 is Byte range 0 .. 127;
   type Zeta_Exp_Table_Type is array (SU7) of Zq;

   Zeta_ExpC : constant Zeta_Exp_Table_Type :=
     (0 => 1,
      1 => 1729,
      2 => 2580,
      3 => 3289,
      4 => 2642,
      5 => 630,
      6 => 1897,
      7 => 848,
      8 => 1062,
      9 => 1919,
      10 => 193,
      11 => 797,
      12 => 2786,
      13 => 3260,
      14 => 569,
      15 => 1746,
      16 => 296,
      17 => 2447,
      18 => 1339,
      19 => 1476,
      20 => 3046,
      21 => 56,
      22 => 2240,
      23 => 1333,
      24 => 1426,
      25 => 2094,
      26 => 535,
      27 => 2882,
      28 => 2393,
      29 => 2879,
      30 => 1974,
      31 => 821,
      32 => 289,
      33 => 331,
      34 => 3253,
      35 => 1756,
      36 => 1197,
      37 => 2304,
      38 => 2277,
      39 => 2055,
      40 => 650,
      41 => 1977,
      42 => 2513,
      43 => 632,
      44 => 2865,
      45 => 33,
      46 => 1320,
      47 => 1915,
      48 => 2319,
      49 => 1435,
      50 => 807,
      51 => 452,
      52 => 1438,
      53 => 2868,
      54 => 1534,
      55 => 2402,
      56 => 2647,
      57 => 2617,
      58 => 1481,
      59 => 648,
      60 => 2474,
      61 => 3110,
      62 => 1227,
      63 => 910,
      64 => 17,
      65 => 2761,
      66 => 583,
      67 => 2649,
      68 => 1637,
      69 => 723,
      70 => 2288,
      71 => 1100,
      72 => 1409,
      73 => 2662,
      74 => 3281,
      75 => 233,
      76 => 756,
      77 => 2156,
      78 => 3015,
      79 => 3050,
      80 => 1703,
      81 => 1651,
      82 => 2789,
      83 => 1789,
      84 => 1847,
      85 => 952,
      86 => 1461,
      87 => 2687,
      88 => 939,
      89 => 2308,
      90 => 2437,
      91 => 2388,
      92 => 733,
      93 => 2337,
      94 => 268,
      95 => 641,
      96 => 1584,
      97 => 2298,
      98 => 2037,
      99 => 3220,
      100 => 375,
      101 => 2549,
      102 => 2090,
      103 => 1645,
      104 => 1063,
      105 => 319,
      106 => 2773,
      107 => 757,
      108 => 2099,
      109 => 561,
      110 => 2466,
      111 => 2594,
      112 => 2804,
      113 => 1092,
      114 => 403,
      115 => 1026,
      116 => 1143,
      117 => 2150,
      118 => 2775,
      119 => 886,
      120 => 1722,
      121 => 1212,
      122 => 1874,
      123 => 1029,
      124 => 2110,
      125 => 2935,
      126 => 885,
      127 => 2154);

   procedure NTT_Inner (F_Hat : in out Poly_Zq;
                        Zeta  : in     Zq;
                        Start : in     Index_256;
                        Len   : in     Len_T)
   is
      procedure P1
        with No_Inline
      is
         T : N32;
      begin
         for J in Index_256 range Start .. Start + (Len - 1) loop
            T               := (Zeta * F_Hat (J + Len));
            F_Hat (J + Len) := (F_Hat (J) - T);
            F_Hat (J)       := (F_Hat (J) + T);
         end loop;
      end P1;

      procedure P2
        with No_Inline
      is
      begin
         for J in Index_256 range Start .. Start + (Len - 1) loop
            F_Hat (J + Len) := F_Hat (J + Len) mod Q;
            F_Hat (J)       := F_Hat (J) mod Q;
         end loop;
      end P2;
   begin
      P1;
      P2;
   end NTT_Inner;

   procedure NTT_Inner128 (F_Hat : in out Poly_Zq;
                           Zeta  : in     Zq)
     with No_Inline
   is
      procedure P1
        with No_Inline
      is
         subtype TP is UPoly_I32 (0 .. 127);
         T     : Zq;
         T_Pos : TP;
         T_Neg : TP;
      begin
         for J in Index_256 range 0 .. 127 loop
            T := (Zeta * F_Hat (J + 128)) mod Q;
            T_Pos (J) := T;
            T_Neg (J) := Q - T;
         end loop;

         for J in Index_256 range 0 .. 127 loop
            F_Hat (J + 128) := (F_Hat (J) + T_Neg (J));
            F_Hat (J)       := (F_Hat (J) + T_Pos (J));
         end loop;
      end P1;

      procedure P2
        with No_Inline
      is
      begin
         for J in Index_256 loop
            pragma Loop_Optimize (Vector, Ivdep);
            F_Hat (J) := F_Hat (J) - (Q * Boolean'Pos(F_Hat (J) > Q_Minus_1));
         end loop;
      end P2;
   begin
      P1;
      P2;
   end NTT_Inner128;

   function NTT (F : in Poly_Zq) return Poly_Zq
   is
      F_Hat : Poly_Zq;
   begin
      F_Hat := F;

      -- I = 0 -----------------
      NTT_Inner128 (F_Hat => F_Hat,
                    Zeta  => Zeta_ExpC (1));

      -- I = 1 -----------------
      NTT_Inner (F_Hat => F_Hat,
                 Zeta  => Zeta_ExpC (2),
                 Start => 0,
                 Len   => 64);

      NTT_Inner (F_Hat => F_Hat,
                 Zeta  => Zeta_ExpC (3),
                 Start => 128,
                 Len   => 64);

      -- I = 2 -----------------
      for J in I32 range 0 .. 3 loop
         NTT_Inner (F_Hat => F_Hat,
                    Zeta  => Zeta_ExpC (4 + Byte (J)),
                    Start => J * 2 * 32,
                    Len   => 32);
      end loop;
      -- I = 3 -----------------
      for J in I32 range 0 .. 7 loop
         NTT_Inner (F_Hat => F_Hat,
                    Zeta  => Zeta_ExpC (8 + Byte (J)),
                    Start => J * 2 * 16,
                    Len   => 16);
      end loop;
      -- I = 4 -----------------
      for J in I32 range 0 .. 15 loop
         NTT_Inner (F_Hat => F_Hat,
                    Zeta  => Zeta_ExpC (16 + Byte (J)),
                    Start => J * 2 * 8,
                    Len   => 8);
      end loop;
      -- I = 5 -----------------
      for J in I32 range 0 .. 31 loop
         NTT_Inner (F_Hat => F_Hat,
                    Zeta  => Zeta_ExpC (32 + Byte (J)),
                    Start => J * 2 * 4,
                    Len   => 4);
      end loop;
      -- I = 6 -----------------
      for J in I32 range 0 .. 63 loop
         NTT_Inner (F_Hat => F_Hat,
                    Zeta  => Zeta_ExpC (64 + Byte (J)),
                    Start => J * 2 * 2,
                    Len   => 2);
      end loop;
      -------------------

      return F_Hat;
   end NTT;
end NTT32;

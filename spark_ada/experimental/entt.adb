--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

with Ada.Text_IO; use Ada.Text_IO;
package body ENTT
  with SPARK_Mode => On
is
   subtype NTT_Len_Bit_Index is Natural range 0 .. 6;
   subtype NTT_Len_Power     is Natural range 1 .. 7;

   --  A power of 2 between 2 and 128. Used in NTT and NTT_Inv
   subtype Len_T is Index_256
      with Dynamic_Predicate => (for some I in NTT_Len_Power => Len_T = 2**I);

   --  A power of 2 between 1 and 64. Used in NTT and NTT_Inv
   subtype Count_T is Index_256
      with Dynamic_Predicate => (for some I in NTT_Len_Bit_Index => Count_T = 2**I);

   --  A power of 2 between 4 and 256
   subtype NTT_Slice_Length is I32
      with Dynamic_Predicate => (for some I in 2 .. 8 => NTT_Slice_Length = 2**I);

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


   procedure NTTu_Inner (F_Hat : in out Poly_Zq;
                         Zeta  : in     Zq;
                         Start : in     Index_256;
                         Len   : in     Len_T)
       with No_Inline,
            Global => null,
            Pre    => Start <= 252 and
                      Start + 2 * Len <= 256
   is
      T : Zq;
   begin
      for J in Index_256 range Start .. Start + (Len - 1) loop
         pragma Loop_Optimize (Ivdep, Vector);
         T               := Zeta * F_Hat (J + Len);
         F_Hat (J + Len) := F_Hat (J) - T;
         F_Hat (J)       := F_Hat (J) + T;
      end loop;
   end NTTu_Inner;

   --  As above, but with Start => 0, Len => 128, Zeta => 1729
   procedure NTT128_Inner (F_Hat : in out Poly_Zq)
       with No_Inline,
            Global => null
   is
      T : Zq;
   begin
      for J in Index_256 range 0 .. 127 loop
         pragma Loop_Optimize (Ivdep, Vector);
         T               := 1729 * F_Hat (J + 128);
         F_Hat (J + 128) := F_Hat (J) - T;
         F_Hat (J)       := F_Hat (J) + T;
      end loop;
   end NTT128_Inner;

   function NTT (F : in Poly_Zq) return Poly_Zq
     with SPARK_Mode => Off
   is
      subtype K_T is Byte range 1 .. 128;
      F_Hat : Poly_Zq;
      K     : K_T;
      Len   : Len_T;
      Count : Count_T;

      --  procedure NTT_Inner (Zeta  : in     Zq;
      --                       Start : in     Index_256)
      --    with No_Inline,
      --         Global => (In_Out => F_Hat,
      --                    Input  => Len),
      --         Pre    => Start <= 252 and
      --                   Start + 2 * Len <= 256
      --  is
      --     T : Zq;
      --  begin
      --     for J in Index_256 range Start .. Start + (Len - 1) loop
      --        T               := Zeta * F_Hat (J + Len);
      --        F_Hat (J + Len) := F_Hat (J) - T;
      --        F_Hat (J)       := F_Hat (J) + T;
      --     end loop;
      --  end NTT_Inner;

   begin
      F_Hat := F;
      K     := 1;

      for I in NTT_Len_Bit_Index loop
         --  When I = 0, Len = 128, Count = 1
         --       I = 1, Len =  64, Count = 2
         --       ...
         --       I = 6, Len =   2, Count = 64
         Len   := 2**(7 - I);
         Count := 2**I;
         for J in I32 range 0 .. Count - 1 loop
            pragma Loop_Invariant (Count * Len = 128);
            pragma Loop_Invariant (J * 2 * Len <= 252);
            pragma Loop_Invariant (I32 (K) = 2**I + J);
            NTTu_Inner (F_Hat => F_Hat,
                        Zeta  => Zeta_ExpC (K),
                        Start => J * 2 * Len,
                        Len   => Len);
            K := K + 1;
         end loop;

         --  When the inner loop terminates, K has been
         --  incremented Count times, therefore...
         pragma Assert (I32 (K) = 2**I + Count);
         --  But we know that Count = 2**I, so...
         pragma Assert (I32 (K) = 2 * 2**I);
         pragma Assert (I32 (K) = 2**(I + 1));
         pragma Loop_Invariant (2**(I + 1) <= 128);
         pragma Loop_Invariant (I32 (K) = 2**(I + 1));
      end loop;
      pragma Assert (K = 128);
      return F_Hat; --  calls _memcpy()
   end NTT;



   -- I Start Len    J Range     Reads        Writes
   -- 0     0 128    0 .. 127    0 .. 255     0 .. 255

   -- 1     0  64    0 ..  63    0 .. 127     0 .. 127 (bottom half)
   -- 1   128  64  128 .. 191  128 .. 255   128 .. 255 (top half)



   function NTTu (F : in Poly_Zq) return Poly_Zq
     with SPARK_Mode => Off
   is
      F_Hat : Poly_Zq;
   begin
      F_Hat := F;

      -- I = 0 -----------------
--      for J in I32 range 0 .. 0 loop
      NTT128_Inner (F_Hat);
--      NTTu_Inner (F_Hat => F_Hat,
--                  Zeta  => Zeta_ExpC (1),
--                  Start => 0,
--                  Len   => 128);
--      end loop;
      -- I = 1 -----------------
--      for J in I32 range 0 .. 1 loop
         NTTu_Inner (F_Hat => F_Hat,
                     Zeta  => Zeta_ExpC (2),
                     Start => 0,
                     Len   => 64);

         NTTu_Inner (F_Hat => F_Hat,
                     Zeta  => Zeta_ExpC (3),
                     Start => 128,
                     Len   => 64);
--      end loop;
      -- I = 2 -----------------
      for J in I32 range 0 .. 3 loop
         pragma Loop_Optimize (Unroll);
         NTTu_Inner (F_Hat => F_Hat,
                     Zeta  => Zeta_ExpC (4 + Byte (J)),
                     Start => J * 2 * 32,
                     Len   => 32);
      end loop;
      -- I = 3 -----------------
      for J in I32 range 0 .. 7 loop
         pragma Loop_Optimize (Unroll);
         NTTu_Inner (F_Hat => F_Hat,
                     Zeta  => Zeta_ExpC (8 + Byte (J)),
                     Start => J * 2 * 16,
                     Len   => 16);
      end loop;
      -- I = 4 -----------------
      for J in I32 range 0 .. 15 loop
         pragma Loop_Optimize (Unroll);
         NTTu_Inner (F_Hat => F_Hat,
                     Zeta  => Zeta_ExpC (16 + Byte (J)),
                     Start => J * 2 * 8,
                     Len   => 8);
      end loop;
      -- I = 5 -----------------
      for J in I32 range 0 .. 31 loop
         pragma Loop_Optimize (Unroll);
         NTTu_Inner (F_Hat => F_Hat,
                     Zeta  => Zeta_ExpC (32 + Byte (J)),
                     Start => J * 2 * 4,
                     Len   => 4);
      end loop;
      -- I = 6 -----------------
      for J in I32 range 0 .. 63 loop
         pragma Loop_Optimize (Unroll);
         NTTu_Inner (F_Hat => F_Hat,
                     Zeta  => Zeta_ExpC (64 + Byte (J)),
                     Start => J * 2 * 2,
                     Len   => 2);
      end loop;
      -------------------

      return F_Hat;
   end NTTu;

   function NTTsrl (F : in UPoly;
                    K : in SU7) return UPoly
     with Global => null,
          Pre    => F'First = 0 and then
                    F'Length in NTT_Slice_Length and then
                    ((F'Length =   4 and K in 64 .. 127) or
                     (F'Length =   8 and K in 32 ..  63) or
                     (F'Length =  16 and K in 16 ..  31) or
                     (F'Length =  32 and K in  8 ..  15) or
                     (F'Length =  64 and K in  4 ..   7) or
                     (F'Length = 128 and K in  2 ..   3) or
                     (F'Length = 256 and K = 1)),
          Post   => NTTsrl'Result'First = 0 and
                    NTTsrl'Result'Length = F'Length;

   function NTTsrl (F : in UPoly;
                    K : in SU7) return UPoly
   is
      subtype This_Poly is UPoly (F'Range);

      --  Length and subtype for each half of F
      Len : constant Len_T := F'Length / 2;
      pragma Assert (Len * 2 = F'Length);
      subtype Half_Poly is UPoly (0 .. Len - 1);

      function CT_Lowerhalf (T    : in This_Poly;
                             Zeta : in Zq) return Half_Poly
        with Global => (Input => Len,
                        Proof_In => F),
             Pre    => T'First = 0
      is
         R : Half_Poly;
      begin
         for I in R'Range loop
            R (I) := T (I) + Zeta * T (I + Len);
         end loop;
         return R;
      end CT_Lowerhalf;

      function CT_Upperhalf (T    : in This_Poly;
                             Zeta : in Zq) return Half_Poly
        with Global => (Input    => Len,
                        Proof_In => F),
             Pre    => T'First = 0
      is
         R : Half_Poly;
      begin
         for J in R'Range loop
            R (J) := T (J) - Zeta * T (J + Len);
         end loop;
         return R;
      end CT_Upperhalf;

      function CT_Butterfly (T    : in This_Poly;
                             Zeta : in Zq) return This_Poly
        with Global => (Input    => Len,
                        Proof_In => F),
             Pre    => T'First = 0 and
                       T'Length in NTT_Slice_Length
      is
      begin
         return CT_Lowerhalf (T, Zeta) & CT_Upperhalf (T, Zeta);
      end CT_Butterfly;

      Zeta : constant Zq := Zeta_ExpC (K);
      T    : constant This_Poly := CT_Butterfly (F, Zeta);
   begin
      return (if T'Length = 4 then
                 T
              else
                 NTTsrl (Half_Poly (T   (0 .. Len - 1)), K * 2) &
                 NTTsrl (Half_Poly (T (Len .. T'Last)),  K * 2 + 1));
   end NTTsrl;


   function NTTsr (F : in Poly_Zq) return Poly_Zq
   is
   begin
      return NTTsrl (F, 1);
   end NTTsr;

   procedure NTTir (F : in out Poly_Zq)
   is
      procedure NTTirl (Start : in Index_256;
                        Len   : in Len_T;
                        K     : in SU7)
        with Global => (In_Out => F),
             Pre    => Start <= 252 and then
                       Start + 2 * Len <= 256 and then
                       ((Len =   2 and K in 64 .. 127) or
                        (Len =   4 and K in 32 ..  63) or
                        (Len =   8 and K in 16 ..  31) or
                        (Len =  16 and K in  8 ..  15) or
                        (Len =  32 and K in  4 ..   7) or
                        (Len =  64 and K in  2 ..   3) or
                        (Len = 128 and K = 1));

      procedure NTTirl (Start : in Index_256;
                        Len   : in Len_T;
                        K     : in SU7)
      is
      begin
         NTTu_Inner (F, Zeta_ExpC (K), Start, Len);
         if Len >= 4 then
            NTTirl (Start,       Len / 2, K * 2);
            NTTirl (Start + Len, Len / 2, K * 2 + 1);
         end if;
      end NTTirl;

   begin
      NTTirl (0, 128, 1);
   end NTTir;


   procedure NTTtir (F : in out Poly_Zq)
     with SPARK_Mode => Off -- no nested tasking allowed in SPARK...
   is
      task type NTTtirl (Start : Index_256;
                         Len   : Len_T;
                         K     : SU7);

      --  Introduce a renaming of NTTtirl here to avoid a task type having
      --  to name itself in its body. (RM 8.6 (17/3))
      subtype NTT2 is NTTtirl;

      task body NTTtirl
      is
      begin
         NTTu_Inner (F, Zeta_ExpC (K), Start, Len);
         if Len >= 4 then
            declare
               --  Spawn two more tasks for the left and right halves of the given array
               TL : NTT2 (Start,       Len / 2, K * 2);
               TR : NTT2 (Start + Len, Len / 2, K * 2 + 1);
            begin
               --  This block statement will terminate when both dependent tasks
               --  TL and TR have terminated.
              null;
            end;
         end if;
      end NTTtirl;

      T1 : NTTtirl (0, 128, 1);
   begin
      --  This block statement will terminate when dependent task T1
      --  has terminated.
      null;
   end NTTtir;


   --====================
   -- Inverse NTT
   --====================

   procedure NTT_Inv_Inner (F_Hat : in out Poly_Zq;
                            Zeta  : in     Zq;
                            Start : in     Index_256;
                            Len   : in     Len_T)
     with No_Inline,
          Global => null,
          Pre    => Start <= 252 and
                    Start + 2 * Len <= 256
   is
      T : Zq;
   begin
      for J in Index_256 range Start .. Start + (Len - 1) loop
         pragma Loop_Optimize (Ivdep, Vector);
         T := F_Hat (J);
         F_Hat (J) := T + F_Hat (J + Len);
         F_Hat (J + Len) := Zeta * (F_Hat (J + Len) - T);
      end loop;
   end NTT_Inv_Inner;

   --  All elements of Left, multiplied by Right (mod q)
   function "*" (Left  : in Poly_Zq;
                 Right : in Zq) return Poly_Zq
     with No_Inline
   is
      R : Poly_Zq;
   begin
      for I in R'Range loop
         R (I) := Left (I) * Right; --  implicitly mod q
      end loop;
      return R;
   end "*";


   --  Algorithm 9
   function NTT_Inv (F : in Poly_Zq) return Poly_Zq
   is
      subtype K_T is Byte range 0 .. 127;
      F_Hat : Poly_Zq;
      K     : K_T;
      Len   : Len_T;
      Count : Count_T;
   begin
      F_Hat := F; --  calls _memcpy()
      K     := 127;

      --  note "reverse" loop here for NTT_Inv
      for I in reverse NTT_Len_Bit_Index loop
         --  When I = 6, Len =   2, Count = 64
         --       I = 5, Len =   4, Count = 32
         --       I = 4, Len =   8, Count = 16
         --       I = 3, Len =  16, Count = 8
         --       I = 2, Len =  32, Count = 4
         --       I = 1, Len =  64, Count = 2
         --       I = 0, Len = 128, Count = 1
         Len   := 2**(7 - I);
         Count := 2**I;
         for J in I32 range 0 .. Count - 1 loop
            pragma Loop_Invariant (Count * Len = 128);
            pragma Loop_Invariant (J * 2 * Len <= 252);
            pragma Loop_Invariant (I32 (K) = 2**I + Count - J - 1);

            NTT_Inv_Inner (F_Hat => F_Hat,
                           Zeta  => Zeta_ExpC (K),
                           Start => J * 2 * Len,
                           Len   => Len);
            K := K - 1;
         end loop;

         --  When the inner loop terminates, K has been
         --  decremented Count times, therefore
         --  K = 2**I + Count - Count - 1, which simplifies to
         pragma Loop_Invariant (I32 (K) = 2**I - 1);
      end loop;

      --  Substitute I = 0 into the outer loop invariant to get
      pragma Assert (K = 0);
      return F_Hat * 3303;
   end NTT_Inv;


   --  As per standard, but outer loop unrolled
   function NTT_Invu (F : in Poly_Zq) return Poly_Zq
   is
      F_Hat : Poly_Zq;
   begin
      F_Hat := F; --  calls _memcpy()

      -- I = 6, Len =   2, Count = 64
      for J in I32 range 0 .. 63 loop
         pragma Loop_Optimize (Unroll);
         NTT_Inv_Inner (F_Hat => F_Hat,
                        Zeta  => Zeta_ExpC (127 - Byte (J)),
                        Start => J * 4,
                        Len   => 2);
      end loop;

      -- I = 5, Len =   4, Count = 32
      for J in I32 range 0 .. 31 loop
         pragma Loop_Optimize (Unroll);
         NTT_Inv_Inner (F_Hat => F_Hat,
                        Zeta  => Zeta_ExpC (63 - Byte (J)),
                        Start => J * 8,
                        Len   => 4);
      end loop;

      -- I = 4, Len =   8, Count = 16
      for J in I32 range 0 .. 15 loop
         pragma Loop_Optimize (Unroll);
         NTT_Inv_Inner (F_Hat => F_Hat,
                        Zeta  => Zeta_ExpC (31 - Byte (J)),
                        Start => J * 16,
                        Len   => 8);
      end loop;

      -- I = 3, Len =  16, Count = 8
      for J in I32 range 0 .. 7 loop
         pragma Loop_Optimize (Unroll);
         NTT_Inv_Inner (F_Hat => F_Hat,
                        Zeta  => Zeta_ExpC (15 - Byte (J)),
                        Start => J * 32,
                        Len   => 16);
      end loop;

      -- I = 2, Len =  32, Count = 4
      for J in I32 range 0 .. 3 loop
         pragma Loop_Optimize (Unroll);
         NTT_Inv_Inner (F_Hat => F_Hat,
                        Zeta  => Zeta_ExpC (7 - Byte (J)),
                        Start => J * 64,
                        Len   => 32);
      end loop;

      -- I = 1, Len =  64, Count = 2
      NTT_Inv_Inner (F_Hat => F_Hat,
                     Zeta  => Zeta_ExpC (3),
                     Start => 0,
                     Len   => 64);
      NTT_Inv_Inner (F_Hat => F_Hat,
                     Zeta  => Zeta_ExpC (2),
                     Start => 128,
                     Len   => 64);

      -- I = 0, Len = 128, Count = 1
      NTT_Inv_Inner (F_Hat => F_Hat,
                     Zeta  => Zeta_ExpC (1),
                     Start => 0,
                     Len   => 128);

      return F_Hat * 3303;
   end NTT_Invu;

   procedure NTT_Invir (F : in out Poly_Zq)
   is
      procedure NTT_Invirl (Start : in Index_256;
                            Len   : in Len_T;
                            K     : in SU7)
        with Global => (In_Out => F),
             Pre    => Start <= 252 and then
                       Start + 2 * Len <= 256 and then
                       ((Len =   2 and K in 64 .. 127) or
                        (Len =   4 and K in 32 ..  63) or
                        (Len =   8 and K in 16 ..  31) or
                        (Len =  16 and K in  8 ..  15) or
                        (Len =  32 and K in  4 ..   7) or
                        (Len =  64 and K in  2 ..   3) or
                        (Len = 128 and K = 1));

      procedure NTT_Invirl (Start : in Index_256;
                            Len   : in Len_T;
                            K     : in SU7)
      is
      begin
         if Len >= 4 then
            NTT_Invirl (Start,       Len / 2, K * 2 + 1);
            NTT_Invirl (Start + Len, Len / 2, K * 2);
         end if;

         NTT_Inv_Inner (F, Zeta_ExpC (K), Start, Len);
      end NTT_Invirl;

   begin
      NTT_Invirl (0, 128, 1);
      F := F * 3303;
   end NTT_Invir;



   function NTT_Invsrl (F : in UPoly;
                        K : in SU7) return UPoly
     with Global => null,
          Pre    => F'First = 0 and then
                    F'Length in NTT_Slice_Length and then
                    ((F'Length =   4 and K in 64 .. 127) or
                     (F'Length =   8 and K in 32 ..  63) or
                     (F'Length =  16 and K in 16 ..  31) or
                     (F'Length =  32 and K in  8 ..  15) or
                     (F'Length =  64 and K in  4 ..   7) or
                     (F'Length = 128 and K in  2 ..   3) or
                     (F'Length = 256 and K = 1)),
          Post   => NTT_Invsrl'Result'First = 0 and
                    NTT_Invsrl'Result'Length = F'Length;

   function NTT_Invsrl (F : in UPoly;
                        K : in SU7) return UPoly
   is
      subtype This_Poly is UPoly (F'Range);

      --  Length and subtype for each half of F
      Len : constant Len_T := F'Length / 2;
      pragma Assert (Len * 2 = F'Length);
      subtype Half_Poly is UPoly (0 .. Len - 1);

      Zeta : constant Zq := Zeta_ExpC (K);

      function GS_Lowerhalf (T : in This_Poly) return Half_Poly
        with Global => (Input    => Len,
                        Proof_In => F),
             Pre    => T'First = 0
      is
         R : Half_Poly;
      begin
         for J in Index_256 range 0 .. Len - 1 loop
            R (J) := T (J) + T (J + Len);
         end loop;
         return R;
      end GS_Lowerhalf;

      function GS_Upperhalf (T : in This_Poly) return Half_Poly
        with Global => (Input    => (Len, Zeta),
                        Proof_In => F),
             Pre    => T'First = 0
      is
         R : Half_Poly;
      begin
         for J in R'Range loop
            R (J) := Zeta * (T (J + Len) - T (J));
         end loop;
         return R;
      end GS_Upperhalf;

      function GS_Butterfly (T : in This_Poly) return This_Poly
        with Global => (Input    => (Len, Zeta),
                        Proof_In => F),
             Pre    => T'First = 0 and
                       T'Length in NTT_Slice_Length
      is
      begin
         return GS_Lowerhalf (T) & GS_Upperhalf (T);
      end GS_Butterfly;

   begin
      return (if F'Length = 4 then
                 GS_Butterfly (F)
              else
                 GS_Butterfly (NTT_Invsrl (Half_Poly (F   (0 .. Len - 1)), K * 2 + 1) &
                               NTT_Invsrl (Half_Poly (F (Len .. F'Last)),  K * 2)));
   end NTT_Invsrl;

   function NTT_Invsr (F : in Poly_Zq) return Poly_Zq
   is
      T : Poly_Zq;
   begin
      T := NTT_Invsrl (F, 1);
      return T * 3303;
   end NTT_Invsr;


end ENTT;

with Ada.Text_IO; use Ada.Text_IO;
package body ENTTRef
  with SPARK_Mode => On
is
   function Shift_Right_Arithmetic (Value  : I32;
                                    Amount : Natural) return I32
     with Import,
          Convention => Intrinsic;

   subtype SU7 is Byte range 0 .. 127;

   type Zeta_Exp_Table_Type is array (SU7) of Zeta_Range;

   Zeta_ExpC : constant Zeta_Exp_Table_Type :=
     (-1044,  -758,  -359, -1517,  1493,  1422,   287,   202,
      -171,   622,  1577,   182,   962, -1202, -1474,  1468,
       573, -1325,   264,   383,  -829,  1458, -1602,  -130,
      -681,  1017,   732,   608, -1542,   411,  -205, -1571,
      1223,   652,  -552,  1015, -1293,  1491,  -282, -1544,
       516,    -8,  -320,  -666, -1618, -1162,   126,  1469,
      -853,   -90,  -271,   830,   107, -1421,  -247,  -951,
      -398,   961, -1508,  -725,   448, -1065,   677, -1275,
     -1103,   430,   555,   843, -1251,   871,  1550,   105,
       422,   587,   177,  -235,  -291,  -460,  1574,  1653,
      -246,   778,  1159,  -147,  -777,  1483,  -602,  1119,
     -1590,   644,  -872,   349,   418,   329,  -156,   -75,
       817,  1097,   603,   610,  1322, -1285, -1465,   384,
     -1215,  -136,  1218, -1335,  -874,   220, -1187, -1659,
     -1185, -1530, -1278,   794, -1510,  -854,  -870,   478,
      -108,  -308,   996,   991,   958, -1460,  1522,  1628);

   Red_Count : Natural := 0;

   procedure PP (F : in Poly_Zq)
   is
   begin
      for I in F'Range loop
         Put (F (I)'Img);
      end loop;
      New_Line (2);
   end PP;


   function RCount return Natural
     with SPARK_Mode => Off
   is
   begin
      return Red_Count;
   end RCount;

   --  Given
   --     int32_t a;
   --  mimics
   --    int16_t r = (int16_t) a;
   --
   --  which is implementation-defined in C, but most compilers
   --  implement this by jsut dropping the most significant 16
   --  bits, and re-interpreting bit 15 as the sign bit of the answer.
   function To16 (A : in Integer_32) return Integer_16
   is
      subtype Bit is Integer_32 range 0 .. 1;
      Flip_Factor : Bit;
      T : Integer_32;
   begin
      T := A mod 65536;
      Flip_Factor := Boolean'Pos (T >= 32768);

      --  If T is in     0 .. 32767, then leave it alone.
      --  If T is in 32768 .. 65535, then subtract 65536
      T := T - (Flip_Factor * 65536);
      return Integer_16 (T);
   end To16;


   function Montgomery_Reduce (X : in Mont_Domain) return Mont_Range
     with SPARK_Mode => Off
   is
      pragma Suppress (All_Checks);
      T1, T3, T4, T5 : I32;
      T2             : I16;
   begin
--      Red_Count := Red_Count + 1;
      T1 := X * QINV;
      T2 := I16 (T1);
      T3 := I32 (T2);
      T4 := X - T3 * Q;
      T5 := Shift_Right_Arithmetic (T4, 16);
      return Mont_Range (T5);
   end Montgomery_Reduce;

   subtype BRange is Integer_16 range -1664 .. 1664;

   -- Barrett reduction
   function BR (A : in Integer_16) return BRange
   is
      --  int16_t t;
      --  const int16_t v = ((1<<26) + KYBER_Q/2)/KYBER_Q;
      --
      --  t  = ((int32_t)v*a + (1<<25)) >> 26;
      --  t *= KYBER_Q;
      --  return a - t;

       C25 : constant := 2**25;
       C26 : constant := 2**26;
       V   : constant := (C26 + (Q / 2)) / Q;
       T   : Integer_32;
       T2  : Integer_16;
       R   : BRange;
   begin
       pragma Assert (V = 20159);
       --  t  = ((int32_t)v * a + (1 << 25)) >> 26;
       T2 := To16 (Shift_Right_Arithmetic (V * Integer_32 (A) + C25, 26));
       T2 := T2 * Q;
--       T2 := To16 (T);
       T := Integer_32 (A) - Integer_32 (T2);
       T2 := To16 (T);
       R := BRange (T2);
       return R;
   end BR;

   function FQMul (Z : in Zeta_Range; --  First parameter is always Zeta
                   B : in I16) return Mont_Range
   is
      D : Mont_Domain;
   begin
      pragma Assert (I32 (Z) * I32 (B) >= Mont_Domain'First);
      pragma Assert (I32 (Z) * I32 (B) <= Mont_Domain'Last);
      D := I32 (Z) * I32 (B);
      return Montgomery_Reduce (D);
   end FQMul;

   procedure NTT_Inner (F_Hat : in out Poly_Zq;
                        ZI    : in     SU7;
                        Start : in     Index_256;
                        Len   : in     Index_256)
       with No_Inline,
            Global => null,
            Pre    => Start <= 252 and
                      Start + 2 * Len <= 256 and
                      (for all K in Index_256 => F_Hat (K) in Mont_Range7),
            Post   =>
                      -- Elements 0 .. Start - 1 are unchanged
                      (for all I in Index_256 range 0 .. Start - 1 => F_Hat (I) = F_Hat'Old (I))
                     and
                      (
                       -- Elements Start through Start + 2 * Len - 1 are updated
                      (for all I in Index_256 range Start .. Start + (Len - 1) =>
                       ((F_Hat (I)       >= F_Hat'Old (I) - Q) and
                        (F_Hat (I)       <= F_Hat'Old (I) + Q) and
                        (F_Hat (I + Len) >= F_Hat'Old (I) - Q) and
                        (F_Hat (I + Len) <= F_Hat'Old (I) + Q)
                       )
                       )
                      )
                    and
                      --  Elements from Start + 2 * Len .. 255 are unchanged
                      (for all I in Index_256 range Start + 2 * Len  .. 255 => F_Hat (I) = F_Hat'Old (I));

   procedure NTT_Inner (F_Hat : in out Poly_Zq;
                        ZI    : in     SU7;
                        Start : in     Index_256;
                        Len   : in     Index_256)
   is
      T : Mont_Range;
   begin
      for J in Index_256 range Start .. Start + (Len - 1) loop
         pragma Loop_Invariant
            -- Elements 0 .. Start - 1 are unchanged
           (for all I in Index_256 range 0 .. Start - 1 => F_Hat (I) = F_Hat'Loop_Entry (I));
         pragma Loop_Invariant
           (
            -- Elements Start through J - 1 are updated
            (for all I in Index_256 range Start .. J - 1 =>
             ((F_Hat (I) >= F_Hat'Loop_Entry (I) - Q) and
              (F_Hat (I) <= F_Hat'Loop_Entry (I) + Q)
             )
            )
           );
         pragma Loop_Invariant
            -- Elements J .. Start + Len - 1 are unchanged
            (for all I in Index_256 range J .. Start + Len - 1 => F_Hat (I) = F_Hat'Loop_Entry (I));
         pragma Loop_Invariant
            --  Elements Start + Len through J + Len - 1 are updated
            (for all I in Index_256 range Start .. J - 1 =>
             ((F_Hat (I + Len) >= F_Hat'Loop_Entry (I) - Q) and
              (F_Hat (I + Len) <= F_Hat'Loop_Entry (I) + Q))
            );
         pragma Loop_Invariant
            --  Elements from J + Len .. 255 are unchanged
            (for all I in Index_256 range J + Len .. 255 => F_Hat (I) = F_Hat'Loop_Entry (I));

         T := FQMul (Zeta_ExpC (ZI), F_Hat (J + Len));
         F_Hat (J + Len) := F_Hat (J) - T;
         F_Hat (J)       := F_Hat (J) + T;

--         pragma Loop_Invariant
--            -- Elements 0 .. Start - 1 are unchanged
--           (for all I in Index_256 range 0 .. Start - 1 => F_Hat (I) = F_Hat'Loop_Entry (I));
--         pragma Loop_Invariant
--           (
--            -- Elements Start through J are updated
--            (for all I in Index_256 range Start .. J =>
--             ((F_Hat (I) >= F_Hat'Loop_Entry (I) - Q) and
--              (F_Hat (I) <= F_Hat'Loop_Entry (I) + Q)
--             )
--            )
--           );
--         pragma Loop_Invariant
--            -- Elements J + 1 .. Start + Len - 1 are unchanged
--            (for all I in Index_256 range J + 1 .. Start + Len - 1 => F_Hat (I) = F_Hat'Loop_Entry (I));
--         pragma Loop_Invariant
--            --  Elements Start + Len through J + Len are updated
--            (for all I in Index_256 range Start .. J =>
--             ((F_Hat (I + Len) >= F_Hat'Loop_Entry (I) - Q) and
--              (F_Hat (I + Len) <= F_Hat'Loop_Entry (I) + Q))
--            );
--         pragma Loop_Invariant
--            --  Elements from J + Len + 1 .. 255 are unchanged
--            (for all I in Index_256 range J + Len + 1 .. 255 => F_Hat (I) = F_Hat'Loop_Entry (I));

      end loop;
   end NTT_Inner;



   procedure NTT (F : in out Poly_Zq)
   is
      Len   : Index_256;
      Start : I32;
      K     : Byte;
   begin
      Len := 128;
      K   := 1;

      loop
         Start := 0;

         pragma Loop_Invariant (Len = 2 or
                                Len = 4 or
                                Len = 8 or
                                Len = 16 or
                                Len = 32 or
                                Len = 64 or
                                Len = 128);
         pragma Loop_Invariant (Len >= 2);
         pragma Loop_Invariant (Len <= 128);
--         pragma Loop_Invariant (Start >= 0);
         pragma Loop_Invariant (Start <= 256 - (2 * Len));
--         pragma Loop_Invariant (K = Byte (256 / (Len * 2)));

         loop
            pragma Loop_Invariant (Len = 2 or
                                   Len = 4 or
                                   Len = 8 or
                                   Len = 16 or
                                   Len = 32 or
                                   Len = 64 or
                                   Len = 128);
            pragma Loop_Invariant (Len >= 2);
            pragma Loop_Invariant (Len <= 128);
            pragma Loop_Invariant (Start >= 0);
            pragma Loop_Invariant (Start <= 256 - (2 * Len));
--            pragma Loop_Invariant (K = Byte ((Start + 256) / (Len * 2)));

            NTT_Inner (F, K, Start, Len);
            K := K + 1;

            Start := Start + (Len * 2);
            exit when Start >= 256;
         end loop;

         exit when Len = 2;
         Len := Len / 2;
      end loop;

      for K in F'range loop
         F (K) := BR (F (K));
      end loop;

   end NTT;

---------------------------------------
   procedure NTT_Inner128 (F_Hat : in out Poly_Zq;
                           Zeta  : in     Zeta_Range)
       with No_Inline,
            Global => null,
            Pre  => (for all K in Index_256 => F_Hat (K) in Mont_Range),
            Post => (for all K in Index_256 => F_Hat (K) in Mont_Range2);

   procedure NTT_Inner128 (F_Hat : in out Poly_Zq;
                           Zeta  : in     Zeta_Range)
   is
      T : Mont_Range;
   begin
      for J in Index_256 range 0 .. 127 loop
         T := FQMul (Zeta, F_Hat (J + 128));
         F_Hat (J + 128) := F_Hat (J) - T;
         F_Hat (J)       := F_Hat (J) + T;

         --  Elements 0 though J have been modified
         pragma Loop_Invariant
            (for all K in Index_256 range 0 .. J =>
              (F_Hat (K) in Mont_Range2));
         --  Elements J + 1 through 127 have NOT been modified
         pragma Loop_Invariant
            (for all K in Index_256 range J + 1 .. 127 =>
              (F_Hat (K) in Mont_Range));
         --  Elements 128 though J + 128 have been modified
         pragma Loop_Invariant
            (for all K in Index_256 range 128 .. J + 128 =>
              (F_Hat (K) in Mont_Range2));
         --  Elements J + 129 though 255 have NOT been modified
         pragma Loop_Invariant
            (for all K in Index_256 range J + 129 .. 255 =>
              (F_Hat (K) in Mont_Range));

      end loop;

      --  substitute J = 128 into that
      pragma Assert
         (for all K in Index_256 range 0 .. 127 =>
           (F_Hat (K) in Mont_Range2));
      pragma Assert
         (for all K in Index_256 range 128 .. 255 =>
           (F_Hat (K) in Mont_Range2));

      --  and therefore...
      pragma Assert
         (for all K in Index_256 =>
           (F_Hat (K) in Mont_Range2));

   end NTT_Inner128;

   procedure NTT_Inner64 (F_Hat : in out Poly_Zq;
                          Zeta  : in     Zeta_Range;
                          Start : in     Index_256)
       with No_Inline,
            Global => null,
            Pre    => Start <= 128 and then
                      --  The elements about to be modified are in Mont_Range2
                      ((for all K in Index_256 range Start       .. Start +  63 => (F_Hat (K) in Mont_Range2)) and
                       (for all K in Index_256 range Start +  64 .. Start + 127 => (F_Hat (K) in Mont_Range2))),
            Post   => --  The elements that HAVE been modified are now in Mont_Range3
                      (for all K in Index_256 range Start       .. Start +  63 => (F_Hat (K) in Mont_Range3)) and
                      (for all K in Index_256 range Start +  64 .. Start + 127 => (F_Hat (K) in Mont_Range3)) and
                      --  Unmodified elements preserve their initial value (and range)
                      (for all K in Index_256 range     0       .. Start -   1 => (F_Hat (K) = F_Hat'Old (K))) and
                      (for all K in Index_256 range Start + 128 .. 255         => (F_Hat (K) = F_Hat'Old (K)));

   procedure NTT_Inner64 (F_Hat : in out Poly_Zq;
                          Zeta  : in     Zeta_Range;
                          Start : in     Index_256)
   is
      T : Mont_Range;
   begin
      for J in Index_256 range Start .. Start + 63 loop
         T := FQMul (Zeta, F_Hat (J + 64));
         F_Hat (J + 64) := F_Hat (J) - T;
         F_Hat (J)      := F_Hat (J) + T;

         --  Elements 0 though Start - 1 have NOT been modified
         pragma Loop_Invariant
            (for all K in Index_256 range 0 .. Start - 1 =>
              (F_Hat (K) = F_Hat'Loop_Entry (K)));

         --  Elements Start though J have been modified
         pragma Loop_Invariant
            (for all K in Index_256 range Start .. J =>
              (F_Hat (K) in Mont_Range3));

         --  Elements Start + J + 1 through Start + 63 have NOT been modified
         pragma Loop_Invariant
            (for all K in Index_256 range J + 1 .. Start + 63 =>
              (F_Hat (K) = F_Hat'Loop_Entry (K)));

         --  Elements Start + 64 though J + 64 have been modified
         pragma Loop_Invariant
            (for all K in Index_256 range Start + 64 .. J + 64 =>
              (F_Hat (K) in Mont_Range3));

         --  Elements J + 65 though 255 have NOT been modified
         pragma Loop_Invariant
            (for all K in Index_256 range J + 65 .. 255 =>
              (F_Hat (K) = F_Hat'Loop_Entry (K)));

      end loop;
      --  substitute J = Start + 63 into each loop invariant to get the postcondition
   end NTT_Inner64;


   procedure Do_Layers_3_4 (F : in out Poly_Zq)
      with Pre  => (for all I in F'Range => F (I) in Mont_Range3),
           Post => (for all I in F'Range => F (I) in Mont_Range5)
   is
   begin
      --  LAYER 3 I = 2 -----------------
      NTT_Inner (F, 4, 0, 32);
      NTT_Inner (F, 5, 64, 32);
      NTT_Inner (F, 6, 128, 32);
      NTT_Inner (F, 7, 192, 32);

      pragma Assert (for all I in F'Range => F (I) in Mont_Range4);

      NTT_Inner (F, 8,    0, 16);
      NTT_Inner (F, 9,   32, 16);
      NTT_Inner (F, 10,  64, 16);
      NTT_Inner (F, 11,  96, 16);
      NTT_Inner (F, 12, 128, 16);
      NTT_Inner (F, 13, 160, 16);
      NTT_Inner (F, 14, 192, 16);
      NTT_Inner (F, 15, 224, 16);

      pragma Assert (for all I in F'Range => F (I) in Mont_Range5);
   end Do_Layers_3_4;


   procedure NTTu (F : in out Poly_Zq)
--      with SPARK_Mode => Off
   is
   begin
      --  LAYER 1 I = 0 -----------------
      NTT_Inner128 (F_Hat => F,
                    Zeta  => Zeta_ExpC (1));
      pragma Assert (for all I in F'Range => F (I) in Mont_Range2);

      --  LAYER 2 I = 1 -----------------
      NTT_Inner64 (F_Hat => F,
                   Zeta  => Zeta_ExpC (2),
                   Start => 0);

      --  Substitute Start = 0 into the post-condition of NTT_Inner64 and simplify to get:
      pragma Assert ((for all K in Index_256 range 0   ..  63 => (F (K) in Mont_Range3)) and
                     (for all K in Index_256 range 64  .. 127 => (F (K) in Mont_Range3)) and
                     (for all K in Index_256 range 128 .. 255 => (F (K) in Mont_Range2)));

      NTT_Inner64 (F_Hat => F,
                   Zeta  => Zeta_ExpC (3),
                   Start => 128);

      --  Substitute Start = 128 into the post-condition of NTT_Inner64 and simplify to get:
      pragma Assert ((for all K in Index_256 range 128 .. 191 => (F (K) in Mont_Range3)) and
                     (for all K in Index_256 range 192 .. 255 => (F (K) in Mont_Range3)) and
                     (for all K in Index_256 range 0   .. 127 => (F (K) in Mont_Range3))); -- from above

      --  Therefore, ALL elements of F are in Mont_Range3
      pragma Assert (for all I in F'Range => F (I) in Mont_Range3);

      Do_Layers_3_4 (F);

      -- LAYER 5 I = 4 -----------------
      for J in I32 range 0 .. 15 loop
         NTT_Inner (F_Hat => F,
                    ZI    => 16 + Byte (J),
                    Start => J * 2 * 8,
                    Len   => 8);
      end loop;
      pragma Assert (for all I in F'Range => F (I) in Mont_Range6);

      -- LAYER 6 I = 5 -----------------
      for J in I32 range 0 .. 31 loop
         NTT_Inner (F_Hat => F,
                    ZI    => 32 + Byte (J),
                    Start => J * 2 * 4,
                    Len   => 4);
      end loop;
      pragma Assert (for all I in F'Range => F (I) in Mont_Range7);

      -- LAYER 7 I = 6 -----------------
      for J in I32 range 0 .. 63 loop
         NTT_Inner (F_Hat => F,
                    ZI    => 64 + Byte (J),
                    Start => J * 2 * 2,
                    Len   => 2);
      end loop;
      -------------------
      pragma Assert (for all I in F'Range => F (I) in Mont_Range8);

      --  Should do Barrett Reduction here
      for K in F'range loop
         F (K) := BR (F (K));
      end loop;

      pragma Assert (for all I in F'Range => F (I) in Mont_Range);

   end NTTu;

end ENTTRef;

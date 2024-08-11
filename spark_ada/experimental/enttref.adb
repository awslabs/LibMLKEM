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

   function RCount return Natural
   is
   begin
      return Red_Count;
   end RCount;

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
                        Zeta  : in     Zeta_Range;
                        Start : in     Index_256;
                        Len   : in     Index_256)
       with No_Inline,
            Global => null,
            Pre    => Start <= 252 and
                      Start + 2 * Len <= 256;


   procedure NTT_Inner (F_Hat : in out Poly_Zq;
                        Zeta  : in     Zeta_Range;
                        Start : in     Index_256;
                        Len   : in     Index_256)
   is
      T : Mont_Range;
   begin
      for J in Index_256 range Start .. Start + (Len - 1) loop
         T := FQMul (Zeta, F_Hat (J + Len));
         F_Hat (J + Len) := F_Hat (J) - T;
         F_Hat (J)       := F_Hat (J) + T;
      end loop;
   end NTT_Inner;



   procedure NTT (F : in out Poly_Zq)
   is
      Len, J  : Index_256;
      Start   : I32;
      K       : Byte;
      Zeta, T : I16;
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
         pragma Loop_Invariant (Start >= 0);
         pragma Loop_Invariant (Start <= 256 - (2 * Len));
         pragma Loop_Invariant (K = Byte (256 / (Len * 2)));

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
            pragma Loop_Invariant (K = Byte ((Start + 256) / (Len * 2)));

            Zeta := Zeta_ExpC (K);
            Put_Line ("Len =" & Len'Img & " Start =" & Start'Img);
            K := K + 1;

            NTT_Inner (F, Zeta, Start, Len);

            Start := Start + (Len * 2);
            exit when Start >= 256;
         end loop;

         exit when Len = 2;
         Len := Len / 2;
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
         --  Elements 0 though J - 1 have been modified
         pragma Loop_Invariant
            (for all K in Index_256 range 0 .. J - 1 =>
              (F_Hat (K) in Mont_Range2));
         --  Elements J though 127 have NOT been modified
         pragma Loop_Invariant
            (for all K in Index_256 range J .. 127 =>
              (F_Hat (K) in Mont_Range));
         --  Elements 128 though J + 127 have been modified
         pragma Loop_Invariant
            (for all K in Index_256 range 128 .. J + 127 =>
              (F_Hat (K) in Mont_Range2));
         --  Elements J + 128 though 255 have NOT been modified
         pragma Loop_Invariant
            (for all K in Index_256 range J + 128 .. 255 =>
              (F_Hat (K) in Mont_Range));

         T := FQMul (Zeta, F_Hat (J + 128));
         F_Hat (J + 128) := F_Hat (J) - T;
         F_Hat (J)       := F_Hat (J) + T;

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
            Pre    => Start <= 128 and
                      (Start = 0 or Start = 128) and
                      (for all K in Index_256 => F_Hat (K) in Mont_Range2),
            Post   => (for all K in Index_256 => F_Hat (K) in Mont_Range3);


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
              (F_Hat (K) in Mont_Range2));

         --  Elements Start though Start + J have been modified
         pragma Loop_Invariant
            (for all K in Index_256 range Start .. Start + J =>
              (F_Hat (K) in Mont_Range3));

         --  Elements Start + J + 1though Start + 63 have NOT been modified
         pragma Loop_Invariant
            (for all K in Index_256 range Start + J + 1 .. Start + 63 =>
              (F_Hat (K) in Mont_Range2));

         --  Elements Start + 64 though Start + J + 64 have been modified
         pragma Loop_Invariant
            (for all K in Index_256 range Start + 64 .. Start + 64 + J =>
              (F_Hat (K) in Mont_Range3));

         --  Elements Start + 64 + J + 1 though 255 have NOT been modified
         pragma Loop_Invariant
            (for all K in Index_256 range Start + 64 + J + 1 .. 255 =>
              (F_Hat (K) in Mont_Range2));

      end loop;

      --  substitute J = Start + 64 into that
      pragma Assert (for all K in Index_256 range 0 .. Start - 1 =>
                      (F_Hat (K) in Mont_Range2));
      pragma Assert (for all K in Index_256 range Start .. Start + 63 =>
                      (F_Hat (K) in Mont_Range3));
      pragma Assert (for all K in Index_256 range Start + 64 .. Start + 127 =>
                      (F_Hat (K) in Mont_Range3));
      pragma Assert (for all K in Index_256 range Start + 128 .. 255 =>
                      (F_Hat (K) in Mont_Range2));

   end NTT_Inner64;






   procedure NTTu (F : in out Poly_Zq)
   is
   begin
      NTT_Inner128 (F_Hat => F,
                    Zeta  => Zeta_ExpC (1));
      --------------
      pragma Assert (for all I in F'Range => F (I) in Mont_Range2);

      NTT_Inner64 (F_Hat => F,
                   Zeta  => Zeta_ExpC (2),
                   Start => 0);
      NTT_Inner64 (F_Hat => F,
                   Zeta  => Zeta_ExpC (3),
                   Start => 128);

      pragma Assert (for all I in F'Range => F (I) in Mont_Range3);

      --------------
      for J in I32 range 0 .. 3 loop
         NTT_Inner (F_Hat => F,
                    Zeta  => Zeta_ExpC (4 + Byte (J)),
                    Start => J * 2 * 32,
                    Len   => 32);
      end loop;
      pragma Assert (for all I in F'Range => F (I) in Mont_Range4);
      -- I = 3 -----------------
      for J in I32 range 0 .. 7 loop
         NTT_Inner (F_Hat => F,
                    Zeta  => Zeta_ExpC (8 + Byte (J)),
                    Start => J * 2 * 16,
                    Len   => 16);
      end loop;
      pragma Assert (for all I in F'Range => F (I) in Mont_Range5);
      -- I = 4 -----------------
      for J in I32 range 0 .. 15 loop
         NTT_Inner (F_Hat => F,
                    Zeta  => Zeta_ExpC (16 + Byte (J)),
                    Start => J * 2 * 8,
                    Len   => 8);
      end loop;
      pragma Assert (for all I in F'Range => F (I) in Mont_Range6);
      -- I = 5 -----------------
      for J in I32 range 0 .. 31 loop
         NTT_Inner (F_Hat => F,
                    Zeta  => Zeta_ExpC (32 + Byte (J)),
                    Start => J * 2 * 4,
                    Len   => 4);
      end loop;
      pragma Assert (for all I in F'Range => F (I) in Mont_Range7);
      -- I = 6 -----------------
      for J in I32 range 0 .. 63 loop
         NTT_Inner (F_Hat => F,
                    Zeta  => Zeta_ExpC (64 + Byte (J)),
                    Start => J * 2 * 2,
                    Len   => 2);
      end loop;
      -------------------
      pragma Assert (for all I in F'Range => F (I) in Mont_Range8);
   end NTTu;

end ENTTRef;

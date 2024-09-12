package body RMerge2
  with SPARK_Mode => On
is
   C26 : constant := 2**26;

   function Shift_Right_Arithmetic (Value  : I32;
                                    Amount : Natural) return I32
     with Global => null,
          Import,
          Convention => Intrinsic;

   --  returns equivalent of X >> 26 in C, doing an arithmetic
   --  shift right when X is negative, assuming 2's complement
   --  representation
   pragma Warnings (GNATprove, Off, "no returning annotation*", Reason => "Not needed");
   function ASR32_26 (X : in I32) return I32
   is (Shift_Right_Arithmetic (X, 26))
     with Post => (if X >= 0 then ASR32_26'Result = X / C26 else
                                  ASR32_26'Result = ((X + 1) / C26) - 1);

   Zeta_Min : constant := -1659;
   Zeta_Max : constant :=  1653;
   subtype Zeta_Range is I16 range Zeta_Min .. Zeta_Max;

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


   ------------------------
   --  Montgomery reduction
   ------------------------
   subtype Mont_Domain is I32 range -Q * 32768 .. Q * 32768 - 1;
   subtype Mont_Range is I16 range -QM1 .. QM1;

   subtype Mont_Range2 is I16 range -2 * QM1 .. 2 * QM1;
   subtype Mont_Range3 is I16 range -3 * QM1 .. 3 * QM1;
   subtype Mont_Range4 is I16 range -4 * QM1 .. 4 * QM1;
   subtype Mont_Range5 is I16 range -5 * QM1 .. 5 * QM1;
   subtype Mont_Range6 is I16 range -6 * QM1 .. 6 * QM1;
   subtype Mont_Range7 is I16 range -7 * QM1 .. 7 * QM1;
   subtype Mont_Range8 is I16 range -8 * QM1 .. 8 * QM1;

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
     with Global => null,
          Inline_Always;

   function Montgomery_Reduce (X : in Mont_Domain) return Mont_Range
     with SPARK_Mode => Off
   is
      pragma Suppress (All_Checks);
      T1, T3, T4, T5 : I32;
      T2             : I16;
   begin
      T1 := X * QINV;
      T2 := I16 (T1);
      T3 := I32 (T2);
      T4 := X - T3 * Q;
      T5 := Shift_Right_Arithmetic (T4, 16);
      return Mont_Range (T5);
   end Montgomery_Reduce;

   -- Barrett reduction
   function Barrett_Reduce (A : in Integer_16) return BRange
   is
      --  int16_t t;
      --  const int16_t v = ((1<<26) + KYBER_Q/2)/KYBER_Q;
      --
      --  t  = ((int32_t)v*a + (1<<25)) >> 26;
      --  t *= KYBER_Q;
      --  return a - t;

       C25 : constant := 2**25;
       V   : constant := (C26 + (Q / 2)) / Q;
       T   : Integer_32;
       T2  : Integer_16;
       R   : BRange;
   begin
       pragma Assert (V = 20159);

       T := V * Integer_32 (A);

       pragma Assert (T >= -660_570_112);
       pragma Assert (T <=  660_549_953);

       T := T + C25;

       pragma Assert (T >= -627_015_680);
       pragma Assert (T <=  694_104_385);

       T := ASR32_26 (T);

       pragma Assert (T >= -10);
       pragma Assert (T <=  10);

       T2 := To16 (T * Q);
       T := Integer_32 (A) - Integer_32 (T2);
       T2 := To16 (T);

       R := BRange (T2);
       pragma Annotate (GNATprove, False_Positive, "range check*", "OK");

       return R;
   end Barrett_Reduce;

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

   procedure NTT_Inner12 (F : in out Poly_Zq)
       with Global => null,
            Pre  => (for all K in Index_256 => F (K) in Mont_Range),
            Post => (for all K in Index_256 => F (K) in Mont_Range3);

   procedure NTT_Inner12 (F : in out Poly_Zq)
   is
      Z1 : constant Zeta_Range := Zeta_ExpC (1);
      Z2 : constant Zeta_Range := Zeta_ExpC (2);
      Z3 : constant Zeta_Range := Zeta_ExpC (3);
   begin

      for J in Index_256 range 0 .. 63 loop
         pragma Loop_Invariant
            (for all I in Index_256 range 0       .. J - 1       => (F (I) in Mont_Range3));
         pragma Loop_Invariant
            (for all I in Index_256 range J       .. 63          => (F (I) = F'Loop_Entry (I)));
         pragma Loop_Invariant
            (for all I in Index_256 range 64      .. 64 + J - 1  => (F (I) in Mont_Range3));
         pragma Loop_Invariant
            (for all I in Index_256 range 64 + J  .. 127         => (F (I) = F'Loop_Entry (I)));
         pragma Loop_Invariant
            (for all I in Index_256 range 128     .. 128 + J - 1 => (F (I) in Mont_Range3));
         pragma Loop_Invariant
            (for all I in Index_256 range 128 + J .. 191         => (F (I) = F'Loop_Entry (I)));
         pragma Loop_Invariant
            (for all I in Index_256 range 192     .. 192 + J - 1 => (F (I) in Mont_Range3));
         pragma Loop_Invariant
            (for all I in Index_256 range 192 + J .. 255         => (F (I) = F'Loop_Entry (I)));
         declare
            C1 : constant Index_256 := J;
            C2 : constant Index_256 := C1 + 64;
            C3 : constant Index_256 := C1 + 128;
            C4 : constant Index_256 := C1 + 192;
         begin
            declare
               T11  : constant Mont_Range := FQMul(Z1, F (C3));
               T11x : constant Mont_Range := F (C1);
               T12  : constant Mont_Range := FQMul(Z1, F (C4));
               T12x : constant Mont_Range := F (C2);
            begin
               F (C3) := T11x - T11;
               F (C1) := T11x + T11;
               F (C4) := T12x - T12;
               F (C2) := T12x + T12;
            end;

            declare
               T21  : constant Mont_Range := FQMul(Z2, F (C2));
               T21x : constant Mont_Range2 := F (C1);
               T22  : constant Mont_Range := FQMul(Z3, F (C4));
               T22x : constant Mont_Range2 := F (C3);
            begin
               F (C2) := T21x - T21;
               F (C1) := T21x + T21;
               F (C4) := T22x - T22;
               F (C3) := T22x + T22;
            end;

         end;
      end loop;

   end NTT_Inner12;


   procedure NTT_Inner34_Slice (F     : in out Poly_Zq;
                                ZI    : in     SU7;
                                Start : in     Index_256)
       with             Global => null,
            Pre  => ZI in 4 .. 7 and then
                    Start <= 192 and then
                    (for all I in Index_256 range Start      .. Start + 63 => (F (I) in Mont_Range3)),
            Post => ((for all I in Index_256 range 0          .. Start - 1  => (F (I) = F'Old (I))) and
                     (for all I in Index_256 range Start      .. Start + 63 => (F (I) in Mont_Range5)) and
                     (for all I in Index_256 range Start + 64 .. 255        => (F (I) = F'Old (I))));

   procedure NTT_Inner34_Slice (F     : in out Poly_Zq;
                                ZI    : in     SU7;
                                Start : in     Index_256)
   is
      Z1 : constant Zeta_Range := Zeta_ExpC (ZI);
      Z2 : constant Zeta_Range := Zeta_ExpC (ZI * 2);
      Z3 : constant Zeta_Range := Zeta_ExpC (ZI * 2 + 1);
   begin
      for J in Index_256 range 0 .. 15 loop

         pragma Loop_Invariant
           (for all I in Index_256 range 0              .. Start - 1          => (F (I) = F'Loop_Entry (I)));
         pragma Loop_Invariant
           (for all I in Index_256 range Start          .. Start + J - 1      => (F (I) in Mont_Range5));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + J      .. Start + 15         => (F (I) = F'Loop_Entry (I)));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 16     .. Start + 16 + J - 1 => (F (I) in Mont_Range5));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 16 + J .. Start + 31         => (F (I) = F'Loop_Entry (I)));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 32     .. Start + 32 + J - 1 => (F (I) in Mont_Range5));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 32 + J .. Start + 47         => (F (I) = F'Loop_Entry (I)));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 48     .. Start + 48 + J - 1 => (F (I) in Mont_Range5));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 48 + J .. 255                => (F (I) = F'Loop_Entry (I)));

         declare
            C1 : constant Index_256 := J + Start;
            C2 : constant Index_256 := C1 + 16;
            C3 : constant Index_256 := C1 + 32;
            C4 : constant Index_256 := C1 + 48;
         begin
            declare
               T31  : constant Mont_Range := FQMul(Z1, F (C3));
               T31x : constant Mont_Range3 := F (C1);
               T32  : constant Mont_Range := FQMul(Z1, F (C4));
               T32x : constant Mont_Range3 := F (C2);
            begin
               F (C3) := T31x - T31;
               F (C1) := T31x + T31;
               F (C4) := T32x - T32;
               F (C2) := T32x + T32;
            end;

            declare
               T41  : constant Mont_Range := FQMul(Z2, F (C2));
               T41x : constant Mont_Range4 := F (C1);
               T42  : constant Mont_Range := FQMul(Z3, F (C4));
               T42x : constant Mont_Range4 := F (C3);
            begin
               F (C2) := T41x - T41;
               F (C1) := T41x + T41;
               F (C4) := T42x - T42;
               F (C3) := T42x + T42;
            end;

         end;

         --  Substitute J = 15 into the loop invariant and simplify yields the postcondition
      end loop;

   end NTT_Inner34_Slice;


   procedure NTT_Inner34 (F : in out Poly_Zq)
     with Global => null,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range3),
          Post => (for all K in Index_256 => F (K) in Mont_Range5);

   procedure NTT_Inner34 (F : in out Poly_Zq)
   is
   begin
      NTT_Inner34_Slice (F, 4, 0);
      NTT_Inner34_Slice (F, 5, 64);
      NTT_Inner34_Slice (F, 6, 128);
      NTT_Inner34_Slice (F, 7, 192);
   end NTT_Inner34;

   procedure NTT_Inner56_Slice (F     : in out Poly_Zq;
                                ZI    : in     SU7;
                                Start : in     Index_256)
       with Global => null,
            Pre  => ZI in 16 .. 31 and then
                    Start <= 240 and then
                    (for all I in Index_256 range Start      .. Start + 15 => (F (I) in Mont_Range5)),
            Post => ((for all I in Index_256 range 0          .. Start - 1  => (F (I) = F'Old (I))) and
                     (for all I in Index_256 range Start      .. Start + 15 => (F (I) in Mont_Range7)) and
                     (for all I in Index_256 range Start + 16 .. 255        => (F (I) = F'Old (I))));

   procedure NTT_Inner56_Slice (F     : in out Poly_Zq;
                                ZI    : in     SU7;
                                Start : in     Index_256)
   is
      Z1 : constant Zeta_Range := Zeta_ExpC (ZI);
      Z2 : constant Zeta_Range := Zeta_ExpC (ZI * 2);
      Z3 : constant Zeta_Range := Zeta_ExpC (ZI * 2 + 1);
   begin
      for J in Index_256 range 0 .. 3 loop
         pragma Loop_Invariant
           (for all I in Index_256 range 0              .. Start - 1          => (F (I) = F'Loop_Entry (I)));
         pragma Loop_Invariant
           (for all I in Index_256 range Start          .. Start + J - 1      => (F (I) in Mont_Range7));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + J      .. Start + 3          => (F (I) = F'Loop_Entry (I)));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 4      .. Start + 4 + J - 1  => (F (I) in Mont_Range7));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 4 + J  .. Start + 7          => (F (I) = F'Loop_Entry (I)));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 8      .. Start + 8 + J - 1  => (F (I) in Mont_Range7));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 8 + J  .. Start + 11         => (F (I) = F'Loop_Entry (I)));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 12     .. Start + 12 + J - 1 => (F (I) in Mont_Range7));
         pragma Loop_Invariant
           (for all I in Index_256 range Start + 12 + J .. 255                => (F (I) = F'Loop_Entry (I)));

         declare
            C1 : constant Index_256 := J + Start;
            C2 : constant Index_256 := C1 + 4;
            C3 : constant Index_256 := C1 + 8;
            C4 : constant Index_256 := C1 + 12;
         begin
            declare
               T51  : constant Mont_Range  := FQMul(Z1, F (C3));
               T51x : constant Mont_Range5 := F (C1);
               T52  : constant Mont_Range  := FQMul(Z1, F (C4));
               T52x : constant Mont_Range5 := F (C2);
            begin
               F (C3) := T51x - T51;
               F (C1) := T51x + T51;
               F (C4) := T52x - T52;
               F (C2) := T52x + T52;
            end;

            declare
               T61  : constant Mont_Range := FQMul(Z2, F (C2));
               T61x : constant Mont_Range6 := F (C1);
               T62  : constant Mont_Range := FQMul(Z3, F (C4));
               T62x : constant Mont_Range6 := F (C3);
            begin
               F (C2) := T61x - T61;
               F (C1) := T61x + T61;
               F (C4) := T62x - T62;
               F (C3) := T62x + T62;
            end;

         end;

         --  Substitute J = 3 into the loop invariant and simplify yields the postcondition
      end loop;

   end NTT_Inner56_Slice;





   procedure NTT_Inner56 (F : in out Poly_Zq)
       with Global => null,
            Pre  => (for all K in Index_256 => F (K) in Mont_Range5),
            Post => (for all K in Index_256 => F (K) in Mont_Range7);

   procedure NTT_Inner56 (F : in out Poly_Zq)
   is
   begin
      NTT_Inner56_Slice (F, 16, 0);
      NTT_Inner56_Slice (F, 17, 16);
      NTT_Inner56_Slice (F, 18, 32);
      NTT_Inner56_Slice (F, 19, 48);
      NTT_Inner56_Slice (F, 20, 64);
      NTT_Inner56_Slice (F, 21, 80);
      NTT_Inner56_Slice (F, 22, 96);
      NTT_Inner56_Slice (F, 23, 112);
      NTT_Inner56_Slice (F, 24, 128);
      NTT_Inner56_Slice (F, 25, 144);
      NTT_Inner56_Slice (F, 26, 160);
      NTT_Inner56_Slice (F, 27, 176);
      NTT_Inner56_Slice (F, 28, 192);
      NTT_Inner56_Slice (F, 29, 208);
      NTT_Inner56_Slice (F, 30, 224);
      NTT_Inner56_Slice (F, 31, 240);
   end NTT_Inner56;


   procedure NTT_Inner7_Slice (F     : in out Poly_Zq;
                               ZI    : in     SU7;
                               Start : in     Index_256)
       with Global => null,
            Pre  => ZI in 64 .. 127 and then
                    Start <= 252 and then
                    (for all I in Index_256 range Start      .. Start + 3 => (F (I) in Mont_Range7)),
            Post => ((for all I in Index_256 range 0         .. Start - 1 => (F (I) = F'Old (I))) and
                     (for all I in Index_256 range Start     .. Start + 3 => (F (I) in Mont_Range8)) and
                     (for all I in Index_256 range Start + 4 .. 255       => (F (I) = F'Old (I))));

   procedure NTT_Inner7_Slice (F     : in out Poly_Zq;
                               ZI    : in     SU7;
                               Start : in     Index_256)
   is
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
   begin
      for J in Index_256 range Start .. Start + 1 loop
         pragma Loop_Invariant
            (for all I in Index_256 range 0          .. Start - 1 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            (for all I in Index_256 range Start      .. J - 1     => F (I) in Mont_Range8);
         pragma Loop_Invariant
            (for all I in Index_256 range J         .. Start + 1 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            (for all I in Index_256 range Start + 2 .. J + 1     => F (I) in Mont_Range8);
         pragma Loop_Invariant
            (for all I in Index_256 range J + 2     .. 255       => F (I) = F'Loop_Entry (I));

         declare
            J2  : constant Index_256 := J + 2;
            FJ2 : constant I16 := F (J2);
            T   : constant Mont_Range := FQMul (Zeta, FJ2);
            FJ  : constant I16 := F (J);
         begin
            F (J + 2) := FJ - T;
            F (J)     := FJ + T;
         end;

      end loop;
   end NTT_Inner7_Slice;



   procedure NTT_Inner7 (F : in out Poly_Zq)
       with Global => null,
            Pre  => (for all K in Index_256 => F (K) in Mont_Range7),
            Post => (for all K in Index_256 => F (K) in Mont_Range8);

   procedure NTT_Inner7 (F : in out Poly_Zq)
   is
   begin
      for J in I32 range 0 .. 63 loop
         pragma Loop_Invariant (for all I in Index_256 range 0      .. J * 4 - 1 => F (I) in Mont_Range8);
         pragma Loop_Invariant (for all I in Index_256 range J * 4  .. 255       => F (I) = F'Loop_Entry (I));

         NTT_Inner7_Slice (F     => F,
                           ZI    => 64 + Byte (J),
                           Start => J * 4);
      end loop;
   end NTT_Inner7;

   procedure NTT (F : in out Poly_Zq)
   is
   begin
      NTT_Inner12 (F);
      NTT_Inner34 (F);
      NTT_Inner56 (F);
      NTT_Inner7  (F);

      for K in F'Range loop
         pragma Loop_Invariant (for all I in Index_256 range 0 .. K - 1 => F (I) in BRange);
         F (K) := Barrett_Reduce (F (K));
      end loop;

      pragma Assert (for all I in F'Range => F (I) in BRange);

   end NTT;

end RMerge2;

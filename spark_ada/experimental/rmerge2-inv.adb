package body RMerge2.Inv
  with SPARK_Mode => On
is
   procedure NTT_Inv_Inner (F     : in out Poly_Zq;
                            ZI    : in     SU7;
                            Start : in     Index_256;
                            Len   : in     I32)
     with No_Inline,
          Global => null,
          Pre    => Len >= 0 and then
                    Len <= 128 and then
                    Start <= 252 and then
                    Start + 2 * Len <= 256 and then
                    (for all K in Index_256 => F (K) in Mont_Range2),
          Post   => (for all K in Index_256 => F (K) in Mont_Range2);

   procedure NTT_Inv_Inner (F     : in out Poly_Zq;
                            ZI    : in     SU7;
                            Start : in     Index_256;
                            Len   : in     I32)
   is
      T : I16;
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
   begin
      for J in Index_256 range Start .. Start + (Len - 1) loop
         T := F (J);
         F (J) := Barrett_Reduce (T + F (J + Len));
         F (J + Len) := FQMul (Zeta, F (J + Len) - T);

         pragma Loop_Invariant
            -- Elements 0 .. Start - 1 are unchanged
           (for all I in Index_256 range 0 .. Start - 1 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            -- Elements Start through J are updated and in BRange
           (for all I in Index_256 range Start .. J => F (I) in BRange);
         pragma Loop_Invariant
            -- Elements J + 1 .. Start + Len - 1 are unchanged
           (for all I in Index_256 range J + 1 .. Start + Len - 1 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            --  Elements Start + Len through J + Len are updated and in Mont_Range
           (for all I in Index_256 range Start + Len .. J + Len => (F (I) in Mont_Range));
         pragma Loop_Invariant
            --  Elements from J + Len + 1 .. 255 are unchanged
           (for all I in Index_256 range J + Len + 1 .. 255 => F (I) = F'Loop_Entry (I));

      end loop;

      --  (J = Start + Len - 1) => Postcondition
   end NTT_Inv_Inner;

      --  --  J = Start + Len - 1
      --  pragma Assert
      --    (for all I in Index_256 range 0 .. Start - 1 => F (I) in Mont_Range2);
      --  pragma Assert
      --    (for all I in Index_256 range Start .. Start + Len - 1 => F (I) in BRange);
      --  pragma Assert
      --    (for all I in Index_256 range Start + Len .. Start + Len - 1 + Len => (F (I) in Mont_Range));
      --  pragma Assert
      --    (for all I in Index_256 range Start + Len - 1 + Len + 1 .. 255 => F (I) in Mont_Range2);

      --  --  Merge ranges of the middle two, and note that Mont_Range is wider than BRange
      --  pragma Assert
      --    (for all I in Index_256 range     0           .. Start - 1           => F (I) in Mont_Range2);
      --  pragma Assert
      --    (for all I in Index_256 range Start           .. Start + 2 * Len - 1 => F (I) in Mont_Range);
      --  pragma Assert
      --    (for all I in Index_256 range Start + 2 * Len .. 255                 => F (I) in Mont_Range2);

      --  pragma Assert
      --    (for all I in Index_256  => F (I) in Mont_Range2);


   --  ================
   --  Layer 1 Len=128
   --  ================

   procedure NTT_Inv_Inner1 (F     : in out Poly_Zq)
     with Global => null,
          Pre    => (for all K in Index_256 => F (K) in Mont_Range2),
          Post   => (for all K in Index_256 => F (K) in Mont_Range2);

   procedure NTT_Inv_Inner1 (F     : in out Poly_Zq)
   is
      T : I16;
      Zeta : constant Zeta_Range := Zeta_ExpC (1);
   begin
      for J in Index_256 range 0 .. 127 loop
         T           := F (J);
         F (J)       := Barrett_Reduce (F (J + 128) + T);
         F (J + 128) :=    FQMul (Zeta, F (J + 128) - T);

         pragma Loop_Invariant
            -- Elements Start through J are updated and in BRange
           (for all I in Index_256 range 0 .. J => F (I) in BRange);
         pragma Loop_Invariant
            -- Elements J + 1 .. Start + 128 - 1 are unchanged
           (for all I in Index_256 range J + 1 .. 127 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            --  Elements Start + 128 through J + 128 are updated and in Mont_Range
           (for all I in Index_256 range 128 .. J + 128 => (F (I) in Mont_Range));
         pragma Loop_Invariant
            --  Elements from J + 128 + 1 .. 255 are unchanged
           (for all I in Index_256 range J + 129 .. 255 => F (I) = F'Loop_Entry (I));

      end loop;

      --  (J = 127) => Postcondition
   end NTT_Inv_Inner1;

   procedure Layer1 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range2),
          Post => (for all K in Index_256 => F (K) in Mont_Range2);

   procedure Layer1 (F : in out Poly_Zq)
   is
   begin
      NTT_Inv_Inner1 (F);
   end Layer1;


   --  ================
   --  Layer 2 Len=64
   --  ================

   procedure NTT_Inv_Inner2 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
     with Global => null,
          Pre    => Start <= 128 and then
                    (for all K in Index_256 => F (K) in Mont_Range2),
          Post   => (for all K in Index_256 => F (K) in Mont_Range2);

   procedure NTT_Inv_Inner2 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
   is
      T : I16;
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
   begin
      for J in Index_256 range Start .. Start + 63 loop
         T          := F (J);
         F (J)      := Barrett_Reduce (F (J + 64) + T);
         F (J + 64) :=    FQMul (Zeta, F (J + 64) - T);

         pragma Loop_Invariant
            -- Elements 0 .. Start - 1 are unchanged
           (for all I in Index_256 range 0 .. Start - 1 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            -- Elements Start through J are updated and in BRange
           (for all I in Index_256 range Start .. J => F (I) in BRange);
         pragma Loop_Invariant
            -- Elements J + 1 .. Start + 64 - 1 are unchanged
           (for all I in Index_256 range J + 1 .. Start + 63 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            --  Elements Start + 64 through J + 64 are updated and in Mont_Range
           (for all I in Index_256 range Start + 64 .. J + 64 => (F (I) in Mont_Range));
         pragma Loop_Invariant
            --  Elements from J + 64 + 1 .. 255 are unchanged
           (for all I in Index_256 range J + 65 .. 255 => F (I) = F'Loop_Entry (I));

      end loop;

      --  (J = Start + 63) => Postcondition
   end NTT_Inv_Inner2;

   procedure Layer2 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range2),
          Post => (for all K in Index_256 => F (K) in Mont_Range2);

   procedure Layer2 (F : in out Poly_Zq)
   is
   begin
      NTT_Inv_Inner2 (F, 3, 0);
      NTT_Inv_Inner2 (F, 2, 128);
   end Layer2;

   --  ================
   --  Layer 3 Len=32
   --  ================

   procedure NTT_Inv_Inner3 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
     with Global => null,
          Pre    => Start <= 192 and then
                    (for all K in Index_256 => F (K) in Mont_Range2),
          Post   => (for all K in Index_256 => F (K) in Mont_Range2);

   procedure NTT_Inv_Inner3 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
   is
      T : I16;
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
   begin
      for J in Index_256 range Start .. Start + (32 - 1) loop
         T          := F (J);
         F (J)      := Barrett_Reduce (F (J + 32) + T);
         F (J + 32) :=    FQMul (Zeta, F (J + 32) - T);

         pragma Loop_Invariant
            -- Elements 0 .. Start - 1 are unchanged
           (for all I in Index_256 range 0 .. Start - 1 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            -- Elements Start through J are updated and in BRange
           (for all I in Index_256 range Start .. J => F (I) in BRange);
         pragma Loop_Invariant
            -- Elements J + 1 .. Start + 32 - 1 are unchanged
           (for all I in Index_256 range J + 1 .. Start + 31 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            --  Elements Start + 32 through J + 32 are updated and in Mont_Range
           (for all I in Index_256 range Start + 32 .. J + 32 => (F (I) in Mont_Range));
         pragma Loop_Invariant
            --  Elements from J + 33 .. 255 are unchanged
           (for all I in Index_256 range J + 33 .. 255 => F (I) = F'Loop_Entry (I));

      end loop;
      --  (J = Start + 32 - 1) => Postcondition
   end NTT_Inv_Inner3;

   procedure Layer3 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range2),
          Post => (for all K in Index_256 => F (K) in Mont_Range2);

   procedure Layer3 (F : in out Poly_Zq)
   is
   begin
      for J in I32 range 0 .. 3 loop
         NTT_Inv_Inner3 (F, 7 - J, J * 64);
         pragma Loop_Invariant (for all K in Index_256 => F (K) in Mont_Range2);
      end loop;
   end Layer3;



   --  ================
   --  Layer 4 Len=16
   --  ================

   procedure NTT_Inv_Inner4 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
     with Global => null,
          Pre    => Start <= 224 and then
                    (for all K in Index_256 => F (K) in Mont_Range2),
          Post   => (for all K in Index_256 => F (K) in Mont_Range2);

   procedure NTT_Inv_Inner4 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
   is
      T : I16;
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
   begin
      for J in Index_256 range Start .. Start + 15 loop
         T          := F (J);
         F (J)      := Barrett_Reduce (F (J + 16) + T);
         F (J + 16) := FQMul    (Zeta, F (J + 16) - T);

         pragma Loop_Invariant
            -- Elements 0 .. Start - 1 are unchanged
           (for all I in Index_256 range 0 .. Start - 1 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            -- Elements Start through J are updated and in BRange
           (for all I in Index_256 range Start .. J => F (I) in BRange);
         pragma Loop_Invariant
            -- Elements J + 1 .. Start + 16 - 1 are unchanged
           (for all I in Index_256 range J + 1 .. Start + 15 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            --  Elements Start + 16 through J + 16 are updated and in Mont_Range
           (for all I in Index_256 range Start + 16 .. J + 16 => (F (I) in Mont_Range));
         pragma Loop_Invariant
            --  Elements from J + 16 + 1 .. 255 are unchanged
           (for all I in Index_256 range J + 17 .. 255 => F (I) = F'Loop_Entry (I));

      end loop;

      --  (J = Start + 15) => Postcondition
   end NTT_Inv_Inner4;

   procedure Layer4 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range2),
          Post => (for all K in Index_256 => F (K) in Mont_Range2);

   procedure Layer4 (F : in out Poly_Zq)
   is
   begin
      for J in I32 range 0 .. 7 loop
         NTT_Inv_Inner4 (F, 15 - J, J * 32);
         pragma Loop_Invariant (for all K in Index_256 => F (K) in Mont_Range2);
      end loop;
   end Layer4;

   --  ================
   --  Layer 5 Len=8
   --  ================
   procedure NTT_Inv_Inner5 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
     with Global => null,
          Pre    => ZI in 16 .. 31 and then
                    Start <= 240 and then
                    Start mod 16 = 0 and then
                    (F (Start)      in Mont_Range4 and
                     F (Start + 1)  in Mont_Range4 and
                     F (Start + 2)  in Mont_Range2 and
                     F (Start + 3)  in Mont_Range2 and
                     F (Start + 4)  in Mont_Range  and
                     F (Start + 5)  in Mont_Range  and
                     F (Start + 6)  in Mont_Range  and
                     F (Start + 7)  in Mont_Range  and
                     F (Start + 8)  in Mont_Range4 and
                     F (Start + 9)  in Mont_Range4 and
                     F (Start + 10) in Mont_Range2 and
                     F (Start + 11) in Mont_Range2 and
                     F (Start + 12) in Mont_Range  and
                     F (Start + 13) in Mont_Range  and
                     F (Start + 14) in Mont_Range  and
                     F (Start + 15) in Mont_Range),
          Post   => (for all K in Index_256 range 0 .. Start - 1 => F (K) = F'Old (K)) and
                     F (Start)      in Mont_Range8 and
                     F (Start + 1)  in Mont_Range8 and
                     F (Start + 2)  in Mont_Range4 and
                     F (Start + 3)  in Mont_Range4 and
                     F (Start + 4)  in Mont_Range2 and
                     F (Start + 5)  in Mont_Range2 and
                     F (Start + 6)  in Mont_Range2 and
                     F (Start + 7)  in Mont_Range2 and
                     F (Start + 8)  in Mont_Range  and
                     F (Start + 9)  in Mont_Range  and
                     F (Start + 10) in Mont_Range  and
                     F (Start + 11) in Mont_Range  and
                     F (Start + 12) in Mont_Range  and
                     F (Start + 13) in Mont_Range  and
                     F (Start + 14) in Mont_Range  and
                     F (Start + 15) in Mont_Range  and
                    (for all K in Index_256 range Start + 16 .. 255 => F (K) = F'Old (K));

   procedure NTT_Inv_Inner5 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
   is
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
      CI0  : constant Index_256 := Start;
      CI1  : constant Index_256 := CI0 + 1;
      CI2  : constant Index_256 := CI0 + 2;
      CI3  : constant Index_256 := CI0 + 3;
      CI4  : constant Index_256 := CI0 + 4;
      CI5  : constant Index_256 := CI0 + 5;
      CI6  : constant Index_256 := CI0 + 6;
      CI7  : constant Index_256 := CI0 + 7;
      CI8  : constant Index_256 := CI0 + 8;
      CI9  : constant Index_256 := CI0 + 9;
      CI10 : constant Index_256 := CI0 + 10;
      CI11 : constant Index_256 := CI0 + 11;
      CI12 : constant Index_256 := CI0 + 12;
      CI13 : constant Index_256 := CI0 + 13;
      CI14 : constant Index_256 := CI0 + 14;
      CI15 : constant Index_256 := CI0 + 15;
      C0  : constant I16 := F (CI0);
      C1  : constant I16 := F (CI1);
      C2  : constant I16 := F (CI2);
      C3  : constant I16 := F (CI3);
      C4  : constant I16 := F (CI4);
      C5  : constant I16 := F (CI5);
      C6  : constant I16 := F (CI6);
      C7  : constant I16 := F (CI7);
      C8  : constant I16 := F (CI8);
      C9  : constant I16 := F (CI9);
      C10 : constant I16 := F (CI10);
      C11 : constant I16 := F (CI11);
      C12 : constant I16 := F (CI12);
      C13 : constant I16 := F (CI13);
      C14 : constant I16 := F (CI14);
      C15 : constant I16 := F (CI15);
   begin
      F (CI0) := C0 + C8; --  Defer reduction
      F (CI8) := FQMul (Zeta, C8 - C0);

      F (CI1) := C1 + C9; --  Defer reduction
      F (CI9) := FQMul (Zeta, C9 - C1);

      F (CI2) := C2 + C10; --  Defer reduction
      F (CI10) := FQMul (Zeta, C10 - C2);

      F (CI3) := C3 + C11; --  Defer reduction
      F (CI11) := FQMul (Zeta, C11 - C3);

      F (CI4) := C4 + C12; --  Defer reduction
      F (CI12) := FQMul (Zeta, C12 - C4);

      F (CI5) := C5 + C13; --  Defer reduction
      F (CI13) := FQMul (Zeta, C13 - C5);

      F (CI6) := C6 + C14; --  Defer reduction
      F (CI14) := FQMul (Zeta, C14 - C6);

      F (CI7) := C7 + C15; --  Defer reduction
      F (CI15) := FQMul (Zeta, C15 - C7);
   end NTT_Inv_Inner5;

   procedure Layer5 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in I32 range 0 .. 15 =>
                     F (K * 16)      in Mont_Range4 and
                     F (K * 16 + 1)  in Mont_Range4 and
                     F (K * 16 + 2)  in Mont_Range2 and
                     F (K * 16 + 3)  in Mont_Range2 and
                     F (K * 16 + 4)  in Mont_Range  and
                     F (K * 16 + 5)  in Mont_Range  and
                     F (K * 16 + 6)  in Mont_Range  and
                     F (K * 16 + 7)  in Mont_Range  and
                     F (K * 16 + 8)  in Mont_Range4 and
                     F (K * 16 + 9)  in Mont_Range4 and
                     F (K * 16 + 10) in Mont_Range2 and
                     F (K * 16 + 11) in Mont_Range2 and
                     F (K * 16 + 12) in Mont_Range  and
                     F (K * 16 + 13) in Mont_Range  and
                     F (K * 16 + 14) in Mont_Range  and
                     F (K * 16 + 15) in Mont_Range),
          Post => (for all K in I32 range 0 .. 15 =>
                     F (K * 16)      in Mont_Range8 and
                     F (K * 16 + 1)  in Mont_Range8 and
                     F (K * 16 + 2)  in Mont_Range4 and
                     F (K * 16 + 3)  in Mont_Range4 and
                     F (K * 16 + 4)  in Mont_Range2 and
                     F (K * 16 + 5)  in Mont_Range2 and
                     F (K * 16 + 6)  in Mont_Range2 and
                     F (K * 16 + 7)  in Mont_Range2 and
                     F (K * 16 + 8)  in Mont_Range  and
                     F (K * 16 + 9)  in Mont_Range  and
                     F (K * 16 + 10) in Mont_Range  and
                     F (K * 16 + 11) in Mont_Range  and
                     F (K * 16 + 12) in Mont_Range  and
                     F (K * 16 + 13) in Mont_Range  and
                     F (K * 16 + 14) in Mont_Range  and
                     F (K * 16 + 15) in Mont_Range);

   procedure Layer5 (F : in out Poly_Zq)
   is
   begin
      for J in I32 range 0 .. 15 loop
         NTT_Inv_Inner5 (F, 31 - J, J * 16);

         --  Elements modified so far increase in magnitude as follows:
         pragma Loop_Invariant (for all K in I32 range 0 .. J =>
                                  F (K * 16)      in Mont_Range8 and
                                  F (K * 16 + 1)  in Mont_Range8 and
                                  F (K * 16 + 2)  in Mont_Range4 and
                                  F (K * 16 + 3)  in Mont_Range4 and
                                  F (K * 16 + 4)  in Mont_Range2 and
                                  F (K * 16 + 5)  in Mont_Range2 and
                                  F (K * 16 + 6)  in Mont_Range2 and
                                  F (K * 16 + 7)  in Mont_Range2 and
                                  F (K * 16 + 8)  in Mont_Range  and
                                  F (K * 16 + 9)  in Mont_Range  and
                                  F (K * 16 + 10) in Mont_Range  and
                                  F (K * 16 + 11) in Mont_Range  and
                                  F (K * 16 + 12) in Mont_Range  and
                                  F (K * 16 + 13) in Mont_Range  and
                                  F (K * 16 + 14) in Mont_Range  and
                                  F (K * 16 + 15) in Mont_Range);

         --  Unmodified element retain their initial values...
         pragma Loop_Invariant (for all K in I32 range (J + 1) * 16 .. 255 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in I32 range J + 1 .. 15 =>
                                  F (K * 16)      = F'Loop_Entry (K * 16)      and
                                  F (K * 16 + 1)  = F'Loop_Entry (K * 16 + 1)  and
                                  F (K * 16 + 2)  = F'Loop_Entry (K * 16 + 2)  and
                                  F (K * 16 + 3)  = F'Loop_Entry (K * 16 + 3)  and
                                  F (K * 16 + 4)  = F'Loop_Entry (K * 16 + 4)  and
                                  F (K * 16 + 5)  = F'Loop_Entry (K * 16 + 5)  and
                                  F (K * 16 + 6)  = F'Loop_Entry (K * 16 + 6)  and
                                  F (K * 16 + 7)  = F'Loop_Entry (K * 16 + 7)  and
                                  F (K * 16 + 8)  = F'Loop_Entry (K * 16 + 8)  and
                                  F (K * 16 + 9)  = F'Loop_Entry (K * 16 + 9)  and
                                  F (K * 16 + 10) = F'Loop_Entry (K * 16 + 10) and
                                  F (K * 16 + 11) = F'Loop_Entry (K * 16 + 11) and
                                  F (K * 16 + 12) = F'Loop_Entry (K * 16 + 12) and
                                  F (K * 16 + 13) = F'Loop_Entry (K * 16 + 13) and
                                  F (K * 16 + 14) = F'Loop_Entry (K * 16 + 14) and
                                  F (K * 16 + 15) = F'Loop_Entry (K * 16 + 15));

         --  ...and therefore retain the ranges specified in the pre-condition. This is
         --  sufficient to meet the pre-condition of the _next_ call to NTT_Inv_Inner6
         pragma Loop_Invariant (for all K in I32 range J + 1 .. 15 =>
                                  F (K * 16)      in Mont_Range4 and
                                  F (K * 16 + 1)  in Mont_Range4 and
                                  F (K * 16 + 2)  in Mont_Range2 and
                                  F (K * 16 + 3)  in Mont_Range2 and
                                  F (K * 16 + 4)  in Mont_Range  and
                                  F (K * 16 + 5)  in Mont_Range  and
                                  F (K * 16 + 6)  in Mont_Range  and
                                  F (K * 16 + 7)  in Mont_Range  and
                                  F (K * 16 + 8)  in Mont_Range4 and
                                  F (K * 16 + 9)  in Mont_Range4 and
                                  F (K * 16 + 10) in Mont_Range2 and
                                  F (K * 16 + 11) in Mont_Range2 and
                                  F (K * 16 + 12) in Mont_Range  and
                                  F (K * 16 + 13) in Mont_Range  and
                                  F (K * 16 + 14) in Mont_Range  and
                                  F (K * 16 + 15) in Mont_Range);

      end loop;
   end Layer5;


   --  ================
   --  Layer 6
   --  ================
   procedure NTT_Inv_Inner6 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
     with Global => null,
          Pre    => ZI in 32 .. 63 and then
                    Start <= 248 and then
                    Start mod 8 = 0 and then
                    (F (Start)     in Mont_Range2 and
                     F (Start + 1) in Mont_Range2 and
                     F (Start + 2) in Mont_Range and
                     F (Start + 3) in Mont_Range and
                     F (Start + 4) in Mont_Range2 and
                     F (Start + 5) in Mont_Range2 and
                     F (Start + 6) in Mont_Range and
                     F (Start + 7) in Mont_Range),
          Post   => (for all K in Index_256 range 0 .. Start - 1 => F (K) = F'Old (K)) and
                     F (Start)     in Mont_Range4 and
                     F (Start + 1) in Mont_Range4 and
                     F (Start + 2) in Mont_Range2 and
                     F (Start + 3) in Mont_Range2 and
                     F (Start + 4) in Mont_Range and
                     F (Start + 5) in Mont_Range and
                     F (Start + 6) in Mont_Range and
                     F (Start + 7) in Mont_Range and
                    (for all K in Index_256 range Start + 8 .. 255 => F (K) = F'Old (K));


   procedure NTT_Inv_Inner6 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
   is
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
      CI0 : constant Index_256 := Start;
      CI1 : constant Index_256 := CI0 + 1;
      CI2 : constant Index_256 := CI0 + 2;
      CI3 : constant Index_256 := CI0 + 3;
      CI4 : constant Index_256 := CI0 + 4;
      CI5 : constant Index_256 := CI0 + 5;
      CI6 : constant Index_256 := CI0 + 6;
      CI7 : constant Index_256 := CI0 + 7;
      C0  : constant I16 := F (CI0);
      C1  : constant I16 := F (CI1);
      C2  : constant I16 := F (CI2);
      C3  : constant I16 := F (CI3);
      C4  : constant I16 := F (CI4);
      C5  : constant I16 := F (CI5);
      C6  : constant I16 := F (CI6);
      C7  : constant I16 := F (CI7);
   begin
      F (CI0) := C0 + C4; --  Defer reduction
      F (CI4) := FQMul (Zeta, C4 - C0);

      F (CI1) := C1 + C5; --  Defer reduction
      F (CI5) := FQMul (Zeta, C5 - C1);

      F (CI2) := C2 + C6; --  Defer reduction
      F (CI6) := FQMul (Zeta, C6 - C2);

      F (CI3) := C3 + C7; --  Defer reduction
      F (CI7) := FQMul (Zeta, C7 - C3);
   end NTT_Inv_Inner6;

   procedure Layer6 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in I32 range 0 .. 31 =>
                     F (K * 8)     in Mont_Range2 and
                     F (K * 8 + 1) in Mont_Range2 and
                     F (K * 8 + 2) in Mont_Range  and
                     F (K * 8 + 3) in Mont_Range  and
                     F (K * 8 + 4) in Mont_Range2 and
                     F (K * 8 + 5) in Mont_Range2 and
                     F (K * 8 + 6) in Mont_Range  and
                     F (K * 8 + 7) in Mont_Range),
          Post => (for all K in I32 range 0 .. 31 =>
                     F (K * 8)     in Mont_Range4 and
                     F (K * 8 + 1) in Mont_Range4 and
                     F (K * 8 + 2) in Mont_Range2 and
                     F (K * 8 + 3) in Mont_Range2 and
                     F (K * 8 + 4) in Mont_Range  and
                     F (K * 8 + 5) in Mont_Range  and
                     F (K * 8 + 6) in Mont_Range  and
                     F (K * 8 + 7) in Mont_Range);


   procedure Layer6 (F : in out Poly_Zq)
   is
   begin
      for J in I32 range 0 .. 31 loop
         NTT_Inv_Inner6 (F, 63 - J, J * 8);

         --  Elements modified so far increase in magnitude as follows:
         pragma Loop_Invariant (for all K in I32 range 0 .. J =>
                                  F (K * 8)     in Mont_Range4 and
                                  F (K * 8 + 1) in Mont_Range4 and
                                  F (K * 8 + 2) in Mont_Range2 and
                                  F (K * 8 + 3) in Mont_Range2 and
                                  F (K * 8 + 4) in Mont_Range  and
                                  F (K * 8 + 5) in Mont_Range  and
                                  F (K * 8 + 6) in Mont_Range  and
                                  F (K * 8 + 7) in Mont_Range);

         --  Unmodified element retain their initial values...
         pragma Loop_Invariant (for all K in I32 range (J + 1) * 8 .. 255 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in I32 range J + 1 .. 31 =>
                                  F (K * 8)     = F'Loop_Entry (K * 8)     and
                                  F (K * 8 + 1) = F'Loop_Entry (K * 8 + 1) and
                                  F (K * 8 + 2) = F'Loop_Entry (K * 8 + 2) and
                                  F (K * 8 + 3) = F'Loop_Entry (K * 8 + 3) and
                                  F (K * 8 + 4) = F'Loop_Entry (K * 8 + 4) and
                                  F (K * 8 + 5) = F'Loop_Entry (K * 8 + 5) and
                                  F (K * 8 + 6) = F'Loop_Entry (K * 8 + 6) and
                                  F (K * 8 + 7) = F'Loop_Entry (K * 8 + 7));

         --  ...and therefore retain the ranges specified in the pre-condition. This is
         --  sufficient to meet the pre-condition of the _next_ call to NTT_Inv_Inner6
         pragma Loop_Invariant (for all K in I32 range J + 1 .. 31 =>
                                  F (K * 8)     in Mont_Range2 and
                                  F (K * 8 + 1) in Mont_Range2 and
                                  F (K * 8 + 2) in Mont_Range  and
                                  F (K * 8 + 3) in Mont_Range  and
                                  F (K * 8 + 4) in Mont_Range2 and
                                  F (K * 8 + 5) in Mont_Range2 and
                                  F (K * 8 + 6) in Mont_Range  and
                                  F (K * 8 + 7) in Mont_Range);
      end loop;
   end Layer6;

   --  ================
   --  Layer 7
   --  ================

   procedure NTT_Inv_Inner7 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
     with Global => null,
          Pre  => ZI in 64 .. 127 and then
                  Start <= 252 and then
                  (for all I in Index_256 range Start .. Start + 3 => (F (I) in Mont_Range)),
          Post => ((for all I in Index_256 range 0         .. Start - 1 => (F (I) = F'Old (I))) and
                   (for all I in Index_256 range Start     .. Start + 1 => (F (I) in Mont_Range2)) and
                   (for all I in Index_256 range Start + 2 .. Start + 3 => (F (I) in Mont_Range)) and
                   (for all I in Index_256 range Start + 4 .. 255       => (F (I) = F'Old (I))));

   procedure NTT_Inv_Inner7 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
   is
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
      CI0 : constant Index_256 := Start;
      CI1 : constant Index_256 := CI0 + 1;
      CI2 : constant Index_256 := CI0 + 2;
      CI3 : constant Index_256 := CI0 + 3;
      C0  : constant I16 := F (CI0);
      C1  : constant I16 := F (CI1);
      C2  : constant I16 := F (CI2);
      C3  : constant I16 := F (CI3);
   begin
      F (CI0) := C0 + C2; --  Defer reduction,
      F (CI2) := FQMul (Zeta, (C2 - C0));

      F (CI1) := C1 + C3; --  Defer reduction
      F (CI3) := FQMul (Zeta, (C3 - C1));
   end NTT_Inv_Inner7;


   procedure Layer7 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range),
          Post => ((for all K in I32 range 0 .. 63 => F (K * 4)     in Mont_Range2) and
                   (for all K in I32 range 0 .. 63 => F (K * 4 + 1) in Mont_Range2) and
                   (for all K in I32 range 0 .. 63 => F (K * 4 + 2) in Mont_Range) and
                   (for all K in I32 range 0 .. 63 => F (K * 4 + 3) in Mont_Range));

   procedure Layer7 (F : in out Poly_Zq)
   is
   begin
      for J in I32 range 0 .. 63 loop
         NTT_Inv_Inner7 (F, 127 - J, J * 4);
         pragma Loop_Invariant (for all K in I32 range 0 .. J => F (K * 4)     in Mont_Range2);
         pragma Loop_Invariant (for all K in I32 range 0 .. J => F (K * 4 + 1) in Mont_Range2);
         pragma Loop_Invariant (for all K in I32 range 0 .. J => F (K * 4 + 2) in Mont_Range);
         pragma Loop_Invariant (for all K in I32 range 0 .. J => F (K * 4 + 3) in Mont_Range);
         pragma Loop_Invariant (for all K in I32 range J * 4 + 4 .. 255 => F (K) in Mont_Range);
      end loop;
   end Layer7;

   --  Optimized implementation
   procedure INTTnew (F : in out Poly_Zq)
   is
      pragma Annotate (GNATprove, Intentional, "postcondition might fail", "Quantifier merging");
      procedure Layer7_to_6_Lemma (F : in Poly_Zq)
        with Ghost,
             Global => null,
             Pre    => ((for all K in I32 range 0 .. 63 => F (K * 4)     in Mont_Range2) and
                        (for all K in I32 range 0 .. 63 => F (K * 4 + 1) in Mont_Range2) and
                        (for all K in I32 range 0 .. 63 => F (K * 4 + 2) in Mont_Range) and
                        (for all K in I32 range 0 .. 63 => F (K * 4 + 3) in Mont_Range)),
             Post   => ((for all K in I32 range 0 .. 31 => F (K * 8)     in Mont_Range2) and
                        (for all K in I32 range 0 .. 31 => F (K * 8 + 1) in Mont_Range2) and
                        (for all K in I32 range 0 .. 31 => F (K * 8 + 2) in Mont_Range) and
                        (for all K in I32 range 0 .. 31 => F (K * 8 + 3) in Mont_Range) and
                        (for all K in I32 range 0 .. 31 => F (K * 8 + 4) in Mont_Range2) and
                        (for all K in I32 range 0 .. 31 => F (K * 8 + 5) in Mont_Range2) and
                        (for all K in I32 range 0 .. 31 => F (K * 8 + 6) in Mont_Range) and
                        (for all K in I32 range 0 .. 31 => F (K * 8 + 7) in Mont_Range));

      procedure Layer7_to_6_Lemma (F : in Poly_Zq) is null;

   begin
      Layer7 (F);
      Layer7_to_6_Lemma (F);
      Layer6 (F);

      Layer5 (F);
      Layer4 (F);
      Layer3 (F);
      Layer2 (F);
      Layer1 (F);

      for I in Index_256 loop
         F (I) := FQMul (1441, F (I));
         pragma Loop_Invariant (for all K in Index_256 range 0 .. I => F (K) in Mont_Range);
      end loop;

   end INTTnew;

   procedure INTT (F : in out Poly_Zq)
   is
      subtype NTT_Len_Bit_Index is Natural range 0 .. 6;
      subtype NTT_Len_Power     is Natural range 1 .. 7;

      --  A power of 2 between 2 and 128. Used in NTT and NTT_Inv
      subtype Len_T is Index_256
         with Dynamic_Predicate =>
            (for some I in NTT_Len_Power => Len_T = 2**I);

      --  A power of 2 between 1 and 64. Used in NTT and NTT_Inv
      subtype Count_T is Index_256
         with Dynamic_Predicate =>
            (for some I in NTT_Len_Bit_Index => Count_T = 2**I);

      K     : SU7;
      Len   : Len_T;
      Count : Count_T;
   begin
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

            NTT_Inv_Inner (F     => F,
                           ZI    => K,
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

      for I in Index_256 loop
         F (I) := FQMul (1441, F (I));
         pragma Loop_Invariant (for all K in Index_256 range 0 .. I => F (K) in Mont_Range);
      end loop;

   end INTT;

end RMerge2.Inv;

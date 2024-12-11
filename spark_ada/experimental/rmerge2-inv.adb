package body RMerge2.Inv
  with SPARK_Mode => On
is
   --============================================================
   --  Part 1 - INTT as per FIPS-203 with Eager reduction
   --  of coefficients
   --============================================================

   --  Multiply all coefficients by F = mont^2/128 = 1441, and
   --  reduce so all coefficients in Mont_Range
   procedure Invert_And_Reduce (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range8),
          Post => (for all K in Index_256 => F (K) in Mont_Range);

   procedure Invert_And_Reduce (F : in out Poly_Zq)
   is
   begin
      for I in Index_256 loop
         F (I) := FQMul (1441, F (I));
         pragma Loop_Invariant (for all K in Index_256 range 0     .. I   => F (K) in Mont_Range);
         pragma Loop_Invariant (for all K in Index_256 range I + 1 .. 255 => F (K) in Mont_Range8);
      end loop;
   end Invert_And_Reduce;


   --  General purpose GS-Butterfly, as per FIPS-203 with EAGER
   --  Reduction.
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
                    (for all K in Index_256 => F (K) in Mont_Range),
          Post   => (for all K in Index_256 => F (K) in Mont_Range);

   procedure NTT_Inv_Inner (F     : in out Poly_Zq;
                            ZI    : in     SU7;
                            Start : in     Index_256;
                            Len   : in     I32)
   is
      T : I16;
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
   begin
      for J in Index_256 range Start .. Start + (Len - 1) loop
         T           := F (J);
         F (J)       := Barrett_Reduce (T + F (J + Len)); --  Reduce
         F (J + Len) := FQMul (Zeta, F (J + Len) - T); -- Reduce

         pragma Loop_Invariant
            -- Elements 0 .. Start - 1 are unchanged
           (for all I in Index_256 range 0 .. Start - 1 => F (I) = F'Loop_Entry (I));
         pragma Loop_Invariant
            -- Elements Start through J are updated and in BRange
           (for all I in Index_256 range Start .. J => F (I) in BRange);
         pragma Loop_Invariant
            -- Elements Start through J are updated and ALSO in Mont_Range
           (for all I in Index_256 range Start .. J => F (I) in Mont_Range);
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
      pragma Assert
         -- Elements Start through J are updated and in Mont_Range
        (for all I in Index_256 range Start .. Start + Len - 1 => F (I) in Mont_Range);
      pragma Assert
         --  Elements Start + Len through J + Len are updated and in Mont_Range
        (for all I in Index_256 range Start + Len .. Start + Len - 1 + Len => (F (I) in Mont_Range));

      --  All other elements preserve their initial values, so still in Mont_Range
      --  as per the precondition, so...
      pragma Assert (for all K in Index_256 => F (K) in Mont_Range);

   end NTT_Inv_Inner;


   --  FIPS-203 Algorithm 10, but inverting and reducing BEFORE butterflies
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
      Invert_And_Reduce (F);

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
            pragma Loop_Invariant (for all K in Index_256 => F (K) in Mont_Range);

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
         pragma Loop_Invariant (Count * Len = 128);
         pragma Loop_Invariant (for all K in Index_256 => F (K) in Mont_Range);
      end loop;

      --  Substitute I = 0 into the outer loop invariant to get
      pragma Assert (K = 0);
      pragma Assert (for all K in Index_256 => F (K) in Mont_Range);

   end INTT;


   --============================================================
   --  Part 2 - INTT optimized with exact tracking of
   --  coefficient ranges for each layer, and deferred reduction
   --============================================================

   --  ================
   --  Layer 1 Len=128
   --  ================

   procedure Layer1 (F     : in out Poly_Zq)
     with Global => null,
          Pre    => (for all K in Index_256 => F (K) in Mont_Range4),
          Post   => (for all K in Index_256 => F (K) in Mont_Range8);

   procedure Layer1 (F     : in out Poly_Zq)
   is
      T : I16;
      Zeta : constant Zeta_Range := Zeta_ExpC (1);
   begin
      for J in Index_256 range 0 .. 127 loop
         declare
            CI0   : constant Index_256 := J;
            CI128 : constant Index_256 := CI0 + 128;
            C0    : constant I16 := F (CI0);
            C128  : constant I16 := F (CI128);
         begin
            T         := C0;
            F (CI0)   := C128 + T; --  Defer reduction
            F (CI128) := FQMul (Zeta, C128 - T);
         end;

         --  Modified, increased to Mont_Range8
         pragma Loop_Invariant (for all K in Index_256 range 0 .. J  => F (K) in Mont_Range8);

         --  Not modified, but about to be
         pragma Loop_Invariant (for all K in Index_256 range J + 1  .. 127 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range J + 1  .. 127 => F (K) in Mont_Range4);

         --  Modified, increased to Mont_Range8
         pragma Loop_Invariant (for all K in Index_256 range 128 .. J + 128  => F (K) in Mont_Range8);

         --  Not modified, but about to be
         pragma Loop_Invariant (for all K in Index_256 range J + 129 .. 255 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range J + 129 .. 255 => F (K) in Mont_Range4);

      end loop;

      --  J = 127, substitute and simplify yields the postcondition
      pragma Assert (for all K in Index_256 range   0 .. 127  => F (K) in Mont_Range8);
      pragma Assert (for all K in Index_256 range 128 .. 255  => F (K) in Mont_Range8);

   end Layer1;

   procedure Reduce_All (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in I16),
          Post => (for all K in Index_256 => F (K) in Mont_Range);

   procedure Reduce_All (F : in out Poly_Zq)
   is
   begin
      for I in F'Range loop
         F (I) := Barrett_Reduce (F (I));
         pragma Loop_Invariant (for all K in Index_256 range 0 .. I => F (K) in Mont_Range);
      end loop;
   end Reduce_All;

   --  ================
   --  Layer 2 Len=64
   --  ================

   procedure NTT_Inv_Inner2 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
     with Pre    => Start <= 128 and then
                    Start mod 128 = 0 and then
                    ZI in 2 .. 3 and then
                    ((for all K in Index_256 range 0 .. 15 => F (Start + K)       in Mont_Range4) and
                     (for all K in Index_256 range 0 .. 15 => F (Start +  16 + K) in Mont_Range2) and
                     (for all K in Index_256 range 0 .. 15 => F (Start +  32 + K) in Mont_Range)  and
                     (for all K in Index_256 range 0 .. 15 => F (Start +  48 + K) in Mont_Range)  and
                     (for all K in Index_256 range 0 .. 15 => F (Start +  64 + K) in Mont_Range4) and
                     (for all K in Index_256 range 0 .. 15 => F (Start +  80 + K) in Mont_Range2) and
                     (for all K in Index_256 range 0 .. 15 => F (Start +  96 + K) in Mont_Range)  and
                     (for all K in Index_256 range 0 .. 15 => F (Start + 112 + K) in Mont_Range)),
          Post   => ((for all K in Index_256 range 0 .. Start - 1  => F (K) = F'Old (K)) and
                     (for all K in Index_256 range 0 .. 15 => F (Start + K)       in Mont_Range8 and
                                                              F (Start +  16 + K) in Mont_Range4 and
                                                              F (Start +  32 + K) in Mont_Range2 and
                                                              F (Start +  48 + K) in Mont_Range2 and
                                                              F (Start +  64 + K) in Mont_Range  and
                                                              F (Start +  80 + K) in Mont_Range  and
                                                              F (Start +  96 + K) in Mont_Range  and
                                                              F (Start + 112 + K) in Mont_Range) and
                     (for all K in Index_256 range Start + 128 .. 255        => F (K) = F'Old (K)));


   procedure NTT_Inv_Inner2 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
   is
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
   begin
      for J in Index_256 range 0 .. 15 loop
         declare
            CI0   : constant Index_256 := Start + J;
            CI16  : constant Index_256 := CI0 + 16;
            CI32  : constant Index_256 := CI0 + 32;
            CI48  : constant Index_256 := CI0 + 48;
            CI64  : constant Index_256 := CI0 + 64;
            CI80  : constant Index_256 := CI0 + 80;
            CI96  : constant Index_256 := CI0 + 96;
            CI112 : constant Index_256 := CI0 + 112;

            C0   : constant I16 := F (CI0);
            pragma Assert (C0 in Mont_Range4);
            C16  : constant I16 := F (CI16);
            pragma Assert (C16 in Mont_Range2);
            C32  : constant I16 := F (CI32);
            pragma Assert (C32 in Mont_Range);
            C48  : constant I16 := F (CI48);
            pragma Assert (C48 in Mont_Range);
            C64  : constant I16 := F (CI64);
            pragma Assert (C64 in Mont_Range4);
            C80  : constant I16 := F (CI80);
            pragma Assert (C80 in Mont_Range2);
            C96  : constant I16 := F (CI96);
            pragma Assert (C96 in Mont_Range);
            C112 : constant I16 := F (CI112);
            pragma Assert (C112 in Mont_Range);
         begin
            F (CI0)  := C64  + C0;  --  Defer reduction
            pragma Assert (F (CI0) in Mont_Range8);

            F (CI16) := C80  + C16; --  Defer reduction
            pragma Assert (F (CI16) in Mont_Range4);

            F (CI32) := C96  + C32; --  Defer reduction
            pragma Assert (F (CI32) in Mont_Range2);

            F (CI48) := C112 + C48; --  Defer reduction
            pragma Assert (F (CI48) in Mont_Range2);

            F (CI64)  := FQMul (Zeta, C64 - C0);
            pragma Assert (F (CI64) in Mont_Range);
            F (CI80)  := FQMul (Zeta, C80 - C16);
            pragma Assert (F (CI80) in Mont_Range);
            F (CI96)  := FQMul (Zeta, C96 - C32);
            pragma Assert (F (CI96) in Mont_Range);
            F (CI112) := FQMul (Zeta, C112 - C48);
            pragma Assert (F (CI112) in Mont_Range);
         end;

         --  Not modified, but about to be, therefore initial value and range as per precondition
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 1  .. Start + 15 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 1  .. Start + 15 => F (K) in Mont_Range4);

         --  Not modified, but about to be, therefore initial value and range as per precondition
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 17 .. Start + 31 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 17 .. Start + 31 => F (K) in Mont_Range2);

         --  Not modified, but about to be, therefore initial value and range as per precondition
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 33 .. Start + 47 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 33 .. Start + 47 => F (K) in Mont_Range);

         --  Not modified, but about to be, therefore initial value and range as per precondition
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 49 .. Start + 63 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 49 .. Start + 63 => F (K) in Mont_Range);

         --  Not modified, but about to be, therefore initial value and range as per precondition
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 65 .. Start + 79 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 65 .. Start + 79 => F (K) in Mont_Range4);

         --  Not modified, but about to be, therefore initial value and range as per precondition
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 81 .. Start + 95 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 81 .. Start + 95 => F (K) in Mont_Range2);

         --  Not modified, but about to be, therefore initial value and range as per precondition
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 97 .. Start + 111 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 97 .. Start + 111 => F (K) in Mont_Range);

         --  Not modified, but about to be, therefore initial value and range as per precondition
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 113 .. Start + 127 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 113 .. Start + 127 => F (K) in Mont_Range);


         --  Modified, increased to Mont_Range8
         pragma Loop_Invariant (for all K in Index_256 range Start          .. Start + J  => F (K) in Mont_Range8);
         --  Modified, increased to Mont_Range4
         pragma Loop_Invariant (for all K in Index_256 range Start + 16     .. Start + J + 16 => F (K) in Mont_Range4);
         --  Modified, increased to Mont_Range2
         pragma Loop_Invariant (for all K in Index_256 range Start + 32     .. Start + J + 32 => F (K) in Mont_Range2);
         --  Modified, increased to Mont_Range2
         pragma Loop_Invariant (for all K in Index_256 range Start + 48     .. Start + J + 48 => F (K) in Mont_Range2);
         --  Modified, but still in Mont_Range
         pragma Loop_Invariant (for all K in Index_256 range Start + 64     .. Start + J + 64 => F (K) in Mont_Range);
         --  Modified, but still in Mont_Range
         pragma Loop_Invariant (for all K in Index_256 range Start + 80     .. Start + J + 80 => F (K) in Mont_Range);
         --  Modified, but still in Mont_Range
         pragma Loop_Invariant (for all K in Index_256 range Start + 96     .. Start + J + 96 => F (K) in Mont_Range);
         --  Modified, but still in Mont_Range
         pragma Loop_Invariant (for all K in Index_256 range Start + 112    .. Start + 112 + J => F (K) in Mont_Range);

         --  Never changed
         pragma Loop_Invariant (for all K in Index_256 range 0           .. Start - 1  => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + 128 .. 255        => F (K) = F'Loop_Entry (K));

      end loop;

      --  J = 15, substitute and simplify...
      pragma Assert (for all K in Index_256 range Start          .. Start +  15 => F (K) in Mont_Range8);
      pragma Assert (for all K in Index_256 range Start + 16     .. Start +  31 => F (K) in Mont_Range4);
      pragma Assert (for all K in Index_256 range Start + 32     .. Start +  47 => F (K) in Mont_Range2);
      pragma Assert (for all K in Index_256 range Start + 48     .. Start +  63 => F (K) in Mont_Range2);
      pragma Assert (for all K in Index_256 range Start + 64     .. Start +  79 => F (K) in Mont_Range);
      pragma Assert (for all K in Index_256 range Start + 80     .. Start +  95 => F (K) in Mont_Range);
      pragma Assert (for all K in Index_256 range Start + 96     .. Start + 111 => F (K) in Mont_Range);
      pragma Assert (for all K in Index_256 range Start + 112    .. Start + 127 => F (K) in Mont_Range);

      --  Merge the last four assertions to get:
      pragma Assert (for all K in Index_256 range Start + 64     .. Start + 127 => F (K) in Mont_Range);
   end NTT_Inv_Inner2;

   procedure Layer2 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  =>   ((for all L in I32 range   0 ..  15 => F (L) in Mont_Range4) and
                     (for all L in I32 range  16 ..  31 => F (L) in Mont_Range2) and
                     (for all L in I32 range  32 ..  63 => F (L) in Mont_Range)  and
                     (for all L in I32 range  64 ..  79 => F (L) in Mont_Range4) and
                     (for all L in I32 range  80 ..  95 => F (L) in Mont_Range2) and
                     (for all L in I32 range  96 .. 127 => F (L) in Mont_Range)  and
                     (for all L in I32 range 128 .. 143 => F (L) in Mont_Range4) and
                     (for all L in I32 range 144 .. 159 => F (L) in Mont_Range2) and
                     (for all L in I32 range 160 .. 191 => F (L) in Mont_Range)  and
                     (for all L in I32 range 192 .. 207 => F (L) in Mont_Range4) and
                     (for all L in I32 range 208 .. 223 => F (L) in Mont_Range2) and
                     (for all L in I32 range 224 .. 255 => F (L) in Mont_Range)),
          Post   => (for all K in Index_256 range 0 .. 15 => F (K)       in Mont_Range8 and
                                                             F  (16 + K) in Mont_Range4 and
                                                             F  (32 + K) in Mont_Range2 and
                                                             F  (48 + K) in Mont_Range2 and
                                                             F  (64 + K) in Mont_Range  and
                                                             F  (80 + K) in Mont_Range  and
                                                             F  (96 + K) in Mont_Range  and
                                                             F (112 + K) in Mont_Range  and
                                                             F (128 + K) in Mont_Range8 and
                                                             F (144 + K) in Mont_Range4 and
                                                             F (160 + K) in Mont_Range2 and
                                                             F (176 + K) in Mont_Range2 and
                                                             F (192 + K) in Mont_Range  and
                                                             F (208 + K) in Mont_Range  and
                                                             F (224 + K) in Mont_Range  and
                                                             F (240 + K) in Mont_Range);

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
                    Start mod 64 = 0 and then
                    ZI in 4 .. 7 and then
                    (for all K in Index_256 range 0 .. 15 => F (Start + K)      in Mont_Range2 and
                                                             F (Start + 16 + K) in Mont_Range and
                                                             F (Start + 32 + K) in Mont_Range2 and
                                                             F (Start + 48 + K) in Mont_Range),
          Post   => ((for all K in Index_256 range 0          .. Start - 1  => F (K) = F'Old (K)) and
                     (for all K in Index_256 range Start      .. Start + 15 => F (K) in Mont_Range4) and
                     (for all K in Index_256 range Start + 16 .. Start + 31 => F (K) in Mont_Range2) and
                     (for all K in Index_256 range Start + 32 .. Start + 63 => F (K) in Mont_Range) and
                     (for all K in Index_256 range Start + 64 .. 255        => F (K) = F'Old (K)));

   procedure NTT_Inv_Inner3 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
   is
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
   begin
      for J in Index_256 range 0 .. 15 loop
         declare
            CI0  : constant Index_256 := Start + J;
            pragma Assert (CI0 in Start .. Start + 15);

            CI16 : constant Index_256 := CI0 + 16;
            pragma Assert (CI16 in Start + 16 .. Start + 31);

            CI32 : constant Index_256 := CI0 + 32;
            pragma Assert (CI32 in Start + 32 .. Start + 47);

            CI48 : constant Index_256 := CI0 + 48;
            pragma Assert (CI48 in Start + 48 .. Start + 63);

            C0   : constant I16 := F (CI0);
            pragma Assert (C0 in Mont_Range2);

            C16  : constant I16 := F (CI16);
            pragma Assert (C16 in Mont_Range);

            C32  : constant I16 := F (CI32);
            pragma Assert (C32 in Mont_Range2);

            C48  : constant I16 := F (CI48);
            pragma Assert (C48 in Mont_Range);
         begin
            F (CI0)  := C32 + C0; --  Defer reduction
            pragma Assert (F (CI0) in Mont_Range4);

            F (CI16) := C48 + C16; --  Defer reduction
            pragma Assert (F (CI16) in Mont_Range2);

            F (CI32) := FQMul (Zeta, C32 - C0);
            pragma Assert (F (CI32) in Mont_Range);

            F (CI48) := FQMul (Zeta, C48 - C16);
            pragma Assert (F (CI48) in Mont_Range);
         end;

         --  Never changed
         pragma Loop_Invariant (for all K in Index_256 range 0              .. Start - 1  => F (K) = F'Loop_Entry (K));


         --  Modified, increased to Mont_Range4
         pragma Loop_Invariant (for all K in Index_256 range Start          .. Start + J  => F (K) in Mont_Range4);

         --  Not modified, but about to be
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 1  .. Start + 15 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 1  .. Start + 15 => F (K) in Mont_Range2);



         --  Modified, increased to Mont_Range2
         pragma Loop_Invariant (for all K in Index_256 range Start + 16     .. Start + 16 + J => F (K) in Mont_Range2);

         --  Not modified, but about to be
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 17 .. Start + 31 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 17 .. Start + 31 => F (K) in Mont_Range);



         --  Modified, but still in Mont_Range
         pragma Loop_Invariant (for all K in Index_256 range Start + 32     .. Start + 32 + J => F (K) in Mont_Range);

         --  Not modified, but about to be
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 33 .. Start + 47 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 33 .. Start + 47 => F (K) in Mont_Range2);



         --  Modified, but still in Mont_Range
         pragma Loop_Invariant (for all K in Index_256 range Start + 48     .. Start + 48 + J => F (K) in Mont_Range);

         --  Not modified, but about to be
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 49 .. Start + 63 => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 49 .. Start + 63 => F (K) in Mont_Range);



         --  Never changed
         pragma Loop_Invariant (for all K in Index_256 range Start + 64     .. 255 => F (K) = F'Loop_Entry (K));

      end loop;

      --  J = 15, substitute and simplify...
      pragma Assert (for all K in Index_256 range Start      .. Start + 15 => F (K) in Mont_Range4);
      pragma Assert (for all K in Index_256 range Start + 16 .. Start + 31 => F (K) in Mont_Range2);
      pragma Assert (for all K in Index_256 range Start + 32 .. Start + 47 => F (K) in Mont_Range);
      pragma Assert (for all K in Index_256 range Start + 48 .. Start + 63 => F (K) in Mont_Range);

      --  Merge the last two assertions to get:
      pragma Assert (for all K in Index_256 range Start + 32 .. Start + 63 => F (K) in Mont_Range);
   end NTT_Inv_Inner3;

   procedure Layer3 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => ((for all K in I32 range    0 ..  15 => F (K) in Mont_Range2) and
                   (for all K in I32 range   16 ..  31 => F (K) in Mont_Range) and
                   (for all K in I32 range   32 ..  47 => F (K) in Mont_Range2) and
                   (for all K in I32 range   48 ..  63 => F (K) in Mont_Range) and
                   (for all K in I32 range   64 ..  79 => F (K) in Mont_Range2) and
                   (for all K in I32 range   80 ..  95 => F (K) in Mont_Range) and
                   (for all K in I32 range   96 .. 111 => F (K) in Mont_Range2) and
                   (for all K in I32 range  112 .. 127 => F (K) in Mont_Range) and
                   (for all K in I32 range  128 .. 143 => F (K) in Mont_Range2) and
                   (for all K in I32 range  144 .. 159 => F (K) in Mont_Range) and
                   (for all K in I32 range  160 .. 175 => F (K) in Mont_Range2) and
                   (for all K in I32 range  176 .. 191 => F (K) in Mont_Range) and
                   (for all K in I32 range  192 .. 207 => F (K) in Mont_Range2) and
                   (for all K in I32 range  208 .. 223 => F (K) in Mont_Range) and
                   (for all K in I32 range  224 .. 239 => F (K) in Mont_Range2) and
                   (for all K in I32 range  240 .. 255 => F (K) in Mont_Range)),
          Post => (for all K in I32 range 0 .. 3 =>
                      ((for all L in I32 range  0 .. 15 => F (K * 64 + L) in Mont_Range4) and
                       (for all L in I32 range 16 .. 31 => F (K * 64 + L) in Mont_Range2) and
                       (for all L in I32 range 32 .. 63 => F (K * 64 + L) in Mont_Range)));

   procedure Layer3 (F : in out Poly_Zq)
   is
   begin
      NTT_Inv_Inner3 (F, 7, 0);
      NTT_Inv_Inner3 (F, 6, 64);
      NTT_Inv_Inner3 (F, 5, 128);
      NTT_Inv_Inner3 (F, 4, 192);
   end Layer3;

   --  ================
   --  Layer 7
   --  ================

   procedure NTT_Inv_InvertInner7 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
     with Global => null,
          Pre  => ZI in 64 .. 127 and then
                  Start <= 252 and then
                  (for all I in Index_256 range Start .. Start + 3 => (F (I) in I16)),
          Post => ((for all I in Index_256 range 0         .. Start - 1 => (F (I) = F'Old (I))) and
                   (for all I in Index_256 range Start     .. Start + 3 => (F (I) in Mont_Range)) and
                   (for all I in Index_256 range Start + 4 .. 255       => (F (I) = F'Old (I))));

   procedure NTT_Inv_InvertInner7 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
   is
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
      CI0 : constant Index_256 := Start;
      CI1 : constant Index_256 := CI0 + 1;
      CI2 : constant Index_256 := CI0 + 2;
      CI3 : constant Index_256 := CI0 + 3;

      C0  : constant Mont_Range := FQMul (1441, F (CI0));
      C1  : constant Mont_Range := FQMul (1441, F (CI1));
      C2  : constant Mont_Range := FQMul (1441, F (CI2));
      C3  : constant Mont_Range := FQMul (1441, F (CI3));
   begin
      F (CI0) := Barrett_Reduce (C0 + C2);
      F (CI2) := FQMul (Zeta, (C2 - C0));

      F (CI1) := Barrett_Reduce (C1 + C3);
      F (CI3) := FQMul (Zeta, (C3 - C1));
   end NTT_Inv_InvertInner7;


   procedure InvertLayer7 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Post  => (for all K in Index_256 => F (K) in Mont_Range);

   procedure InvertLayer7 (F : in out Poly_Zq)
   is
   begin
      for J in I32 range 0 .. 63 loop
         NTT_Inv_InvertInner7 (F, 127 - J, J * 4);
         pragma Loop_Invariant (for all K in I32 range 0 .. (J * 4 + 3) => F (K) in Mont_Range);
      end loop;
   end InvertLayer7;


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
                    (for all K in Index_256 range Start .. Start + 7 => F (K) in Mont_Range),
          Post   => (for all K in Index_256 range 0         .. Start - 1 => F (K) = F'Old (K)) and
                    (for all K in Index_256 range Start     .. Start + 7 => F (K) in Mont_Range2) and
                    (for all K in Index_256 range Start + 8 .. 255       => F (K) = F'Old (K));


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
          Pre  => (for all K in Index_256 => F (K) in Mont_Range),
          Post => (for all K in Index_256 => F (K) in Mont_Range2);

   procedure Layer6 (F : in out Poly_Zq)
   is
   begin
      for J in I32 range 0 .. 31 loop
         NTT_Inv_Inner6 (F, 63 - J, J * 8);

         --  Elements modified so far increase in magnitude as follows:
         pragma Loop_Invariant (for all K in I32 range 0         .. J * 8 + 7 => F (K) in Mont_Range2);
         pragma Loop_Invariant (for all K in I32 range J * 8 + 8 .. 255       => F (K) in Mont_Range);
      end loop;
   end Layer6;

   --  ================
   --  Layer 54
   --  ================

   procedure NTT_Inv_Inner4 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
     with Global => null,
          Inline_Always,
          Pre    => Start <= 224 and then
                    Start mod 32 = 0 and then
                    ZI in 8 .. 15 and then
                    (for all K in Index_256 range Start      .. Start + 31 => F (K) in Mont_Range4) and then
                    (for all K in Index_256 range Start + 32 .. 255        => F (K) in Mont_Range4),
          Post   => (for all K in Index_256 range 0 .. Start - 1 => F (K) = F'Old (K)) and
                    (for all K in Index_256 range Start .. Start + 31 => F (K) in Mont_Range8) and
                    (for all K in Index_256 range Start + 32 .. 255 => F (K) = F'Old (K));

   procedure NTT_Inv_Inner4 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
   is
      Zeta : constant Zeta_Range := Zeta_ExpC (ZI);
   begin
      for J in Index_256 range 0 .. 15 loop
         declare
            CI0  : constant Index_256 := Start + J;
            CI16 : constant Index_256 := Start + J + 16;
            C0   : constant I16 := F (CI0);
            C16  : constant I16 := F (CI16);
         begin
            F (CI0)  := C16 + C0; --  Defer reduction
            F (CI16) := FQMul (Zeta, C16 - C0);
         end;
         pragma Loop_Invariant (for all K in Index_256 range 0                  .. Start - 1      => F (K) = F'Loop_Entry (K));
         pragma Loop_Invariant (for all K in Index_256 range Start              .. Start + J      => F (K) in Mont_Range8);
         pragma Loop_Invariant (for all K in Index_256 range Start + J + 1      .. Start + 15     => F (K) in Mont_Range4);
         pragma Loop_Invariant (for all K in Index_256 range Start + 16         .. Start + 16 + J => F (K) in Mont_Range8);
         pragma Loop_Invariant (for all K in Index_256 range Start + 16 + J + 1 .. Start + 31     => F (K) in Mont_Range4);
         pragma Loop_Invariant (for all K in Index_256 range Start + 32         .. 255            => F (K) = F'Loop_Entry (K));
      end loop;
   end NTT_Inv_Inner4;

   procedure NTT_Inv_Inner5 (F     : in out Poly_Zq;
                             ZI    : in     SU7;
                             Start : in     Index_256)
     with Global => null,
          Inline_Always,
          Pre    => ZI in 16 .. 31 and then
                    Start <= 240 and then
                    Start mod 16 = 0 and then
                    (for all K in Index_256 range Start .. Start + 15 => F (K) in Mont_Range2),
          Post   => (for all K in Index_256 range 0 .. Start - 1 => F (K) = F'Old (K)) and
                    (for all K in Index_256 range Start .. Start + 15 => F (K) in Mont_Range4) and
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

   procedure Layer54_Slice (F     : in out Poly_Zq;
                            L4ZI  : in     SU7;
                            Start : in     Index_256)
     with Pre  => L4ZI in 8 .. 15 and then
                  Start <= 224 and then
                  Start mod 32 = 0 and then
                  (for all I in Index_256 range 0     .. Start - 1  => F (I) in Mont_Range8) and then
                  (for all I in Index_256 range Start .. 255        => F (I) in Mont_Range2),
          Post => (for all I in Index_256 range 0          .. Start + 31 => F (I) in Mont_Range8) and
                  (for all I in Index_256 range Start + 32 .. 255        => F (I) in Mont_Range2)
   is
      L5ZI1 : constant SU7 := L4ZI * 2;
      L5ZI2 : constant SU7 := L5ZI1 + 1;
   begin
      NTT_Inv_Inner5 (F, L5ZI2, Start);
      NTT_Inv_Inner5 (F, L5ZI1, Start + 16);
      NTT_Inv_Inner4 (F, L4ZI,  Start);
   end Layer54_Slice;

   procedure Layer54 (F : in out Poly_Zq)
     with Pre  => (for all I in Index_256 => F (I) in Mont_Range2),
          Post => (for all I in Index_256 => F (I) in Mont_Range8);

   procedure Layer54 (F : in out Poly_Zq)
   is
   begin
      Layer54_Slice (F, 15, 0);
      Layer54_Slice (F, 14, 32);
      Layer54_Slice (F, 13, 64);
      Layer54_Slice (F, 12, 96);
      Layer54_Slice (F, 11, 128);
      Layer54_Slice (F, 10, 160);
      Layer54_Slice (F,  9, 192);
      Layer54_Slice (F,  8, 224);
   end Layer54;

   --  ================
   --  Layer 321
   --  ================

   procedure Layer321 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all I in Index_256 => F (I) in Mont_Range8),
          Post => (for all I in Index_256 => F (I) in Mont_Range);

   procedure Layer321 (F : in out Poly_Zq)
   is
   begin
      Reduce_All (F);
      Layer3 (F);
      Reduce_All (F);
      Layer2 (F);
      Reduce_All (F);
      Layer1 (F);
      Reduce_All (F);
   end Layer321;


   --  Optimized implementation, one layer at a time
   procedure INTTnew (F : in out Poly_Zq)
   is
   begin
      InvertLayer7 (F);
      Layer6 (F);
      Layer54 (F);
      Layer321(F);
   end INTTnew;

end RMerge2.Inv;

package body RMerge2.Inv
  with SPARK_Mode => On
is
   --  Shorthand to shorten line length of invariants
   subtype I256 is Index_256;

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
   --  coefficient ranges, deferred reduction, and merging
   --  of layers (5,4) and (3,2,1)
   --============================================================

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

      --  Invert and reduce all coefficients here the first time they
      --  are read. This is efficient, and also means we can accept
      --  any I16 value for all coefficients as input.
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

   procedure Layer54_Slice (F     : in out Poly_Zq;
                            L4ZI  : in     SU7;
                            Start : in     Index_256)
     with Global => null,
          No_Inline,
          Pre  => L4ZI in 8 .. 15 and then
                  Start <= 224 and then
                  Start mod 32 = 0 and then
                  (for all I in Index_256 range 0     .. Start - 1  => F (I) in Mont_Range) and then
                  (for all I in Index_256 range Start .. 255        => F (I) in Mont_Range2),
          Post => (for all I in Index_256 range 0          .. Start + 31 => F (I) in Mont_Range) and
                  (for all I in Index_256 range Start + 32 .. 255        => F (I) in Mont_Range2);

   procedure Layer54_Slice (F     : in out Poly_Zq;
                            L4ZI  : in     SU7;
                            Start : in     Index_256)
   is
      L4Zeta  : constant Zeta_Range := Zeta_ExpC (L4ZI);
      L5Zeta1 : constant Zeta_Range := Zeta_ExpC (L4ZI * 2);
      L5Zeta2 : constant Zeta_Range := Zeta_ExpC (L4ZI * 2 + 1);
   begin
      for I in Index_256 range 0 .. 7 loop
         declare
            CI0  : constant Index_256 := Start + I;
            CI8  : constant Index_256 := CI0  + 8;
            CI16 : constant Index_256 := CI8  + 8;
            CI24 : constant Index_256 := CI16 + 8;
         begin
            declare
               C0   : constant Mont_Range2 := F (CI0);
               C8   : constant Mont_Range2 := F (CI8);
               C16  : constant Mont_Range2 := F (CI16);
               C24  : constant Mont_Range2 := F (CI24);
            begin
               F (CI0) := C0 + C8;
               F (CI8) := FQMul (L5Zeta2, C8 - C0);

               F (CI16) := C16 + C24;
               F (CI24) := FQMul (L5Zeta1, C24 - C16);
            end;

            declare
               C0   : constant Mont_Range4 := F (CI0);
               C8   : constant Mont_Range  := F (CI8);
               C16  : constant Mont_Range4 := F (CI16);
               C24  : constant Mont_Range  := F (CI24);
            begin
               --  In layer 4, reduce all coefficients to be in Mont_Range
               --  to meet the pre-condition of Layer321
               F (CI0)  := Barrett_Reduce (C16 + C0);
               F (CI16) := FQMul (L4Zeta, C16 - C0);

               F (CI8)  := Barrett_Reduce (C24 + C8);
               F (CI24) := FQMul (L4Zeta, C24 - C8);
            end;
         end;

         pragma Loop_Invariant (for all K in I256 range 0              .. Start - 1      => F (K) in Mont_Range);
         pragma Loop_Invariant (for all K in I256 range Start          .. Start + I      => F (K) in Mont_Range);
         pragma Loop_Invariant (for all K in I256 range Start + I + 1  .. Start + 7      => F (K) in Mont_Range2);
         pragma Loop_Invariant (for all K in I256 range Start + 8      .. Start + 8 + I  => F (K) in Mont_Range);
         pragma Loop_Invariant (for all K in I256 range Start + 9 + I  .. Start + 15     => F (K) in Mont_Range2);
         pragma Loop_Invariant (for all K in I256 range Start + 16     .. Start + 16 + I => F (K) in Mont_Range);
         pragma Loop_Invariant (for all K in I256 range Start + 17 + I .. Start + 23     => F (K) in Mont_Range2);
         pragma Loop_Invariant (for all K in I256 range Start + 24     .. Start + 24 + I => F (K) in Mont_Range);
         pragma Loop_Invariant (for all K in I256 range Start + 25 + I .. Start + 31     => F (K) in Mont_Range2);
         pragma Loop_Invariant (for all K in I256 range Start + 32     .. 255            => F (K) in Mont_Range2);
      end loop;
   end Layer54_Slice;

   procedure Layer54 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all I in Index_256 => F (I) in Mont_Range2),
          Post => (for all I in Index_256 => F (I) in Mont_Range);

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
          Pre  => (for all I in Index_256 => F (I) in Mont_Range),
          Post => (for all I in Index_256 => F (I) in Mont_Range8);

   procedure Layer321 (F : in out Poly_Zq)
   is
      Zeta1 : constant Zeta_Range := Zeta_ExpC (1);
      Zeta2 : constant Zeta_Range := Zeta_ExpC (2);
      Zeta3 : constant Zeta_Range := Zeta_ExpC (3);
      Zeta4 : constant Zeta_Range := Zeta_ExpC (4);
      Zeta5 : constant Zeta_Range := Zeta_ExpC (5);
      Zeta6 : constant Zeta_Range := Zeta_ExpC (6);
      Zeta7 : constant Zeta_Range := Zeta_ExpC (7);
   begin
      --  We inline, expand, loop-fuse and simplify this sequence of calls:
      --   NTT_Inv_Inner (F, 7, 0, 32);
      --   NTT_Inv_Inner (F, 6, 64, 32);
      --   NTT_Inv_Inner (F, 5, 128, 32);
      --   NTT_Inv_Inner (F, 4, 192, 32);
      --   NTT_Inv_Inner (F, 3, 0, 64);
      --   NTT_Inv_Inner (F, 2, 128, 64);
      --  to get:
      for J in Index_256 range 0 .. 31 loop
         declare
            CI0   : constant I256 := J;
            CI32  : constant I256 := CI0 + 32;
            CI64  : constant I256 := CI0 + 64;
            CI96  : constant I256 := CI0 + 96;
            CI128 : constant I256 := CI0 + 128;
            CI160 : constant I256 := CI0 + 160;
            CI192 : constant I256 := CI0 + 192;
            CI224 : constant I256 := CI0 + 224;
         begin
            --  Layer 3
            declare
               C0    : constant Mont_Range := F (CI0);
               C32   : constant Mont_Range := F (CI32);
               C64   : constant Mont_Range := F (CI64);
               C96   : constant Mont_Range := F (CI96);
               C128  : constant Mont_Range := F (CI128);
               C160  : constant Mont_Range := F (CI160);
               C192  : constant Mont_Range := F (CI192);
               C224  : constant Mont_Range := F (CI224);
            begin
               F (CI0)  := C0 + C32;
               F (CI32) := FQMul (Zeta7, C32 - C0);

               F (CI64) := C64 + C96;
               F (CI96) := FQMul (Zeta6, C96 - C64);

               F (CI128) := C128 + C160;
               F (CI160) := FQMul (Zeta5, C160 - C128);

               F (CI192) := C192 + C224;
               F (CI224) := FQMul (Zeta4, C224 - C192);
            end;

            --  Layer 2
            declare
               C0    : constant Mont_Range2 := F (CI0);
               C32   : constant Mont_Range  := F (CI32);
               C64   : constant Mont_Range2 := F (CI64);
               C96   : constant Mont_Range  := F (CI96);
               C128  : constant Mont_Range2 := F (CI128);
               C160  : constant Mont_Range  := F (CI160);
               C192  : constant Mont_Range2 := F (CI192);
               C224  : constant Mont_Range  := F (CI224);
            begin
               F (CI0)  := C0 + C64;
               F (CI64) := FQMul (Zeta3, C64 - C0);

               F (CI32) := C32 + C96;
               F (CI96) := FQMul (Zeta3, C96 - C32);

               F (CI128) := C128 + C192;
               F (CI192) := FQMul (Zeta2, C192 - C128);

               F (CI160) := C160 + C224;
               F (CI224) := FQMul (Zeta2, C224 - C160);
            end;

            --  Layer 1
            declare
               C0    : constant Mont_Range4 := F (CI0);
               C32   : constant Mont_Range2 := F (CI32);
               C64   : constant Mont_Range  := F (CI64);
               C96   : constant Mont_Range  := F (CI96);
               C128  : constant Mont_Range4 := F (CI128);
               C160  : constant Mont_Range2 := F (CI160);
               C192  : constant Mont_Range  := F (CI192);
               C224  : constant Mont_Range  := F (CI224);
            begin
               F (CI0)   := C128 + C0;
               F (CI128) := FQMul (Zeta1, C128 - C0);

               F (CI32)  := C160 + C32;
               F (CI160) := FQMul (Zeta1, C160 - C32);

               F (CI64)  := C192 + C64;
               F (CI192) := FQMul (Zeta1, C192 - C64);

               F (CI96)  := C224 + C96;
               F (CI224) := FQMul (Zeta1, C224 - C96);
            end;
         end;

         pragma Loop_Invariant (for all K in I256 range 0     ..  J => F (K) in Mont_Range8);
         pragma Loop_Invariant (for all K in I256 range J + 1 .. 31 => F (K) in Mont_Range);

         pragma Loop_Invariant (for all K in I256 range 32         .. 32 + J => F (K) in Mont_Range4);
         pragma Loop_Invariant (for all K in I256 range 32 + J + 1 .. 63     => F (K) in Mont_Range);

         pragma Loop_Invariant (for all K in I256 range 64         .. 64 + J => F (K) in Mont_Range2);
         pragma Loop_Invariant (for all K in I256 range 64 + J + 1 .. 95     => F (K) in Mont_Range);

         pragma Loop_Invariant (for all K in I256 range 96         .. 96 + J => F (K) in Mont_Range2);
         pragma Loop_Invariant (for all K in I256 range 96 + J + 1 .. 127    => F (K) in Mont_Range);

         pragma Loop_Invariant (for all K in I256 range 128        .. 255 => F (K) in Mont_Range);

      end loop;
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

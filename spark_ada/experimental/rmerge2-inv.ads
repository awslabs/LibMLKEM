package RMerge2.Inv
  with SPARK_Mode => On
is
   --  Standard GS-based INTT implemented as per FIPS 203
   procedure INTT (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range),
          Post => (for all K in Index_256 => F (K) in Mont_Range);

   --  Optimized
   procedure INTTnew (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in I16),
          Post => (for all K in Index_256 => F (K) in I16);

   --  Optimized, with layer merging
   procedure INTTmerge (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in I16),
          Post => (for all K in Index_256 => F (K) in I16);

   --  Standard GS-based INTT implemented as per FIPS 203, C version
   procedure CINTT (F : in out Poly_Zq)
     with Global => null,
          Import,
          Convention => C,
          External_Name => "poly_intt",
          No_Inline;

   procedure Layer7 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range),
          Post => ((for all K in I32 range 0 .. 63 => F (K * 4)     in Mont_Range2) and
                   (for all K in I32 range 0 .. 63 => F (K * 4 + 1) in Mont_Range2) and
                   (for all K in I32 range 0 .. 63 => F (K * 4 + 2) in Mont_Range) and
                   (for all K in I32 range 0 .. 63 => F (K * 4 + 3) in Mont_Range));

   procedure InvertLayer7 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in I16),
          Post => (for all K in Index_256 => F (K) in Mont_Range);

   procedure Layer654 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range),
          Post => (for all K in Index_256 => F (K) in Mont_Range);

   procedure Layer54 (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range),
          Post => (for all K in Index_256 => F (K) in Mont_Range);

   procedure Layer54a (F : in out Poly_Zq)
     with Global => null,
          No_Inline,
          Pre  => (for all K in Index_256 => F (K) in Mont_Range2),
          Post => (for all K in Index_256 => F (K) in Mont_Range8);

end RMerge2.Inv;

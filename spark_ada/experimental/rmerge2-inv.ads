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
          Pre  => (for all K in Index_256 => F (K) in Mont_Range),
          Post => (for all K in Index_256 => F (K) in Mont_Range);

   --  Standard GS-based INTT implemented as per FIPS 203, C version
   procedure CINTT (F : in out Poly_Zq)
     with Global => null,
          Import,
          Convention => C,
          External_Name => "poly_intt",
          No_Inline;

end RMerge2.Inv;

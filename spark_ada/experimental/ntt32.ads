--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

with Interfaces; use Interfaces;
package NTT32
  with SPARK_Mode => On
is
   --===================================
   --  Experimental NTT implementations
   --===================================

   Q         : constant := 3329;

   -- Q_Minus_1 = 13*(2**8), so a round number in binary when used as a literal
   Q_Minus_1 : constant := 3328;

   subtype Byte is Unsigned_8;
   subtype I32  is Integer_32;
   subtype I64  is Integer_64;
   subtype U32  is Unsigned_32;
   subtype N32  is I32 range 0 .. I32'Last;

   subtype ZqI32 is I32 range 0 .. (Q - 1);
   subtype ZqU32 is U32 range 0 .. (Q - 1);

   subtype Index_256 is I32 range 0 .. 255;

   type UPoly_I32 is array (Index_256 range <>) of I32;
   subtype Poly_I32 is UPoly_I32 (Index_256);
   subtype Poly_Zq is Poly_I32
     with Dynamic_Predicate => (for all K in Index_256 => Poly_Zq (K) >= 0 and Poly_Zq (K) < Q);

   subtype NTT_Len_Power is Natural range 1 .. 7;

   --  A power of 2 between 2 and 128. Used in NTT and NTT_Inv
   subtype Len_T is Index_256
      with Dynamic_Predicate =>
         (for some I in NTT_Len_Power => Len_T = 2**I);

   --====================
   --  NTT
   --====================

   procedure NTT_Inner (F_Hat : in out Poly_Zq;
                        Zeta  : in     ZqI32;
                        Start : in     Index_256;
                        Len   : in     Len_T)
       with No_Inline,
            Global => null,
            Pre    => Start <= 252 and
                      Start + 2 * Len <= 256;

   --  Standard CT-based NTT implemented as per FIPS 203
   function NTT (F : in Poly_Zq) return Poly_Zq
     with Global => null,
          No_Inline;


   function MZq (Left, Right : in ZqU32) return ZqU32
     with Global => null,
          No_Inline,
          Post => MZq'Result = ZqU32 ((Left * Right) mod Q);

end NTT32;

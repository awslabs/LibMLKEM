--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

with SHA3;  use SHA3;
with SHAKE; use SHAKE;

package body MLKEM
  with SPARK_Mode => On
is
   --==============================================================================
   --  Notation, Naming and Operators
   --==============================================================================
   --
   --  This section lays out a few notational conventions for readers
   --  that might not be familiar with Ada or SPARK, and notes a few
   --  important differences between the notation used in FIPS 203 and
   --  that appearing here.
   --
   --  Assignment and Equality
   --  -----------------------
   --
   --  As in Pascal, SPARK uses ":=" for assignment and "=" for equality.
   --  The latter is predefined for most types, and always returns the predefined
   --  Boolean type. The "not equals" operator is denoted "/="
   --
   --  Concatenation
   --  -------------
   --
   --  FIPS 203 uses "||" for concatenation of sequences and/or arrays.
   --  In SPARK, all one-dimensional arrays have a predefined concatentation
   --  index operator, denoted "&".
   --
   --  Ranges and Array Slices
   --  -----------------------
   --
   --  Ranges of integers in SPARK (denoted "X .. Y") are _inclusive_
   --  at both ends. Similarly a "slice" of an array object, denoted
   --  A (X .. Y), is all the elements of A from the X'th to the Y'th
   --  element inclusive.
   --
   --  Naming
   --  ------
   --
   --  Where FIPS 203 uses accented characters such as the UNICODE code-point
   --  "Latin Capital A with Circumflex", this code uses a suffix on a simple
   --  name (e.g. "A_Hat" in this case) and sticks to the simple Latin_1 subset
   --  of the character set. Other than that, the code maintains the names of all
   --  types and variables from FIPS 203.
   --==============================================================================



   --  GNATProve generates false-alarms for the gnatwa.t warning ("suspicious contracts")
   --  when instantiating generics owing to a defect in the compiler front-end in
   --  GNAT versions up to and including 13.1.0. This problem will be corrected in GNAT Pro 25.0
   --  (See AdaCore TN CS0037963)
   pragma Warnings (GNATprove, Off, "postcondition does not mention function result");
   pragma Warnings (GNATprove, Off, "conjunct in postcondition does not check the outcome");


   --=======================================
   --  Local constants and types
   --=======================================

   --  Bytes_64 type is needed for SHA3
   subtype Index_64  is I32 range 0 .. 63;
   subtype Bytes_64  is Byte_Seq (Index_64);

   subtype U8_Bit is Unsigned_8 range 0 .. 1;

   package body Zq
     with SPARK_Mode => On
   is
      C      : constant := 2**37;
      Magic  : constant := C / Q;

      function "+" (Left, Right : in T) return T
      is
         R      : I32;
         Reduce : I32;
      begin
         --  At -O0 and -Og, GCC typically generates a branch for a
         --  predefined modular "+" operator, so we code
         --  explicitly here for constant time

         R := I32 (Left) + I32 (Right);
         pragma Assert (R >= 0 and R <= 2 * I32 (T'Last));

         Reduce := Boolean'Pos (R >= Q);

         R := R - (Reduce * Q);

         --  Prove that we can safely convert the answer back to type T...
         pragma Assert (R >= 0 and R < Q);
         --  ... and that the answer is correct
         pragma Assert (R = (I32 (Left) + I32 (Right)) mod Q);

         return T (R);
      end "+";

      function "-" (Left, Right : in T) return T
      is
         R      : I32;
         Reduce : I32;
      begin
         R := I32 (Left) - I32 (Right);
         pragma Assert (R > -Q and R < Q); --  R in -3228 .. 3228

         --  If R is negative, then we need to add Q, else add 0
         Reduce := Boolean'Pos (R < 0);
         R := R + (Reduce * Q);

         --  Prove that we can safely convert the answer back to type T...
         pragma Assert (R >= 0 and R < Q);
         --  ... and that the answer is correct
         pragma Assert (R = (I32 (Left) - I32 (Right)) mod Q);

         return T (R);
      end "-";

      function "*" (Left, Right : in T) return T
      is
         R2         : I64;
         R, R1, R3  : I32;
      begin
         --  We know that Left and Right and both < Q, so 16x16->32-bit multiplication
         --  is sufficient
         R1 := I32 (Left) * I32 (Right);

         --  Switch to 64-bit multiplication now
         R2 := I64 (R1) * Magic;

         --  Shift right by 37 places, and switch back to 32-bit from here on
         R3 := I32 (R2 / C);

         --  Lemma 1 - Given that Q is prime and R1 is the product of two numbers, both < Q,
         --            the it's impossible for (R1 / Q) * Q = R1
         --
         --  This Lemma is proved in Lean4 and HOL-Light in the file zq_multiply_proof.txt,
         --  so it is "Assumed" here.
         pragma Assume ((if Left /= 0 and Right /= 0 then (((R1 / Q) * Q) /= R1)));

         --  We know that Magic is rounded down, but Lemma 1 is strong enough to exclude
         --  the case where R3 = (R1 / Q) - 1, so we can infer...
         pragma Assert (R3 = R1 / Q);

         R := R1 - R3 * Q;

         --  From the definition of "mod", we can conclude
         --    R = R1 - (R1 / Q) * Q) = R1 mod Q
         --  so we have the right answer
         pragma Assert (T (R) = T (R1 mod Q));

         return T (R);
      end "*";

      function ModQ (X : in U16_12Bits) return T
      is
      begin
         --  X is in range 0 .. 4095, so a constant-time
         --  conditional subtract of Q suffices.
         return T (X - (Q * Boolean'Pos (X >= Q)));
      end ModQ;

      function Div2 (Right : in T) return T
      is
      begin
         --  Note that Interfaces.Shift_Right for U16 is intrinsic,
         --  so should generate exactly one instruction on most ISAs.
         return T (Shift_Right (U16 (Right), 1));
      end Div2;

   end Zq;

   --  Make everything in Zq directly visible from here on
   use Zq;

   type K_Range is range 0 .. K - 1;

   subtype Index_256 is I32 range 0 .. 255;
   type Poly_Zq is array (Index_256) of Zq.T;

   type Poly_Zq_Vector is array (K_Range) of Poly_Zq;

   --  Polynomials in the NTT domain are structurally identical to the
   --  above, but should never be mixed up with them, so we declare
   --  an explicitly derived named types for them here.
   type NTT_Poly_Zq is new Poly_Zq;
   type NTT_Poly_Zq_Vector is array (K_Range) of NTT_Poly_Zq;
   type NTT_Poly_Matrix    is array (K_Range) of NTT_Poly_Zq_Vector;




   subtype NTT_Len_Bit_Index is Natural range 0 .. 6;
   subtype NTT_Len_Power     is Natural range 1 .. 7;
   --  A power of 2 between 2 and 128. Used in NTT and NTT_Inv
   subtype Len_T is Index_256 range 2 .. 128
      with Dynamic_Predicate => (for some I in NTT_Len_Power => Len_T = 2**I);

   --  A power of 2 between 1 and 64. Used in NTT and NTT_Inv
   subtype Count_T is Index_256 range 1 .. 64
      with Dynamic_Predicate => (for some I in NTT_Len_Bit_Index => Count_T = 2**I);

   subtype Index_3   is I32 range 0 .. 2;
   subtype Index_8   is I32 range 0 .. 7;
   subtype Index_12  is I32 range 0 .. 11;
   subtype Index_384 is I32 range 0 .. 383;
   subtype Index_3072 is I32 range 0 .. 3071;
   subtype Index_Poly_UDU_Bytes is I32 range 0 .. ((N * DU * K) / 8 - 1);
   subtype Index_Poly_Zq_Vector_Bytes is I32 range 0 .. (384 * K - 1);

   subtype Index_UDU_Bytes is I32 range 0 .. (N * DU) / 8 - 1;
   subtype Bytes_UDU is Byte_Seq (Index_UDU_Bytes);

   subtype Index_UDV_Bytes is I32 range 0 .. (N * DV) / 8 - 1;
   subtype Bytes_UDV is Byte_Seq (Index_UDV_Bytes);

   subtype Bytes_3   is Byte_Seq (Index_3);
   subtype Bytes_384 is Byte_Seq (Index_384);

   subtype Poly_UDU_Bytes is Byte_Seq (Index_Poly_UDU_Bytes);
   subtype Poly_Zq_Vector_Bytes is Byte_Seq (Index_Poly_Zq_Vector_Bytes);

   --  Array of bits, bit each bit stored as a Byte, so
   --  ineffecient in terms of space
   type Bit_Seq is array (N32 range <>) of U8_Bit;

   subtype Bits_12 is Bit_Seq (Index_12);
   subtype Bits_256 is Bit_Seq (Index_256);
   subtype Bits_3072 is Bit_Seq (Index_3072);

   subtype Index_Bits_UDU is I32 range 0 .. (N * DU) - 1;
   subtype Bits_UDU is Bit_Seq (Index_Bits_UDU);

   subtype Index_Bits_UDV is I32 range 0 .. (N * DV) - 1;
   subtype Bits_UDV is Bit_Seq (Index_Bits_UDV);

   subtype Index_PRF_Eta_1_Bytes is I32 range 0 .. 64 * Eta_1 - 1;
   subtype PRF_Eta_1_Bytes is Byte_Seq (Index_PRF_Eta_1_Bytes);

   subtype Index_PRF_Eta_2_Bytes is I32 range 0 .. 64 * Eta_2 - 1;
   subtype PRF_Eta_2_Bytes is Byte_Seq (Index_PRF_Eta_2_Bytes);

   --------------------------------------------------
   --  Polynomials, plus Vectors and Matrices thereof
   --------------------------------------------------

   --  A DU-bit unsigned, modular type, but stored
   --  in 16 bits
   type UDU is mod 2**DU
     with Object_Size => 16;

   --  A DV-bit unsigned, modular type, but stored
   --  in 16 bits
   type UDV is mod 2**DV
     with Object_Size => 16;

   type Poly_UDU is array (Index_256) of UDU;
   type Poly_UDV is array (Index_256) of UDV;

   subtype Poly_Zq_Bit is Poly_Zq
     with Dynamic_Predicate =>
            (for all I in Poly_Zq_Bit'Range => Poly_Zq_Bit (I) in Zq_Bit);

   Null_NTT_Poly_Zq : constant NTT_Poly_Zq := (others => 0);

   type Poly_UDU_Vector is array (K_Range) of Poly_UDU;

   ------------------
   --  PKE Keys
   ------------------

   subtype PKE_Decryption_Key_Index is I32 range 0 .. (384 * K - 1);
   subtype PKE_Decryption_Key is Byte_Seq (PKE_Decryption_Key_Index);

   subtype PKE_Encryption_Key is MLKEM_Encapsulation_Key;

   type PKE_Key is record
      EK : PKE_Encryption_Key;
      DK : PKE_Decryption_Key;
   end record;


   --=======================================
   --  Local subprogram declarations
   --=======================================

   ----------------------------------
   --  BitsToBytes and BytesToBits
   --  See FIPS 203 4.2.1
   ----------------------------------

   --  Algorithm 3
   --  BitsToBytes is generic here over its parameter and return types
   --  so that each instantiation of it has definite/constrained types.
   --  This avoids the need for unconstrained parameters and return types,
   --  and this avoids the need for secondary stack and/or heap usage
   --  at run-time.
   generic
      type Bits_Index is range <>;
      type Some_Bits is array (Bits_Index) of U8_Bit;
      type Bytes_Index is range <>;
      type Some_Bytes is array (Bytes_Index) of Byte;
   function Generic_BitsToBytes (B : in Some_Bits) return Some_Bytes
     with No_Inline,
          Global => null,
          Pre    => B'First = 0 and
                    B'Length >= 8 and   --  at least 1 byte's worth
                    B'Length mod 8 = 0, --  an exact multiple of 8 bits
          Post   => Generic_BitsToBytes'Result'First = 0 and
                    Generic_BitsToBytes'Result'Length * 8 = B'Length and
                    Generic_BitsToBytes'Result'Length = B'Length / 8;

   --  Algorithm 4
   --  Similarly, BytesToBits is generic to avoid unconstrained types
   generic
      type Bytes_Index is range <>;
      type Some_Bytes is array (Bytes_Index) of Byte;
      type Bits_Index is range <>;
      type Some_Bits is array (Bits_Index) of U8_Bit;
   function Generic_BytesToBits (B : in Some_Bytes) return Some_Bits
     with No_Inline,
          Global => null,
          Pre    => B'First = 0 and
                    U32 (B'Length) <= U32 (I32'Last / 8),
          Post   => Generic_BytesToBits'Result'First = 0 and
                    Generic_BytesToBits'Result'Length = 8 * B'Length;

   --=======================================
   --  Local subprogram bodies
   --=======================================

   -----------------------------------------
   --  Basic mathematical operators on Zq.T,
   --  polynomials, plus vectors and
   --  matrices thereof
   -----------------------------------------

   function "+" (Left, Right : in NTT_Poly_Zq) return NTT_Poly_Zq
     with No_Inline,
          Post => (for all I in Index_256 => "+"'Result (I) = (Left (I) + Right (I)));

   function "+" (Left, Right : in NTT_Poly_Zq) return NTT_Poly_Zq
   is
      R : NTT_Poly_Zq with Relaxed_Initialization;
   begin
      for I in R'Range loop
         R (I) := Left (I) + Right (I); -- implicitly mod Q
         pragma Loop_Invariant
            (for all K in Index_256 range 0 .. I => R (K)'Initialized and then
                                                    R (K) = (Left (K) + Right (K)));
      end loop;

      return R;
   end "+";

   function "+" (Left, Right : in Poly_Zq) return Poly_Zq
     with No_Inline
   is
   begin
      return Poly_Zq (NTT_Poly_Zq (Left) + NTT_Poly_Zq (Right)); --  calls _memcpy()
   end "+";

   function "-" (Left, Right : in Poly_Zq) return Poly_Zq
     with No_Inline
   is
      R : Poly_Zq;
   begin
      for I in R'Range loop
         R (I) := Left (I) - Right (I); -- implicitly mod Q
      end loop;
      return R;
   end "-";

   function "+" (Left, Right : in NTT_Poly_Zq_Vector) return NTT_Poly_Zq_Vector
     with No_Inline
   is
      R : NTT_Poly_Zq_Vector;
   begin
      for I in R'Range loop
         R (I) := Left (I) + Right (I);
      end loop;
      return R;
   end "+";

   function "+" (Left, Right : in Poly_Zq_Vector) return Poly_Zq_Vector
     with No_Inline
   is
      R : Poly_Zq_Vector;
   begin
      for I in R'Range loop
         R (I) := Left (I) + Right (I);
      end loop;
      return R;
   end "+";


   --  All elements of Left, multiplied by Right (mod q)
   function "*" (Left  : in Poly_Zq;
                 Right : in Zq.T) return Poly_Zq
     with No_Inline
   is
      R : Poly_Zq;
   begin
      for I in R'Range loop
         R (I) := Left (I) * Right; --  implicitly mod q
      end loop;
      return R;
   end "*";

   ----------------------------------
   --  Pseudo-Random Function
   --  See FIPS 203 4.1
   ----------------------------------

   function PRF_Eta_1 (S : in Bytes_32;
                       B : in Byte) return PRF_Eta_1_Bytes
     with No_Inline
   is
      C : SHAKE256.Context;
      R : PRF_Eta_1_Bytes;
   begin
      SHAKE256.Init (C);
      SHAKE256.Update (C, SHAKE256.Byte_Array (S & B));
      SHAKE256.Extract (C, SHAKE256.Byte_Array (R));
      pragma  Unreferenced (C);
      return R;
   end PRF_Eta_1;

   function PRF_Eta_2 (S : in Bytes_32;
                       B : in Byte) return PRF_Eta_2_Bytes
     with No_Inline
   is
      C : SHAKE256.Context;
      R : PRF_Eta_2_Bytes;
   begin
      SHAKE256.Init (C);
      SHAKE256.Update (C, SHAKE256.Byte_Array (S & B));
      SHAKE256.Extract (C, SHAKE256.Byte_Array (R));
      pragma  Unreferenced (C);
      return R;
   end PRF_Eta_2;

   --  The function XOF is declared below
   --  as part of Algorithm 7

   ----------------------------------
   --  Hash functions, built on SHA3
   --  See FIPS 203 4.1
   ----------------------------------

   --  G returns a (32 bytes) followed by b (32 bytes)
   --  concatenated into 64 bytes.
   function G (C : in Byte_Seq) return Bytes_64
     with No_Inline,
          Global => null,
          Pre    => C'First = 0 and
                    C'Last <= I32 (Natural'Last - 1)
   is
      Ctx : SHA3_512.Context;
      R   : SHA3_512.Digest_Type;
   begin
      SHA3_512.Init (Ctx);
      SHA3_512.Update (Ctx, SHA3_512.Byte_Array (C));
      SHA3_512.Final (Ctx, R);
      pragma  Unreferenced (Ctx);
      return Bytes_64 (R);
   end G;

   function H (C : in Byte_Seq) return Bytes_32
     with No_Inline,
          Global => null,
          Pre    => C'First = 0 and
                    C'Last <= I32 (Natural'Last - 1)
   is
      Ctx : SHA3_256.Context;
      R   : SHA3_256.Digest_Type;
   begin
      SHA3_256.Init (Ctx);
      SHA3_256.Update (Ctx, SHA3_256.Byte_Array (C));
      SHA3_256.Final (Ctx, R);
      pragma  Unreferenced (Ctx);
      return Bytes_32 (R);
   end H;

   function J (C : in Byte_Seq) return Bytes_32
     with No_Inline,
          Global => null,
          Pre    => C'First = 0 and
                    C'Last <= I32 (Natural'Last - 1)
   is
      Ctx : SHAKE256.Context;
      R   : Bytes_32;
   begin
      SHAKE256.Init (Ctx);
      SHAKE256.Update (Ctx, SHAKE256.Byte_Array (C));
      SHAKE256.Extract (Ctx, SHAKE256.Byte_Array (R));
      pragma  Unreferenced (Ctx);
      return R;
   end J;




   function Generic_BitsToBytes (B : in Some_Bits) return Some_Bytes
   is
      R : Some_Bytes := Some_Bytes'(others => 0); --  calls _memset()
   begin
      for I in B'Range loop
         R (Bytes_Index (I / 8)) := R (Bytes_Index (I / 8)) +
                                    B (I) * (2 ** Natural (I mod 8));
      end loop;
      return R;
   end Generic_BitsToBytes;


   function Generic_BytesToBits (B : in Some_Bytes) return Some_Bits
   is
      R : Some_Bits := (others => 0); --  calls _memset()
      This_Byte : Byte;
   begin
      for I in B'Range loop
         This_Byte := B (I);
         for J in Index_8 loop
            R (8 * Bits_Index (I) + Bits_Index (J)) := This_Byte mod 2;
            This_Byte := This_Byte / 2;
         end loop;
      end loop;
      return R;
   end Generic_BytesToBits;

   -------------------------------------------------------
   --  Compression and Decompression
   --  Each function is declared overloaded several times
   --  for specific values of d and parameter types
   -------------------------------------------------------

   --  Barrett reduction constants used below
   Q_C : constant := 43;
   Q_M : constant := 2_642_262_849; --  round (2**Q_C / Q);

   function Compress1 (X : in Zq.T) return U8_Bit
     with No_Inline
   is
      T : U64;
   begin
      T := U64 (X) * 4 + Q;

      --  Division by (Q * 2) is first achieved by dividing by 2
      T := T / 2;
      --  Then multiplication by Q_M and a shift right by Q_C places
      T := T * Q_M;
      T := Shift_Right (T, Q_C);

      --  T might be in 0 .. 2 here, so a final reduction mod 2 is required
      T := T mod 2;
      return U8_Bit (T);
   end Compress1;

   function Compress1 (X : in Poly_Zq) return Bits_256
     with No_Inline
   is
      R : Bits_256;
   begin
      for I in X'Range loop
         R (I) := Compress1 (X (I));
      end loop;
      return R;
   end Compress1;

   function CompressDV (X : in Zq.T) return UDV
     with No_Inline
   is
      C : constant := UDV'Modulus;
      T : U64;
   begin
      --  Add Q to the top-line, so that subsequent truncating division
      --  by 2Q is effectively "round to nearest"
      --    round-to-nearest(CX / Q) =
      --    floor((CX + 0.5Q)/Q) =
      --    floor((2CX + Q)/2Q)
      T := U64 (X) * 2 * C + Q;

      --  Division by (Q * 2) is first achieved by dividing by 2
      T := T / 2;
      --  Then multiplication by Q_M and a shift right by Q_C places
      T := T * Q_M;
      T := Shift_Right (T, Q_C);

      --  To return a value in UDV, an explicit reduction is
      --  required here. This is missing in FIPS-203 Eq 4.5
      T := T mod C;
      return UDV (T);
   end CompressDV;

   function CompressDV (V : in Poly_Zq) return Poly_UDV
     with No_Inline
   is
      R : Poly_UDV;
   begin
      for I in V'Range loop
         R (I) := CompressDV (V (I));
      end loop;
      return R;
   end CompressDV;

   function CompressDU (X : in Zq.T) return UDU
     with No_Inline
   is
      C : constant := UDU'Modulus;
      T : U64;
   begin
      T := U64 (X) * 2 * C + Q;

      --  Division by (Q * 2) is first achieved by dividing by 2
      T := T / 2;
      --  Then multiplication by Q_M and a shift right by Q_C places
      T := T * Q_M;
      T := Shift_Right (T, Q_C);

      --  To return a value in UDV, an explicit reduction is
      --  required here. This is missing in FIPS-203 Eq 4.5
      T := T mod C;
      return UDU (T);
   end CompressDU;

   function CompressDU (V : in Poly_Zq) return Poly_UDU
     with No_Inline
   is
      R : Poly_UDU;
   begin
      for I in V'Range loop
         R (I) := CompressDU (V (I));
      end loop;
      return R;
   end CompressDU;

   function CompressDU (V : in Poly_Zq_Vector) return Poly_UDU_Vector
     with No_Inline
   is
      R : Poly_UDU_Vector;
   begin
      for I in V'Range loop
         R (I) := CompressDU (V (I));
      end loop;
      return R;
   end CompressDU;

   function Decompress1 (Y : in U8_Bit) return Zq.T
     with No_Inline
   is
      subtype RT is I32 range 0 .. 1665;
      T : RT;
   begin
      --  Round (Q / 2) = 1665
      --  0 -> 0
      --  1 -> 1665
      --  but implement in constant-time
      T := RT (Y) * 1665;
      return Zq.T (T);
   end Decompress1;

   --  Decompress a vector of Zq_Bit values
   function Decompress1 (Y : in Poly_Zq_Bit) return Poly_Zq
     with No_Inline
   is
      R : Poly_Zq;
   begin
      for I in R'Range loop
         R (I) := Decompress1 (U8_Bit (Y (I)));
      end loop;
      return R;
   end Decompress1;

   function DecompressDV (Y : in UDV) return Zq.T
     with No_Inline
   is
      C      : constant := 2**DV;
      Half_C : constant := C / 2;
      subtype Int_T is I32 range 0 .. (Q * I32 (UDV'Last) + Half_C);
      T : Int_T;
   begin
      T := Q * I32 (Y) + Half_C;
      T := T / C;

      pragma Assert (T >= 0);
      pragma Assert (T < Q);
      return Zq.T (T);
   end DecompressDV;

   function DecompressDV (Y : in Poly_UDV) return Poly_Zq
     with No_Inline
   is
      R : Poly_Zq;
   begin
      for I in R'Range loop
         R (I) := DecompressDV (Y (I));
      end loop;
      return R;
   end DecompressDV;

   function DecompressDU (Y : in UDU) return Zq.T
     with No_Inline
   is
      C : constant := UDU'Modulus;
      Half_C : constant := C / 2;

      subtype Int_T is I32 range 0 .. (Q * I32 (UDU'Last) + Half_C);
      T : Int_T;
   begin
      T := Q * I32 (Y) + Half_C;
      T := T / C;

      pragma Assert (T >= 0);
      pragma Assert (T < Q);
      return Zq.T (T);
   end DecompressDU;

   function DecompressDU (Y : in Poly_UDU) return Poly_Zq
     with No_Inline
   is
      R : Poly_Zq;
   begin
      for I in R'Range loop
         R (I) := DecompressDU (Y (I));
      end loop;
      return R;
   end DecompressDU;

   --  Overloaded. Applies DecompressDU to all elements of V
   function DecompressDU (V : in Poly_UDU_Vector) return Poly_Zq_Vector
     with No_Inline
   is
      R : Poly_Zq_Vector;
   begin
      for I in K_Range loop
         R (I) := DecompressDU (V (I));
      end loop;
      return R;
   end DecompressDU;

   -------------------------------------------------------
   --  Byte Encoding (Algorithm 5) and Decoding (Algorithm 6)
   --  Each function is declared overloaded several times
   --  for specific values of d and parameter types.
   -------------------------------------------------------

   --  256 1-bit digits is 256 bits, which is 32 bytes
   function ByteEncode1 (F : in Bits_256) return Bytes_32
     with No_Inline
   is
      function BitsToBytes is new Generic_BitsToBytes
        (Index_256, Bits_256, Index_32, Bytes_32);
   begin
      return BitsToBytes (F);
   end ByteEncode1;

   function ByteEncodeDV (F : in Poly_UDV) return Bytes_UDV
     with No_Inline
   is
      R : Bytes_UDV;
      B : Bits_UDV := (others => 0); --  calls _memset()
      A : UDV;
      This_Bit : UDV;

      function BitsToBytes is new Generic_BitsToBytes
        (Index_Bits_UDV, Bits_UDV, Index_UDV_Bytes, Bytes_UDV);
   begin
      for I in F'Range loop
         A := F (I);

         for J in I32 range 0 .. DV - 1 loop
            This_Bit := A mod 2;
            B (I * DV + J) := U8_Bit (This_Bit);
            A := (A - This_Bit) / 2;
         end loop;
      end loop;

      pragma Assert (B'Length = N * DV);
      R := BitsToBytes (B);
      return R;
   end ByteEncodeDV;

   function ByteEncodeDU (F : in Poly_UDU) return Bytes_UDU
     with No_Inline
   is
      R : Bytes_UDU;
      B : Bits_UDU := (others => 0); --  calls _memset()
      A : UDU;
      This_Bit : UDU;

      function BitsToBytes is new Generic_BitsToBytes
        (Index_Bits_UDU, Bits_UDU, Index_UDU_Bytes, Bytes_UDU);
   begin
      for I in F'Range loop
         A := F (I);

         for J in I32 range 0 .. DU - 1 loop
            This_Bit := A mod 2;
            B (I * DU + J) := U8_Bit (This_Bit);
            A := (A - This_Bit) / 2;
         end loop;

      end loop;
      pragma Assert (B'Length = N * DU);
      R := BitsToBytes (B);
      return R;
   end ByteEncodeDU;


   function ByteEncodeDU (F : in Poly_UDU_Vector) return Poly_UDU_Bytes
     with No_Inline
   is
      R : Poly_UDU_Bytes with Relaxed_Initialization;
      C : constant I32 := (N * DU) / 8;
   begin
      for I in K_Range loop
         R (I32 (I) * C .. (I32 (I) + 1) * C - 1) := ByteEncodeDU (F (I));
         pragma Loop_Invariant (R (0 .. (I32 (I) + 1) * C - 1)'Initialized);
      end loop;

      --  Substitute K for I + 1 in the loop invariant to get...
      pragma Assert (R (0 .. (K * C - 1))'Initialized);
      --  ...and therefore...
      pragma Assert (R'Initialized);
      return R;
   end ByteEncodeDU;


   function Bits_12_To_U16 (X : in Bits_12) return U16
   is (U16 (X (0)) +
       U16 (X (1)) * 2 +
       U16 (X (2)) * 4 +
       U16 (X (3)) * 8 +
       U16 (X (4)) * 16 +
       U16 (X (5)) * 32 +
       U16 (X (6)) * 64 +
       U16 (X (7)) * 128 +
       U16 (X (8)) * 256 +
       U16 (X (9)) * 512 +
       U16 (X (10)) * 1024 +
       U16 (X (11)) * 2048)
     with Ghost,
          Post => Bits_12_To_U16'Result < 4096;

   function Zq_To_Bits_12 (X : in Zq.T) return Bits_12
     with Post => Bits_12_To_U16 (Zq_To_Bits_12'Result) < Q
   is
      T : constant U16 := U16 (X);
   begin
      pragma Assert (T < Q);
      return Bits_12'(0  => U8_Bit (T and 1),
                      1  => U8_Bit (Shift_Right (T, 1) and 1),
                      2  => U8_Bit (Shift_Right (T, 2) and 1),
                      3  => U8_Bit (Shift_Right (T, 3) and 1),
                      4  => U8_Bit (Shift_Right (T, 4) and 1),
                      5  => U8_Bit (Shift_Right (T, 5) and 1),
                      6  => U8_Bit (Shift_Right (T, 6) and 1),
                      7  => U8_Bit (Shift_Right (T, 7) and 1),
                      8  => U8_Bit (Shift_Right (T, 8) and 1),
                      9  => U8_Bit (Shift_Right (T, 9) and 1),
                      10 => U8_Bit (Shift_Right (T, 10) and 1),
                      11 => U8_Bit (Shift_Right (T, 11) and 1));
   end Zq_To_Bits_12;

   function ByteEncode12 (F : in NTT_Poly_Zq) return Bytes_384
     with No_Inline
   is
      R : Bytes_384;
      B : Bits_3072 := (others => 0); --  calls _memset()

      function BitsToBytes is new Generic_BitsToBytes
        (Index_3072, Bits_3072, Index_384, Bytes_384);
   begin
      for I in F'Range loop
         B (I * 12 .. I * 12 + 11) := Zq_To_Bits_12 (F (I));
         pragma Assert (Bits_12_To_U16 (B (I * 12 .. I * 12 + 11)) < Q);
         pragma Loop_Invariant
           (for all K in Index_256 range 0 .. I =>
             (Bits_12_To_U16 (B (K * 12 .. K * 12 + 11)) < Q));
      end loop;

      pragma Assert
        (for all K in Index_256 =>
          (Bits_12_To_U16 (B (K * 12 .. K * 12 + 11)) < Q));

      R := BitsToBytes (B);
      return R;
   end ByteEncode12;

   --  Overloaded. Applies ByteEncode12 to all elements of V
   function ByteEncode12 (V : in NTT_Poly_Zq_Vector) return Poly_Zq_Vector_Bytes
     with No_Inline
   is
      R : Poly_Zq_Vector_Bytes with Relaxed_Initialization;
   begin
      for I in K_Range loop
         R (I32 (I) * 384 .. I32 (I) * 384 + 383) := ByteEncode12 (V (I));
         pragma Loop_Invariant (R (0 .. I32 (I) * 384 + 383)'Initialized);
      end loop;

      pragma Assert (R'Initialized);
      return R;
   end ByteEncode12;

   function ByteDecode1 (B : in Bytes_32) return Poly_Zq_Bit
     with No_Inline
   is
      function BytesToBits is new Generic_BytesToBits
        (Index_32, Bytes_32, Index_256, Bits_256);

      Bits : constant Bits_256 := BytesToBits (B);
      F : Poly_Zq_Bit := (others => 0); --  calls _memset()
   begin
      for I in F'Range loop
         F (I) := Zq_Bit (Bits (I));
         pragma Loop_Invariant (for all K in 0 .. I => F (K) in Zq_Bit);
      end loop;
      pragma Assert (F in Poly_Zq_Bit);
      return F;
   end ByteDecode1;

   function ByteDecodeDV (B : in Bytes_UDV) return Poly_UDV
     with No_Inline
   is
      function BytesToBits is new Generic_BytesToBits
        (Index_UDV_Bytes, Bytes_UDV, Index_Bits_UDV, Bits_UDV);

      Bits : constant Bits_UDV := BytesToBits (B);
      F : Poly_UDV;
      T : U16;

   begin
      for I in F'Range loop
         T := 0;
         for Bit in I32 range 0 .. DV - 1 loop
            T := T + U16 (Bits (I * DV + Bit)) * 2**Natural (Bit);
            pragma Loop_Invariant (T >= 0);
            pragma Loop_Invariant (T <= 2**Natural (Bit + 1) - 1);
         end loop;
         F (I) := UDV (T);
      end loop;
      return F;
   end ByteDecodeDV;

   function ByteDecodeDU (B : in Bytes_UDU) return Poly_UDU
     with No_Inline
   is
      function BytesToBits is new Generic_BytesToBits
        (Index_UDU_Bytes, Bytes_UDU, Index_Bits_UDU, Bits_UDU);

      Bits : constant Bits_UDU := BytesToBits (B);
      F : Poly_UDU;
      T : U16;
   begin
      for I in F'Range loop
         T := 0;
         for Bit in I32 range 0 .. DU - 1 loop
            T := T + U16 (Bits (I * DU + Bit)) * 2**Natural (Bit);
            pragma Loop_Invariant (T >= 0);
            pragma Loop_Invariant (T <= 2**Natural (Bit + 1) - 1);
         end loop;
         F (I) := UDU (T);
      end loop;
      return F;
   end ByteDecodeDU;

   function ByteDecodeDU (B : in Poly_UDU_Bytes) return Poly_UDU_Vector
     with No_Inline
   is
      R : Poly_UDU_Vector;
   begin
      for I in K_Range loop
         R (I) := ByteDecodeDU (B (I32 (I) * 32 * DU ..
                                  (I32 (I) + 1) * 32 * DU - 1));
      end loop;
      return R;
   end ByteDecodeDU;

   function ByteDecode12 (B : in Bytes_384) return NTT_Poly_Zq
     with No_Inline
   is
      function BytesToBits is new Generic_BytesToBits
        (Index_384, Bytes_384, Index_3072, Bits_3072);

      Bits : constant Bits_3072 := BytesToBits (B);
      F : NTT_Poly_Zq;
      T : U16_12Bits;
   begin
      for I in F'Range loop
         T := U16 (Bits (I * 12)) +
              U16 (Bits (I * 12 + 1)) * 2 +
              U16 (Bits (I * 12 + 2)) * 4 +
              U16 (Bits (I * 12 + 3)) * 8 +
              U16 (Bits (I * 12 + 4)) * 16 +
              U16 (Bits (I * 12 + 5)) * 32 +
              U16 (Bits (I * 12 + 6)) * 64 +
              U16 (Bits (I * 12 + 7)) * 128 +
              U16 (Bits (I * 12 + 8)) * 256 +
              U16 (Bits (I * 12 + 9)) * 512 +
              U16 (Bits (I * 12 + 10)) * 1024 +
              U16 (Bits (I * 12 + 11)) * 2048;
         F (I) := ModQ (T);
      end loop;
      return F;
   end ByteDecode12;

   function ByteDecode12 (B : in Poly_Zq_Vector_Bytes) return NTT_Poly_Zq_Vector
     with No_Inline
   is
      R : NTT_Poly_Zq_Vector;
   begin
      for I in K_Range loop
         R (I) := ByteDecode12 (B (384 * I32 (I) .. 384 * I32 (I) + 383));
      end loop;
      return R;
   end ByteDecode12;

   ----------------------------------
   --  NTT, NTT_Inv and Sampling
   ----------------------------------

   Max_Zeta  : constant := 3289;
   subtype Zeta_Entry is Zq.T range 0 .. Max_Zeta;
   type Zeta_Exp_Table_Type is array (SU7) of Zeta_Entry;

   Max_Gamma : constant := 3312;
   subtype Gamma_Entry is Zq.T range 0 .. Max_Gamma;
   type Gamma_Table_Type is array (Index_128) of Gamma_Entry;

   --  This table generated by MLKEM.Tests.Gen_Zeta_Exp_Table procedure
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

   --  This table generated by MLKEM.Tests.Gen_Gamma_Table procedure
   Gamma_Table : constant Gamma_Table_Type :=
     (0 => 17,
      1 => 3312,
      2 => 2761,
      3 => 568,
      4 => 583,
      5 => 2746,
      6 => 2649,
      7 => 680,
      8 => 1637,
      9 => 1692,
      10 => 723,
      11 => 2606,
      12 => 2288,
      13 => 1041,
      14 => 1100,
      15 => 2229,
      16 => 1409,
      17 => 1920,
      18 => 2662,
      19 => 667,
      20 => 3281,
      21 => 48,
      22 => 233,
      23 => 3096,
      24 => 756,
      25 => 2573,
      26 => 2156,
      27 => 1173,
      28 => 3015,
      29 => 314,
      30 => 3050,
      31 => 279,
      32 => 1703,
      33 => 1626,
      34 => 1651,
      35 => 1678,
      36 => 2789,
      37 => 540,
      38 => 1789,
      39 => 1540,
      40 => 1847,
      41 => 1482,
      42 => 952,
      43 => 2377,
      44 => 1461,
      45 => 1868,
      46 => 2687,
      47 => 642,
      48 => 939,
      49 => 2390,
      50 => 2308,
      51 => 1021,
      52 => 2437,
      53 => 892,
      54 => 2388,
      55 => 941,
      56 => 733,
      57 => 2596,
      58 => 2337,
      59 => 992,
      60 => 268,
      61 => 3061,
      62 => 641,
      63 => 2688,
      64 => 1584,
      65 => 1745,
      66 => 2298,
      67 => 1031,
      68 => 2037,
      69 => 1292,
      70 => 3220,
      71 => 109,
      72 => 375,
      73 => 2954,
      74 => 2549,
      75 => 780,
      76 => 2090,
      77 => 1239,
      78 => 1645,
      79 => 1684,
      80 => 1063,
      81 => 2266,
      82 => 319,
      83 => 3010,
      84 => 2773,
      85 => 556,
      86 => 757,
      87 => 2572,
      88 => 2099,
      89 => 1230,
      90 => 561,
      91 => 2768,
      92 => 2466,
      93 => 863,
      94 => 2594,
      95 => 735,
      96 => 2804,
      97 => 525,
      98 => 1092,
      99 => 2237,
      100 => 403,
      101 => 2926,
      102 => 1026,
      103 => 2303,
      104 => 1143,
      105 => 2186,
      106 => 2150,
      107 => 1179,
      108 => 2775,
      109 => 554,
      110 => 886,
      111 => 2443,
      112 => 1722,
      113 => 1607,
      114 => 1212,
      115 => 2117,
      116 => 1874,
      117 => 1455,
      118 => 1029,
      119 => 2300,
      120 => 2110,
      121 => 1219,
      122 => 2935,
      123 => 394,
      124 => 885,
      125 => 2444,
      126 => 2154,
      127 => 1175);



   --  Algorithm 7 - SampleNTT and XOF
   --  For this implementation, we combine XOF and SampleNTT
   --  into a single function. This avoids the need for XOF
   --  to return an unbounded sequence of bytes and/or some
   --  sort of lazy evaluation of an infinite sequence.
   subtype Index_34  is I32 range 0 .. 33;
   subtype Bytes_34  is Byte_Seq (Index_34);

   function XOF_Then_SampleNTT (B : in Bytes_34) return NTT_Poly_Zq
     with No_Inline
   is
      Ctx : SHAKE128.Context;
      J2  : Natural := 0;
      A   : NTT_Poly_Zq := (others => 0); --  calls _memset()
      C   : Bytes_3;
   begin
      --  Initialize and feed input data into the XOF function
      --  which is actually SHAKE128
      SHAKE128.Init (Ctx);
      SHAKE128.Update (Ctx, SHAKE128.Byte_Array (B));

      while J2 < 256 loop
         pragma Loop_Variant (Increases => J2);
         pragma Annotate (GNATprove,
                          False_Positive,
                          "loop variant might fail",
                          "Terminates with very high probability");

         --  To execute this loop body once, we need exactly 3 bytes of output
         --  from the XOF function, so we fetch that many, and keep
         --  looping until the sampling terminates
         SHAKE128.Extract (Ctx, SHAKE128.Byte_Array (C));
         declare
            D1  : constant U16 := U16 (C (0)) + (256 * (U16 (C (1)) mod 16));
            D2  : constant U16 := U16 (C (1)) / 16 + (16 * U16 (C (2)));
         begin
            if D1 < Q then
               A (Index_256 (J2)) := Zq.T (D1);
               J2 := J2 + 1;
            end if;
            if D2 < Q and J2 < 256 then
               A (Index_256 (J2)) := Zq.T (D2);
               J2 := J2 + 1;
            end if;
         end;
      end loop;
      return A;
   end XOF_Then_SampleNTT;


   --  Algorithm 8 - SamplePolyCBD2, specialized for Eta_1
   function SamplePolyCBD_Eta_1 (B : in PRF_Eta_1_Bytes) return Poly_Zq
     with No_Inline
   is
      subtype Index_PRF_Eta_1_Bits is I32 range 0 .. 8 * 64 * Eta_1 - 1;
      subtype PRF_Eta_1_Bits is Bit_Seq (Index_PRF_Eta_1_Bits);

      function BytesToBits is new Generic_BytesToBits
        (Index_PRF_Eta_1_Bytes, PRF_Eta_1_Bytes,
         Index_PRF_Eta_1_Bits, PRF_Eta_1_Bits);

      SB : constant PRF_Eta_1_Bits := BytesToBits (B);
      F  : Poly_Zq;

      subtype Bit_Sum is Natural range 0 .. Eta_1;

      function Sum_X (I : in Index_256) return Bit_Sum
        with No_Inline,
             Global => SB
      is
         R : Bit_Sum := 0;
      begin
         for J in Index_PRF_Eta_1_Bytes range 0 .. Eta_1 - 1 loop
            pragma Loop_Invariant (R >= 0);
            pragma Loop_Invariant (R <= Natural (J));
            R := R + Natural (SB (2 * I * Eta_1 + J));
         end loop;
         return R;
      end Sum_X;

      function Sum_Y (I : in Index_256) return Bit_Sum
        with No_Inline,
             Global => SB
      is
         R : Bit_Sum := 0;
      begin
         for J in Index_PRF_Eta_1_Bytes range 0 .. Eta_1 - 1 loop
            pragma Loop_Invariant (R >= 0);
            pragma Loop_Invariant (R <= Natural (J));
            R := R + Natural (SB (2 * I * Eta_1 + Eta_1 + J));
         end loop;
         return R;
      end Sum_Y;

   begin
      for I in Index_256 loop
         declare
            X : constant Bit_Sum := Sum_X (I);
            Y : constant Bit_Sum := Sum_Y (I);
         begin
            --  This "-" _is_ modulo Q
            F (I) := Zq.T (X) - Zq.T (Y); --  implicitly mod Q
         end;
      end loop;
      return F;
   end SamplePolyCBD_Eta_1;

   --  Algorithm 8 - SamplePolyCBD2, specialized for Eta_2
   function SamplePolyCBD_Eta_2 (B : in PRF_Eta_2_Bytes) return Poly_Zq
     with No_Inline
   is
      subtype Index_PRF_Eta_2_Bits is I32 range 0 .. 8 * 64 * Eta_2 - 1;
      subtype PRF_Eta_2_Bits is Bit_Seq (Index_PRF_Eta_2_Bits);

      function BytesToBits is new Generic_BytesToBits
        (Index_PRF_Eta_2_Bytes, PRF_Eta_2_Bytes,
         Index_PRF_Eta_2_Bits, PRF_Eta_2_Bits);

      SB : constant PRF_Eta_2_Bits := BytesToBits (B);
      F  : Poly_Zq;

      subtype Bit_Sum is Natural range 0 .. Eta_2;

      function Sum_X (I : in Index_256) return Bit_Sum
        with No_Inline,
             Global => SB
      is
         R : Bit_Sum := 0;
      begin
         for J in Index_PRF_Eta_2_Bytes range 0 .. Eta_2 - 1 loop
            pragma Loop_Invariant (R >= 0);
            pragma Loop_Invariant (R <= Natural (J));
            R := R + Natural (SB (2 * I * Eta_2 + J));
         end loop;
         return R;
      end Sum_X;

      function Sum_Y (I : in Index_256) return Bit_Sum
        with No_Inline,
             Global => SB
      is
         R : Bit_Sum := 0;
      begin
         for J in Index_PRF_Eta_2_Bytes range 0 .. Eta_2 - 1 loop
            pragma Loop_Invariant (R >= 0);
            pragma Loop_Invariant (R <= Natural (J));
            R := R + Natural (SB (2 * I * Eta_2 + Eta_2 + J));
         end loop;
         return R;
      end Sum_Y;
   begin
      for I in Index_256 loop
         declare
            X : constant Bit_Sum := Sum_X (I);
            Y : constant Bit_Sum := Sum_Y (I);
         begin
            --  This "-" _is_ modulo Q
            F (I) := Zq.T (X) - Zq.T (Y); --  implicitly mod Q
         end;
      end loop;
      return F;
   end SamplePolyCBD_Eta_2;


   --  Algorithm 9
   function NTT (F : in Poly_Zq) return NTT_Poly_Zq
     with No_Inline
   is
      subtype K_T is Byte range 1 .. 128;
      F_Hat : NTT_Poly_Zq;
      K     : K_T;
      Len   : Len_T;
      Count : Count_T;

      procedure NTT_Inner (Zeta  : in     Zq.T;
                           Start : in     Index_256)
        with No_Inline,
             Global => (In_Out => F_Hat,
                        Input  => Len),
             Pre    => Start <= 252 and
                       Start + 2 * Len <= 256
      is
         T : Zq.T;
      begin
         for J in Index_256 range Start .. Start + (Len - 1) loop
            T               := Zeta * F_Hat (J + Len);
            F_Hat (J + Len) := F_Hat (J) - T;
            F_Hat (J)       := F_Hat (J) + T;
         end loop;
      end NTT_Inner;

   begin
      F_Hat := NTT_Poly_Zq (F); --  calls _memcpy()
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
            NTT_Inner (Zeta  => Zeta_ExpC (K),
                       Start => J * 2 * Len);
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
      pragma Assert (I32 (K) = 128);
      pragma Assert (K = 128);
      return F_Hat; --  calls _memcpy()
   end NTT;

   --  Overloaded - applies NTT to all elements of V
   function NTT (V : in Poly_Zq_Vector) return NTT_Poly_Zq_Vector
     with No_Inline
   is
      R : NTT_Poly_Zq_Vector;
   begin
      for I in R'Range loop
         R (I) := NTT (V (I));
      end loop;
      return R;
   end NTT;

   --  Algorithm 10
   function NTT_Inv (F : in NTT_Poly_Zq) return Poly_Zq
     with No_Inline
   is
      subtype K_T is Byte range 0 .. 127;
      F_Hat : Poly_Zq;
      K     : K_T;
      Len   : Len_T;
      Count : Count_T;

      procedure NTT_Inv_Inner (Zeta  : in     Zq.T;
                               Start : in     Index_256)
        with No_Inline,
             Global => (In_Out => F_Hat,
                        Input => Len),
             Pre    => Start <= 252 and
                       Start + 2 * Len <= 256
      is
         T : Zq.T;
      begin
         for J in Index_256 range Start .. Start + (Len - 1) loop
            T := F_Hat (J);
            F_Hat (J) := T + F_Hat (J + Len);
            F_Hat (J + Len) := Zeta * (F_Hat (J + Len) - T);
         end loop;
      end NTT_Inv_Inner;
   begin
      F_Hat := Poly_Zq (F); --  calls _memcpy()
      K     := 127;

      --  note "reverse" loop here for NTT_Inv
      for I in reverse NTT_Len_Bit_Index loop
         --  When I = 6, Len =   2, Count = 64
         --       I = 5, Len =   4, Count = 32
         --       ...
         --       I = 0, Len = 128, Count = 1
         Len   := 2**(7 - I);
         Count := 2**I;
         for J in I32 range 0 .. Count - 1 loop
            pragma Loop_Invariant (Count * Len = 128);
            --  A bit of spoon-feeding the prover here to help it work
            --  out that J * 2 * Len <= 252
            pragma Loop_Invariant (J <= Count - 1);
            pragma Loop_Invariant (J * 2 <= (Count - 1) * 2);
            pragma Loop_Invariant (J * 2 * Len <= (Count - 1) * 2 * Len);
            pragma Loop_Invariant (J * 2 * Len <= Count * 2 * Len - 2 * Len);
            pragma Loop_Invariant (J * 2 * Len <= 2**I * 2 * 2**(7 - I) - 2 * 2**(7 - I));
            pragma Loop_Invariant (J * 2 * Len <= 256 - 2 * 2**(7 - I));
            pragma Loop_Invariant (J * 2 * Len <= 256 - 2**(8 - I));
            pragma Loop_Invariant (J * 2 * Len <= 252);

            pragma Loop_Invariant (I32 (K) = 2**I + Count - J - 1);

            NTT_Inv_Inner (Zeta  => Zeta_ExpC (K),
                           Start => J * 2 * Len);
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

   --  Overloaded - applies NTT to all elements of V
   function NTT_Inv (V : in NTT_Poly_Zq_Vector) return Poly_Zq_Vector
     with No_Inline
   is
      R : Poly_Zq_Vector;
   begin
      for I in R'Range loop
         R (I) := NTT_Inv (V (I));
      end loop;
      return R;
   end NTT_Inv;


   --  Algorithms 11 and 12
   --  BaseCaseMultiply is inlined here in MultiplyNTTs
   function MultiplyNTTs (F, G : in NTT_Poly_Zq) return NTT_Poly_Zq
     with No_Inline
   is
      H : NTT_Poly_Zq with Relaxed_Initialization;
   begin
      for I in Index_128 loop
         declare
            A0    : constant Zq.T := F (2 * I);
            A1    : constant Zq.T := F (2 * I + 1);
            B0    : constant Zq.T := G (2 * I);
            B1    : constant Zq.T := G (2 * I + 1);
            Gamma : constant Zq.T := Gamma_Table (I);
            B1G   : constant Zq.T := B1 * Gamma;
         begin
            H (2 * I)     := (A0 * B0) + (A1 * B1G);
            H (2 * I + 1) := (A0 * B1) + (A1 * B0);
         end;
         pragma Loop_Invariant
           (for all K in Index_256 range 0 .. I * 2 + 1 => H (K)'Initialized);
      end loop;
      return H;
   end MultiplyNTTs;

   --  FIPS 203 2.4.7 defines a "dot product" operator between
   --  matrices and vectors of Poly_Zq, so we declare it thus:
   function "*" (Left  : in NTT_Poly_Matrix;
                 Right : in NTT_Poly_Zq_Vector) return NTT_Poly_Zq_Vector
     with No_Inline
   is
      R : NTT_Poly_Zq_Vector with Relaxed_Initialization;
   begin
      for I in K_Range loop
         --  Unroll the first iteration of the inner loop to avoid
         --  need to pre-initialize R with all 0 values
         R (I) := MultiplyNTTs (Left (I) (0), Right (0));

         pragma Loop_Invariant (for all P in K_Range range 0 .. I => R (P)'Initialized);

         for J in K_Range range 1 .. K_Range'Last loop

            pragma Loop_Invariant (for all P in K_Range range 0 .. I => R (P)'Initialized);

            R (I) := R (I) + MultiplyNTTs (Left (I) (J), Right (J));
         end loop;
      end loop;

      return R;
   end "*";

   --  Dot product of K-length vectors of NTT_Poly_Zq.
   --  third equation
   function "*" (Left  : in NTT_Poly_Zq_Vector;
                 Right : in NTT_Poly_Zq_Vector) return NTT_Poly_Zq
     with No_Inline
   is
      R : NTT_Poly_Zq;
   begin
      --  Unroll the first iteration of the loop to avoid
      --  need to pre-initialize R with all 0 values
      R := MultiplyNTTs (Left (0), Right (0));
      for J in K_Range range 1 .. K_Range'Last loop
         R := R + MultiplyNTTs (Left (J), Right (J));
      end loop;
      return R;
   end "*";



   -------------------------------------
   --  K-PKE KeyGen, Encrypt and Decrypt
   -------------------------------------

   function Transpose (X : in NTT_Poly_Matrix) return NTT_Poly_Matrix
     with No_Inline
   is
      T : NTT_Poly_Matrix := (others => (others => Null_NTT_Poly_Zq)); --  calls _memset()
   begin
      for I in K_Range loop
         for J in K_Range loop
            T (J) (I) := X (I) (J); --  calls _memcpy()
         end loop;
      end loop;
      return T;
   end Transpose;

   --  Generating the A_Hat matrix is common to K_PKE_KeyGen and
   --  K_PKE_Encrypt, so is factored out here
   procedure Generate_A_Hat_Matrix (Rho   : in     Bytes_32;
                                    A_Hat :    out NTT_Poly_Matrix)
     with Relaxed_Initialization => A_Hat,
          Post => A_Hat'Initialized
   is
   begin
      --  In order to avoid a double-initialization of A_Hat, we prove
      --  safe initialization of A_Hat by proof here, rather than using
      --  the PDG flow-analysis engine.  Therefore, A_Hat is marked
      --  with the "Relaxed_Initialization" aspect, and loop
      --  invariants are used to track initialization of each slice
      --  and element of A_Hat.
      for I in K_Range loop
         for J in K_Range loop
            A_Hat (I) (J) := XOF_Then_SampleNTT (Rho & Byte (J) & Byte (I));

            --  The first I-1 slices of R are fully initialized and
            --  the first J elements of slice I are initialized
            pragma Loop_Invariant (A_Hat (K_Range'First .. I - 1)'Initialized and
                                   A_Hat (I) (K_Range'First .. J)'Initialized);

         end loop;

         --  The first I slices of A_Hat are fully initialized
         pragma Loop_Invariant (A_Hat (K_Range'First .. I)'Initialized);

      end loop;

      --  All slices of R are now initialized...
      pragma Assert (A_Hat (K_Range'First .. K_Range'Last)'Initialized);
      --  ...and therefore
      pragma Assert (A_Hat'Initialized);
   end Generate_A_Hat_Matrix;

   --  Generating a Poly_Zq_Vector with Eta_1 is common to K_PKE_KeyGen and
   --  K_PKE_Encrypt, so is factored out here
   procedure Generate_Poly_Zq_Vector_With_Eta_1
      (Sigma     : in     Bytes_32;
       Initial_N : in     Byte;
       V         :    out Poly_Zq_Vector)
     with Pre => Initial_N = 0 or Initial_N = K
   is
      N : Byte := Initial_N;
   begin
      for I in K_Range loop
         pragma Loop_Invariant (N = Initial_N + Byte (I));
         V (I) := SamplePolyCBD_Eta_1 (PRF_Eta_1 (Sigma, N));
         N := N + 1;
      end loop;
   end Generate_Poly_Zq_Vector_With_Eta_1;

   --  Generating a Poly_Zq_Vector with Eta_2 is common to K_PKE_KeyGen and
   --  K_PKE_Encrypt, so is factored out here
   procedure Generate_Poly_Zq_Vector_With_Eta_2
      (Sigma     : in     Bytes_32;
       V         :    out Poly_Zq_Vector)
   is
      N : Byte := K;
   begin
      for I in K_Range loop
         pragma Loop_Invariant (N = K + Byte (I));
         V (I) := SamplePolyCBD_Eta_2 (PRF_Eta_2 (Sigma, N));
         N := N + 1;
      end loop;
   end Generate_Poly_Zq_Vector_With_Eta_2;

   --  Algorithm 13, FIPS 203 5.1
   function K_PKE_KeyGen (Random_D : in Bytes_32) return PKE_Key
     is separate;

   --  Algorithm 14, FIPS 203 5.2
   function K_PKE_Encrypt (EK_PKE   : in PKE_Encryption_Key;
                           M        : in Bytes_32;
                           Random_R : in Bytes_32) return Ciphertext
   is
      A_Hat : NTT_Poly_Matrix;

      Y, E1, U     : Poly_Zq_Vector;
      Y_Hat, T_Hat : NTT_Poly_Zq_Vector;

      E2, V, Mu : Poly_Zq;
      Rho       : Bytes_32;
      C1        : Poly_UDU_Bytes;
      C2        : Bytes_UDV;
   begin
      T_Hat := ByteDecode12 (EK_PKE (0 .. 384 * K - 1));
      Rho := EK_PKE (384 * K .. EK_PKE'Last); --  Should be exactly 32 bytes

      Generate_A_Hat_Matrix (Rho, A_Hat);
      Generate_Poly_Zq_Vector_With_Eta_1 (Random_R, 0, Y);
      Generate_Poly_Zq_Vector_With_Eta_2 (Random_R, E1);

      E2 := SamplePolyCBD_Eta_2 (PRF_Eta_2 (Random_R, K * 2));
      Y_Hat := NTT (Y);

      U := NTT_Inv (Transpose (A_Hat) * Y_Hat) + E1;

      Mu := Decompress1 (ByteDecode1 (M));
      V := NTT_Inv (T_Hat * Y_Hat) + E2 + Mu;

      C1 := ByteEncodeDU (CompressDU (U));
      C2 := ByteEncodeDV (CompressDV (V));
      return C1 & C2; --  calls _memcpy()
   end K_PKE_Encrypt;


   --  Algorithm 15, FIPS 203 5.3
   function K_PKE_Decrypt (DK_PKE   : in PKE_Decryption_Key;
                           C        : in Ciphertext) return Bytes_32
     with No_Inline
   is
      C1     : Poly_UDU_Bytes;
      C2     : Bytes_UDV;
      U_Tick : Poly_Zq_Vector;
      S_Hat  : NTT_Poly_Zq_Vector;
      V_Tick : Poly_Zq;
      W      : Poly_Zq;
      M      : Bytes_32;
   begin
      C1 := C (0 .. 32 * DU * K - 1); --  calls _memcpy()
      C2 := C (32 * DU * K .. 32 * (DU * K + DV) - 1);

      U_Tick := DecompressDU (ByteDecodeDU (C1));
      V_Tick := DecompressDV (ByteDecodeDV (C2));

      S_Hat := ByteDecode12 (DK_PKE);

      W := V_Tick - NTT_Inv (S_Hat * NTT (U_Tick));

      M := ByteEncode1 (Compress1 (W));
      return M;
   end K_PKE_Decrypt;

   --  Constant time equality test for unconstrained Byte_Seq's, where
   --  bounds match exactly.
   function Byte_Seq_Equal (X, Y : in Byte_Seq) return Boolean
     with No_Inline,
          Global => null,
          Pre    => X'First = Y'First and
                    X'Last  = Y'Last and
                    X'Length >= 1 and
                    Y'Length >= 1 and
                    X'Length = Y'Length,
          Post   => Byte_Seq_Equal'Result =
                      (for all I in X'Range => X (I) = Y (I));

   function Byte_Seq_Equal (X, Y : in Byte_Seq) return Boolean
   is
      D : Boolean := True;
      I : N32 := X'First;
   begin
      --  Explicit loop statement here to avoid dead branch that
      --  a "for" loop generates when X'Length = 0
      loop
         D := D and (X (I) = Y (I));
         pragma Loop_Invariant
           (I >= X'First and I <= X'Last and
            (D = (for all J in N32 range X'First .. I => X (J) = Y (J))));
         pragma Loop_Variant (Increases => I);
         exit when I = X'Last;
         I := I + 1;
      end loop;
      return D;
   end Byte_Seq_Equal;


   --=======================================
   --  Exported subprogram bodies
   --=======================================

   --  FIPS 203 section 7.2
   function EK_Valid_For_Encaps (EK_Bar : in MLKEM_Encapsulation_Key)
     return Boolean
   is
      Key_To_Check : constant Poly_Zq_Vector_Bytes := EK_Bar (0 .. 384 * K - 1);
      Decoded      : NTT_Poly_Zq_Vector;
      Reencoded    : Poly_Zq_Vector_Bytes;
   begin
      --  FIPS 203 7.2 - Encapsulation key check
      --    1. Type check. Check on the length of EK is a static type-check in SPARK, so
      --       nothing to do here.
      --    2. Modulus check - check that Decode/Encode is idempotent:
      Decoded := ByteDecode12 (Key_To_Check);
      Reencoded := ByteEncode12 (Decoded);
      return Byte_Seq_Equal (Key_To_Check, Reencoded);
   end EK_Valid_For_Encaps;

   --  FIPS 203 section 7.3 - Decapsulation key and Ciphertext check
   function DK_Valid_For_Decaps (DK_Bar : in MLKEM_Decapsulation_Key)
     return Boolean
   is
      subtype Hash_Data_Index is I32 range 0 .. 384 * K + 31;
      subtype Hash_Data is Byte_Seq (Hash_Data_Index);

      HD : constant Hash_Data := Hash_Data (DK_Bar (384 * K .. 768 * K + 31));
      Test, Reference_Hash : Bytes_32;
   begin
      --  FIPS 203 7.3 - Decapsulation key check
      --    1. Ciphertext type check. This is a static type-check in SPARK,
      --       so nothing to do here.
      --    2. Decapsulation key type check. This is a static type-check in
      --       SPARK, so nothing to do here.
      --    3. Hash check, as follows:
      Test           := H (HD);
      Reference_Hash := Bytes_32 (DK_Bar (768 * K + 32 .. 768 * K + 63));

      return Byte_Seq_Equal (Test, Reference_Hash);
   end DK_Valid_For_Decaps;

   --  FIPS 203 section 7.1
   function Key_Pair_Is_Consistent_With_Seed
      (Key_Pair : in MLKEM_Key;
       Random_D : in Bytes_32;
       Random_Z : in Bytes_32) return Boolean
   is
      Regenerated_Key : MLKEM_Key;
   begin
      Regenerated_Key := MLKEM_KeyGen (Random_D, Random_Z);
      return Byte_Seq_Equal (Key_Pair.EK, Regenerated_Key.EK) and
             Byte_Seq_Equal (Key_Pair.DK, Regenerated_Key.DK);
   end Key_Pair_Is_Consistent_With_Seed;


   --  FIPS 203 section 7.1 "Key pair check (without seed)"
   function Key_Pair_Check_Without_Seed
      (Key_Pair : in MLKEM_Key;
       Random_M : in Bytes_32) return Boolean
   is
      Key          : Bytes_32;
      Key_Tick     : Bytes_32;
      C            : Ciphertext;
   begin
      --  We can only call MLKEM_Encaps and MLKEM_Decaps if
      --  we know that DK and EK really are valid first.
      if (DK_Valid_For_Decaps (Key_Pair.DK) and
          EK_Valid_For_Encaps (Key_Pair.EK)) then

         --  Now we can do the Pair-wise consistency check. Section 7.1 (4)
         MLKEM_Encaps (Key_Pair.EK, Random_M, Key, C);
         Key_Tick := MLKEM_Decaps (C, Key_Pair.DK);
         return Byte_Seq_Equal (Key, Key_Tick);
      else
         return False;
      end if;
   end Key_Pair_Check_Without_Seed;


   --  FIPS 203 section 7.1 "Key pair check (with seed)"
   function Key_Pair_Check_With_Seed
      (Key_Pair : in MLKEM_Key;
       Random_D : in Bytes_32;
       Random_Z : in Bytes_32;
       Random_M : in Bytes_32) return Boolean
   is
   begin
      return (Key_Pair_Is_Consistent_With_Seed (Key_Pair, Random_D, Random_Z) and
              Key_Pair_Check_Without_Seed (Key_Pair, Random_M));
   end Key_Pair_Check_With_Seed;

   -- This is also ML-KEM.KeyGen_internal from FIPS 203 Algorithm 16
   function MLKEM_KeyGen (Random_D : in Bytes_32;
                          Random_Z : in Bytes_32) return MLKEM_Key
   is
      PKE_K : PKE_Key;
      DK    : MLKEM_Decapsulation_Key;
      HEK   : Bytes_32;
   begin
      PKE_K := K_PKE_KeyGen (Random_D); --  calls _memcpy()
      HEK := H (PKE_K.EK);
      DK := Byte_Seq (PKE_K.DK) & --  calls _memcpy() several times
            Byte_Seq (PKE_K.EK) &
            HEK &
            Random_Z;

      return MLKEM_Key'(EK => PKE_K.EK, --  calls _memcpy()
                        DK => DK);
   end MLKEM_KeyGen;


   -- This is also ML-KEM.Encaps_internal from FIPS 203 Algorithm 17
   procedure MLKEM_Encaps (EK       : in     MLKEM_Encapsulation_Key;
                           Random_M : in     Bytes_32;
                           Key      :    out Bytes_32;
                           C        :    out Ciphertext)
   is
      KR : Bytes_64;
   begin
      KR  := G (Random_M & H (EK));
      Key := KR (0 .. 31);
      C   := K_PKE_Encrypt (EK, Random_M, Bytes_32 (KR (32 .. 63))); --  calls _memcpy()
   end MLKEM_Encaps;

   -- This is also ML-KEM.Encaps_internal from FIPS 203 Algorithm 18
   function MLKEM_Decaps (C  : in Ciphertext;
                          DK : in MLKEM_Decapsulation_Key) return Bytes_32
   is
      DK_PKE : PKE_Decryption_Key;
      EK_PKE : PKE_Encryption_Key;
      H      : Bytes_32;
      Z      : Bytes_32;
      M_Tick : Bytes_32;
      K_Bar  : Bytes_32;
      KR     : Bytes_64;
      C_Tick : Ciphertext;

      Result : Bytes_32;

      --  Constant time conditional swap of Result and K_Bar.
      --  For illustration, this procedure is proven correct
      --  with the following Contract_Cases postcondition.
      procedure CSwap (Swap : in Boolean)
        with Global => (In_Out => (Result, K_Bar)),
             No_Inline,
             Contract_Cases =>
               (Swap     => (K_Bar = Result'Old and Result = K_Bar'Old),
                not Swap => (K_Bar = K_Bar'Old  and Result = Result'Old));

      procedure CSwap (Swap : in Boolean)
      is
         -- Conditional swap from Hacker's Delight 2-19
         T : Byte;
         C : constant Byte := 16#FF# * Boolean'Pos (Swap);
      begin
         for I in Index_32 loop
            T := C and (K_Bar (I) xor Result (I));
            K_Bar (I) := K_Bar (I) xor T;
            Result (I) := Result (I) xor T;

            pragma Loop_Invariant
              (if Swap then
                 (for all J in Index_32 range 0 .. I =>
                      (K_Bar (J) = Result'Loop_Entry (J) and
                       Result (J) = K_Bar'Loop_Entry (J)))
               else
                 (for all J in Index_32 range 0 .. I =>
                      (K_Bar (J) = K_Bar'Loop_Entry (J) and
                       Result (J) = Result'Loop_Entry (J)))
              );
         end loop;
      end CSwap;

   begin
      DK_PKE := PKE_Decryption_Key (DK (0 .. 384 * K - 1)); --  calls _memcpy()
      EK_PKE := PKE_Encryption_Key (DK (384 * K .. 768 * K + 32 - 1)); --  calls _memcpy()
      H      := Bytes_32 (DK (768 * K + 32 .. 768 * K + 64 - 1));
      Z      := Bytes_32 (DK (768 * K + 64 .. 768 * K + 96 - 1));

      M_Tick := K_PKE_Decrypt (DK_PKE, C);
      KR     := G (M_Tick & H);

      K_Bar  := J (Z & C); --  calls _memcpy()

      C_Tick := K_PKE_Encrypt (EK_PKE, M_Tick, Bytes_32 (KR (32 .. 63)));

      Result := KR (0 .. 31);

      --  if C /= C_Tick then swap K_Bar into Result.
      --  This fulfills the FIPS-203 spec for implicit rejection
      --  but does so in constant time.
      CSwap (not Byte_Seq_Equal (C, C_Tick));

      pragma Unreferenced (K_Bar);
      return Result;
   end MLKEM_Decaps;

end MLKEM;

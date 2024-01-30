--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

with Ada.Real_Time; use Ada.Real_Time;
with Ada.Text_IO;   use Ada.Text_IO;
with Interfaces;    use Interfaces;

with MLKEM;       use MLKEM;

procedure TKeyGen
is
   subtype Index_48  is I32 range 0 .. 47;
   subtype Bytes_48  is Byte_Seq (Index_48);
   Null_Bytes_48 : constant Bytes_48 := (others => 0);

   Null_Bytes_32 : constant Bytes_32 := (others => 0);


   type MLKEM_KAT is record
      --  KAT inputs and expected results read from the file
      Count        : Natural;
      Z            : Bytes_32;
      D            : Bytes_32;
      Msg          : Bytes_32;
      Seed         : Bytes_48;
      Expected_PK  : MLKEM_Encapsulation_Key;
      Expected_SK  : MLKEM_Decapsulation_Key;
      Expected_CT  : Ciphertext;
      Expected_SS  : Bytes_32;

      --  Computed results
      Computed_PK  : MLKEM_Encapsulation_Key;
      Computed_SK  : MLKEM_Decapsulation_Key;
      Computed_CT  : Ciphertext;
      Computed_SS1 : Bytes_32;
      Computed_SS2 : Bytes_32;
   end record;

   Null_MLKEM_KAT : constant MLKEM_KAT :=
     (Count        => 0,
      Z            => Null_Bytes_32,
      D            => Null_Bytes_32,
      Msg          => Null_Bytes_32,
      Seed         => Null_Bytes_48,

      Expected_PK  => (others => 0),
      Expected_SK  => (others => 0),
      Expected_CT  => (others => 0),
      Expected_SS  => Null_Bytes_32,

      Computed_PK  => (others => 0),
      Computed_SK  => (others => 0),
      Computed_CT  => (others => 0),
      Computed_SS1 => Null_Bytes_32,
      Computed_SS2 => Null_Bytes_32);

   TK  : MLKEM_KAT;

   function String_To_Bytes (S : in String) return Byte_Seq
     with Pre =>  S'Length mod 2 = 0,
          Post => S'Length = String_To_Bytes'Result'Length * 2 and
                  String_To_Bytes'Result'First = 0;

   function String_To_Bytes (S : in String) return Byte_Seq
   is
      subtype R_Index is I32 range 0 .. (S'Length / 2) - 1;
      subtype R_Type is Byte_Seq (R_Index);
      subtype Nibble is Byte range 0 .. 15;
      function CtoI (C : in Character) return Nibble;

      function CtoI (C : in Character) return Nibble
      is
      begin
         case C is
            when '0' .. '9' => return Character'Pos (C) -
                                      Character'Pos ('0');

            when 'A' .. 'F' => return Character'Pos (C) -
                                      Character'Pos ('A') + 10;

            when 'a' .. 'f' => return Character'Pos (C) -
                                      Character'Pos ('a') + 10;

            when others => raise Program_Error;
         end case;
      end CtoI;

      R : R_Type := (others => 0);
      J : Positive := S'First;
   begin
      for I in R'Range loop
         R (I) := CtoI (S (J)) * 16 + CtoI (S (J + 1));
         J := J + 2;
      end loop;
      return R;
   end String_To_Bytes;

   procedure Read_KeyGen_KAT;
   procedure Run_KeyGen_KAT;

   procedure Read_KeyGen_KAT
   is
   begin
      TK := Null_MLKEM_KAT;

      TK.Z := String_To_Bytes
        ("92AC7D1F83BAFAE6EE86FE00F95D813375772434860F5FF7D54FFC37399BC4CC");
      TK.D := TK.Z;
   end Read_KeyGen_KAT;

   procedure Run_KeyGen_KAT
   is
      CK : MLKEM_Key;
   begin
      CK := MLKEM_KeyGen (TK.D, TK.Z);
   end Run_KeyGen_KAT;

   T1, T2 : Time;
   T3     : Duration;
begin
   Read_KeyGen_KAT;
   T1 := Clock;
   for I in 1 .. 1_000_000 loop
      Run_KeyGen_KAT;
      TK.Z (0) := TK.Z (0) + 1;
   end loop;
   T2 := Clock;
   T3 := To_Duration (T2 - T1);
   Put_Line (T3'Img & " microseconds per KeyGen");
end TKeyGen;

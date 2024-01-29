--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

with Ada.Text_IO; use Ada.Text_IO;
with Ada.IO_Exceptions;

with GNAT.IO_Aux; use GNAT.IO_Aux;

with Interfaces; use Interfaces;

with MLKEM;       use MLKEM;
with MLKEM.Debug; use MLKEM.Debug;

procedure TUnlucky
is
   FN : constant String := "unlucky.rsp";
   FH : File_Type;

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
      Computed_PK   : MLKEM_Encapsulation_Key;
      Computed_SK   : MLKEM_Decapsulation_Key;
      Computed_CT   : Ciphertext;
      Computed_SS1  : Bytes_32;
      Computed_SS2  : Bytes_32;
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

   EOF : Boolean := False;
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

   procedure Read_KAT;

   procedure Read_KAT
   is
      procedure Read_A_Line (Ready : out Boolean);

      procedure Read_A_Line (Ready : out Boolean)
      is
         L : constant String := GNAT.IO_Aux.Get_Line (FH);
      begin
         Ready := False;
         if L (1 .. 8) = "count = " then
            TK.Count := Natural'Value (String (L (9 .. L'Last)));

         elsif L (1 .. 4) = "z = " then
            TK.Z := String_To_Bytes (String (L (5 .. L'Last)));

         elsif L (1 .. 4) = "d = " then
            TK.D := String_To_Bytes (String (L (5 .. L'Last)));

         elsif L (1 .. 6) = "msg = " then
            TK.Msg := String_To_Bytes (String (L (7 .. L'Last)));

         elsif L (1 .. 7) = "seed = " then
            TK.Seed := String_To_Bytes (String (L (8 .. L'Last)));

         elsif L (1 .. 5) = "pk = " then
            TK.Expected_PK := String_To_Bytes (String (L (6 .. L'Last)));

         elsif L (1 .. 5) = "sk = " then
            TK.Expected_SK := String_To_Bytes (String (L (6 .. L'Last)));

         elsif L (1 .. 5) = "ct = " then
            TK.Expected_CT := String_To_Bytes (String (L (6 .. L'Last)));

         elsif L (1 .. 5) = "ss = " then
            TK.Expected_SS := String_To_Bytes (String (L (6 .. L'Last)));
            --  The "ss = " line signifies a complete KAT, so let's go...
            Ready := True;
         end if;
      exception
         when Ada.IO_Exceptions.End_Error =>
            Ready := True;
            EOF   := True;
      end Read_A_Line;

      TK_Ready : Boolean := False;
   begin
      TK := Null_MLKEM_KAT;
      if End_Of_File (FH) then
         EOF := True;
      else
         loop
            Read_A_Line (TK_Ready);
            exit when TK_Ready;
         end loop;
      end if;
   end Read_KAT;

   procedure Run_KAT;

   procedure Run_KAT
   is
      CK : MLKEM_Key;
   begin
      CK := MLKEM_KeyGen (TK.D, TK.Z);
      TK.Computed_PK := CK.EK;
      TK.Computed_SK := CK.DK;

      if EK_Is_Valid_For_Encaps (CK.EK) then
         MLKEM_Encaps (CK.EK, TK.Msg, TK.Computed_SS1, TK.Computed_CT);
         TK.Computed_SS2 := MLKEM_Decaps (TK.Computed_CT, CK.DK);

         Put_Line ("count =" & TK.Count'Img);
         Put_Line ("z = ", TK.Z);
         Put_Line ("d = ", TK.D);
         Put_Line ("msg = ", TK.Msg);
         Put_Line ("seed = ", TK.Seed);
         --  Report the computed answers for comparison with the inputs
         Put_Line ("pk = ", TK.Computed_PK);
         Put_Line ("sk = ", TK.Computed_SK);
         Put_Line ("ct = ", TK.Computed_CT);
         Put_Line ("ss = ", TK.Computed_SS1);

         if TK.Expected_PK = TK.Computed_PK then
            Put_Line ("PK Pass");
         else
            Put_Line ("PK Fail");
         end if;

         if TK.Expected_SK = TK.Computed_SK then
            Put_Line ("SK Pass");
         else
            Put_Line ("SK Fail");
         end if;

         if TK.Expected_CT = TK.Computed_CT then
            Put_Line ("CT Pass");
         else
            Put_Line ("CT Fail");
         end if;

         if TK.Expected_SS = TK.Computed_SS1 then
            Put_Line ("SS1 Pass");
         else
            Put_Line ("SS1 Fail");
         end if;

         if TK.Computed_SS1 = TK.Computed_SS2 then
            Put_Line ("SS1 = SS2 Pass");
         else
            Put_Line ("SS1 = SS2 Fail");
         end if;

      else
         Put_Line ("Computed EK is not valid - fail");
      end if;

   end Run_KAT;

begin
   if File_Exists (FN) then
      Open (FH, In_File, FN);

      loop
         Read_KAT;
         exit when EOF;
         Run_KAT;
      end loop;

      Close (FH);
   else
      Put_Line (FN & " does not exist");
   end if;
end TUnlucky;

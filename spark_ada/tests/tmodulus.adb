--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

with Ada.Text_IO; use Ada.Text_IO;
with Ada.IO_Exceptions;

with GNAT.IO_Aux; use GNAT.IO_Aux;

with Interfaces; use Interfaces;

with MLKEM;       use MLKEM;
with MLKEM.Tests;

procedure TModulus
is
   FN : constant String := "invalid_ek.txt";
   FH : File_Type;

   type MLKEM_KAT is record
      --  KAT inputs and expected results read from the file
      Invalid_PK  : MLKEM_Encapsulation_Key;
   end record;

   Null_MLKEM_KAT : constant MLKEM_KAT :=
     (Invalid_PK  => (others => 0));

   EOF : Boolean := False;
   TK  : MLKEM_KAT;

   Count : Positive := 1;

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
         TK.Invalid_PK := String_To_Bytes (L);
         Ready := True;
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
   begin
      Put (Count'Img);
      if EK_Is_Valid_For_Encaps (TK.Invalid_PK) then
         Put_Line (" EK is OK - FAIL!");
      else
         Put_Line (" EK is Invalid - PASS");
      end if;

      Count := Count + 1;
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

   Put_Line ("--- MulTest ---");
   MLKEM.Tests.MulTest;
end TModulus;

--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

with Ada.Text_IO; use Ada.Text_IO;
package body MLKEM.Debug
  with SPARK_Mode => Off
is
   type BToCT is array (Byte range 0 .. 15) of Character;
   BToC : constant BToCT :=
     ('0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
      'a', 'b', 'c', 'd', 'e', 'f');

   procedure PB (X : in Byte);

   procedure PB (X : in Byte)
   is
   begin
      Put (BToC (X / 16));
      Put (BToC (X mod 16));
   end PB;

   procedure Put_Line (S : in String; D : in Byte_Seq)
   is
   begin
      Put (S);
      for I in D'Range loop
         PB (D (I));
      end loop;
      New_Line;
   end Put_Line;

end MLKEM.Debug;

with SToU2; use SToU2;
with Ada.Numerics.Discrete_Random;
with Ada.Text_IO; use Ada.Text_IO;
with Interfaces; use Interfaces;
with Interfaces.C; use Interfaces.C;
with Interfaces.C.Strings; use Interfaces.C.Strings;
with cpucycles_h;
procedure TSToU
is
   package RC is new Ada.Numerics.Discrete_Random (SC);

   SP : SPoly;
   R, UP1, UP2, UP3 : UPoly;
   G : RC.Generator;
   I : chars_ptr;
   Count1, Count2, EC, EC2, EC4, EC4O : Long_Long_Integer;

   procedure  NC (X : in SPoly;
                  Y : out UPoly)
   is
   begin
      for I in X'Range loop
         Y (I) := UC (I16 (X (I)) mod 3329);
      end loop;
   end NC;

   procedure Put (X : in SPoly)
   is
   begin
      for I in X'Range loop
         Put (X (I)'Img);
      end loop;
      New_Line;
   end Put;

   procedure Put (X : in UPoly)
   is
   begin
      for I in X'Range loop
         Put (X (I)'Img);
      end loop;
      New_Line;
   end Put;

begin
   RC.Reset (G);

   for K in 0 .. 9999 loop
      for I in SP'Range loop
         SP (I) := RC.Random (G);
      end loop;
      NC (SP, R);
      SToU2.C (SP, UP1);
      SToU2.C2 (SP, UP2);
      SToU2.C4o (SP, UP3);

      if R = UP1 and UP1 = UP2 and UP3 = UP3 then
         null;
      else
         Put_Line ("Fail");
         raise Program_Error;
      end if;
   end loop;
   Put_Line ("Functional Pass");

   for I in SP'Range loop
      SP (I) := RC.Random (G);
   end loop;

   I := cpucycles_h.cpucycles_implementation;

   Put_Line ("CpuCycles Implem is " & To_Ada (Value (I)));

   Count1 := cpucycles_h.cpucycles.all;
   for I in 0 .. 999_999 loop
      SToU2.C (SP, R);
   end loop;
   Count2 := cpucycles_h.cpucycles.all;
   EC := Count2 - Count1;

   Count1 := cpucycles_h.cpucycles.all;
   for I in 0 .. 999_999 loop
      SToU2.C2 (SP, R);
   end loop;
   Count2 := cpucycles_h.cpucycles.all;
   EC2 := Count2 - Count1;

   Count1 := cpucycles_h.cpucycles.all;
   for I in 0 .. 999_999 loop
      SToU2.C4 (SP, R);
   end loop;
   Count2 := cpucycles_h.cpucycles.all;
   EC4 := Count2 - Count1;

   Count1 := cpucycles_h.cpucycles.all;
   for I in 0 .. 999_999 loop
      SToU2.C4O (SP, R);
   end loop;
   Count2 := cpucycles_h.cpucycles.all;
   EC4O := Count2 - Count1;



   Put_Line ("C   Cycles = " & EC'Img);
   Put_Line ("C2  Cycles = " & EC2'Img);
   Put_Line ("C4  Cycles = " & EC4'Img);
   Put_Line ("C4O Cycles = " & EC4O'Img);



end TSToU;

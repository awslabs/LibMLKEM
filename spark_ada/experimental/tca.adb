with ENTTRef; use ENTTRef;
with Ada.Text_IO; use Ada.Text_IO;
with Ada.Real_Time; use Ada.Real_Time;
procedure TCA
is
   R1, R2 : Poly_Zq;
   T1, T2 : Time;
   TA, TC : Duration;
begin
   for I in R1'Range loop
      R1 (I) := I16 (I);
   end loop;
   R2 := R1;


   T1 := Clock;
--   for J in 1 .. 1_000_000 loop
      Put_Line ("--- one ---");
      NTTu (R1);
      Put_Line ("--- two ---");
      NTTu (R1);
--   end loop;
   T2 := Clock;
   TA := To_Duration (T2 - T1);

   T1 := Clock;
--   for J in 1 .. 1_000_000 loop
      CNTT (R2);
      CNTT (R2);
--   end loop;
   T2 := Clock;
   TC := To_Duration (T2 - T1);

   Put_Line ("--- R1 from Ada ---");
   for I in R1'Range loop
      Put (R1 (I)'Img);
   end loop;
   New_Line;

   Put_Line ("--- R2 from C ---");
   for I in R2'Range loop
      Put (R2 (I)'Img);
   end loop;
   New_Line;

   if R1 = R2 then
      Put_Line ("Pass");
   else
      Put_Line ("Fail");
   end if;

   -- Should be 896
   Put_Line ("Reductions = " & RCount'Img);

   Put_Line ("C   time " & TC'Img);
   Put_Line ("Ada time " & TA'Img);
end TCA;

with RMerge2; use RMerge2;
with Ada.Text_IO; use Ada.Text_IO;
with Interfaces.C; use Interfaces.C;
with Interfaces.C.Strings; use Interfaces.C.Strings;
with cpucycles_h;
procedure TRef
is
   P1 : Poly_Zq;

   procedure PP (F : in Poly_Zq)
   is
   begin
      for I in F'Range loop
         Put (F (I)'Img);
      end loop;
      New_Line (2);
   end PP;

   Count1, Count2, E : Long_Long_Integer;
   I : chars_ptr;
begin
   I := cpucycles_h.cpucycles_implementation;

   Put_Line ("Implem is " & To_Ada (Value (I)));

   P1 := (others => 3);

   Count1 := cpucycles_h.cpucycles.all;
   for I in 0 .. 999 loop
      NTT  (P1);
   end loop;
   Count2 := cpucycles_h.cpucycles.all;
   E := Count2 - Count1;

   Put_Line ("Result...");
   PP (P1);
   Put_Line ("Cycles = " & E'Img);
end TRef;

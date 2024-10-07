with RMerge2; use RMerge2;
with RMerge2.Inv; use RMerge2.Inv;
with Ada.Text_IO; use Ada.Text_IO;
with Interfaces.C; use Interfaces.C;
with Interfaces.C.Strings; use Interfaces.C.Strings;
with cpucycles_h;
procedure TRef
is
   P1, P2 : Poly_Zq;

   procedure PP (F : in Poly_Zq)
   is
   begin
      for I in F'Range loop
         Put (F (I)'Img);
      end loop;
      New_Line (2);
   end PP;

   Count1, Count2, Eref, Enew : Long_Long_Integer;
   I : chars_ptr;
begin
   I := cpucycles_h.cpucycles_implementation;

   Put_Line ("Implem is " & To_Ada (Value (I)));

   P1 := (others => 3);

   Put_Line ("P1:");
   PP (P1);

   NTT  (P1);

   Put_Line ("NTT(P1):");
   PP (P1);

   P2 := P1;

   Count1 := cpucycles_h.cpucycles.all;
   for I in 0 .. 999 loop
      INTT  (P1);
   end loop;
   Count2 := cpucycles_h.cpucycles.all;
   Eref := Count2 - Count1;

   Count1 := cpucycles_h.cpucycles.all;
   for I in 0 .. 999 loop
      INTTnew (P2);
   end loop;
   Count2 := cpucycles_h.cpucycles.all;
   Enew := Count2 - Count1;


   Put_Line ("INTT(NTT(P1)):");
   PP (P1);
   Put_Line ("INTT(P2):");
   PP (P2);
   if P1 = P2 then
      Put_Line ("Pass");
   else
      Put_Line ("FAIL");
   end if;
   Put_Line ("Ref Cycles = " & Eref'Img);
   Put_Line ("New Cycles = " & Enew'Img);
end TRef;

with RMerge2; use RMerge2;
with RMerge2.Inv; use RMerge2.Inv;
with Ada.Text_IO; use Ada.Text_IO;
with Interfaces.C; use Interfaces.C;
with Interfaces.C.Strings; use Interfaces.C.Strings;
with cpucycles_h;
procedure TRef
is
   P1, P2, P3 : Poly_Zq;

   procedure PP (F : in Poly_Zq)
   is
   begin
      for I in F'Range loop
         Put (F (I)'Img);
      end loop;
      New_Line (2);
   end PP;

   Count1, Count2, EAref, ECRef, Enew : Long_Long_Integer;
   I : chars_ptr;
begin
   I := cpucycles_h.cpucycles_implementation;

   Put_Line ("Implem is " & To_Ada (Value (I)));

   P1 := (others => 3);

   Put_Line ("P1:");
   PP (P1);

   for I in 0 .. 999 loop
      NTT  (P1);
   end loop;

   Put_Line ("NTT(P1):");
   PP (P1);

   P2 := P1;
   P3 := P1;
--   P4 := P1;

   -- Test and time C version
   Count1 := cpucycles_h.cpucycles.all;
   for I in 0 .. 999 loop
      CINTT  (P1);
   end loop;
   Count2 := cpucycles_h.cpucycles.all;
   ECref := Count2 - Count1;

   -- Test and time Ada reference code
   Count1 := cpucycles_h.cpucycles.all;
   for I in 0 .. 999 loop
      INTT  (P2);
   end loop;
   Count2 := cpucycles_h.cpucycles.all;
   EAref := Count2 - Count1;

   -- Test and time new SPARK Code, 1,1,2,3 merge
   Count1 := cpucycles_h.cpucycles.all;
   for I in 0 .. 999 loop
      INTTnew (P3);
   end loop;
   Count2 := cpucycles_h.cpucycles.all;
   Enew := Count2 - Count1;

   -- Test and time new SPARK Code, with merging
--   Count1 := cpucycles_h.cpucycles.all;
--   for I in 0 .. 999 loop
--      INTTmerge (P4);
--   end loop;
--   Count2 := cpucycles_h.cpucycles.all;
--   Efast := Count2 - Count1;


   Put_Line ("INTT C:");
   PP (P1);
   Put_Line ("INTT Ada ref:");
   PP (P2);
   Put_Line ("INTT Ada new (1,3,3 layers):");
   PP (P3);
--   Put_Line ("INTT Ada new (3,1,1,1,1 layers):");
--   PP (P4);

--   if P1 = P2 and P2 = P3 and P3 = P4 then
   if P1 = P2 and P2 = P3 then
      Put_Line ("Pass");
   else
      Put_Line ("FAIL");
   end if;
   Put_Line ("Ref     C Cycles = " & ECref'Img);
   Put_Line ("Ref   Ada Cycles = " & EAref'Img);
   Put_Line ("New   Ada Cycles = " & Enew'Img);
--   Put_Line ("MergedAda Cycles = " & Efast'Img);
end TRef;

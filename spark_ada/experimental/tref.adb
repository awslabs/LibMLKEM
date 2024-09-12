with RMerge2; use RMerge2;
with Ada.Text_IO; use Ada.Text_IO;
with Interfaces; use Interfaces;
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

begin

   P1 := (others => 6);
   P2 := P1;
   P3 := P1;

   NTT  (P2);
   CNTT (P3);

   PP (P1);
   Put_Line ("SPARK");
   PP (P2);
   Put_Line ("C");
   PP (P3);

   for I in 1 .. 1_000 loop

      P2 := P1;
      P3 := P1;

      CNTT (P2);
      NTT (P3);

      if P2 = P3 then
         null;
      else
         Put_Line ("Fail P2 /= P3");
         raise Program_Error;
      end if;

      P1 (Index_256 (I mod 256)) := (P1 (Index_256 (I mod 256)) + 1) mod Q;
   end loop;

   Put_Line ("Final SPARK");
   PP (P2);
   Put_Line ("Final C");
   PP (P3);

   Put_Line ("Pass");
end TRef;

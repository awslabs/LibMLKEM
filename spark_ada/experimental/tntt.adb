with ENTT; use ENTT;
with Ada.Text_IO; use Ada.Text_IO;
procedure TNTT
is
   P1, P2, P3 : Poly_Zq;
begin
   P1 := (others => 5);


   for I in 1 .. 1000 loop
      P3 := P1;

      P2 := NTT (P1);
      NTTir (P3);

      if P2 = P3 then
         null;
      else
         Put_Line ("Fail");
         raise Program_Error;
      end if;

      P1 (Index_256 (I mod 256)) := P1 (Index_256 (I mod 256)) + 1;
   end loop;
   Put_Line ("Pass");
end TNTT;

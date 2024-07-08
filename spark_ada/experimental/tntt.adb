with ENTT; use ENTT;
with Ada.Text_IO; use Ada.Text_IO;
procedure TNTT
is
   P1, P2, P3 : Poly_Zq;
   P4, P5 : Poly_Zq;
begin
   P1 := (others => 5);


   for I in 1 .. 100_000 loop
--      P3 := P1;

      P2 := NTT (P1);
      P3 := NTTsr (P1);

      P4 := NTT_Inv (P2);

      P5 := NTT_Invsr (P3);
--      NTT_Invir (P5);

      if P2 = P3 then
         null;
      else
         Put_Line ("Fail P2 /= P3");
         raise Program_Error;
      end if;

      if P4 = P5 then
         null;
      else
         Put_Line ("Fail P4 /= P5");
         raise Program_Error;
      end if;

      if P4 = P1 then
         null;
      else
         Put_Line ("Fail P4 /= P1");
         raise Program_Error;
      end if;

      P1 (Index_256 (I mod 256)) := P1 (Index_256 (I mod 256)) + 1;
   end loop;
   Put_Line ("Pass");
end TNTT;

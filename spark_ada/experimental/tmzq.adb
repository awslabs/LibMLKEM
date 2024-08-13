with ENTT;
with NTT32; use NTT32;
with Ada.Text_IO; use Ada.Text_IO;
with Interfaces; use Interfaces;
procedure TMZQ
is
   R1, R2 : U32;
begin
   for I in ZqU32 loop
      for J in ZqU32 loop
         R1 := (I * J) mod 3329;
         R2 := MZq (I, J);
         if R1 /= R2 then
            Put_Line (I'Img & J'Img & "Fail");
         end if;
      end loop;
   end loop;
end TMZQ;

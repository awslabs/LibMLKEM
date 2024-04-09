with P; use P;
with Interfaces; use Interfaces;
procedure TestDiv
is
   T1, T2 : U32;
begin
   for I in Zq_Product loop
      T1 := Div1 (I);
      T2 := Div2 (I);
      if T1 /= T2 then
         raise Program_Error;
      end if;
   end loop;
end TestDiv;

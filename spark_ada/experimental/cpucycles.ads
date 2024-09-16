with Interfaces.C; use Interfaces.C;
with Interfaces.C.Strings; use Interfaces.C.Strings;
package CPUCycles
is
   pragma Linker_Options("-lcpucycles");

   pragma Linker_Options("-L/Users/rodchap/lib");

   function Get_CPUCycles return Long_Long;

   function Get_CPUCycles_Implementation return chars_ptr
     with Import,
          Convention => C,
          External_Name => "cpucycles_implementation";
end CPUCycles;

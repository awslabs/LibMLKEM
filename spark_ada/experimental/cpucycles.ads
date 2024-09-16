with Interfaces.C; use Interfaces.C;
package CPUCycles
is
   pragma Linker_Options("-lcpucycles");

   pragma Linker_Options("-L/Users/rodchap/lib");

   function Get_CPUCycles return Long_Long;

end CPUCycles;

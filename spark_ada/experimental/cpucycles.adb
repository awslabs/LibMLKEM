package body CPUCycles
is
   type FP is access function return Long_Long;

   GetCC : FP
     with Import,
          Convention => C,
          External_Name => "cpucycles";

   function Get_CPUCycles return Long_Long
   is
   begin
      return GetCC.all;
   end Get_CPUCycles;

end CPUCycles;

with Interfaces; use Interfaces;
package SToU2
  with SPARK_Mode => On
is
   pragma Linker_Options ("stou_asm.o");

   Q   : constant := 3329;
   QM1 : constant := 3328;
   HQ  : constant := 1664;

   subtype I32 is Integer_32;
   subtype I16 is Integer_16;
   subtype U16 is Unsigned_16;

   subtype I256 is I32 range 0 .. 255;

   subtype SC is I16 range -HQ .. HQ;
   subtype UC is U16 range   0 .. QM1;

   type SPoly is array (I256) of SC;
   type UPoly is array (I256) of UC;

   procedure C (SP : in     SPoly;
                UP :    out UPoly)
     with Global => null,
          Import,
          Convention => C,
          External_Name => "stou__c";

   procedure C2 (SP : in     SPoly;
                 UP :    out UPoly)
     with Global => null,
          Import,
          Convention => C,
          External_Name => "stou__c2";

   procedure C4 (SP : in     SPoly;
                 UP :    out UPoly)
     with Global => null,
          Import,
          Convention => C,
          External_Name => "stou__c4";

   procedure C4O (SP : in     SPoly;
                  UP :    out UPoly)
     with Global => null,
          Import,
          Convention => C,
          External_Name => "stou__c4o";

end SToU2;

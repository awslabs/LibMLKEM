pragma Ada_2012;

pragma Style_Checks (Off);
pragma Warnings (Off, "-gnatwu");

with Interfaces.C; use Interfaces.C;
with Interfaces.C.Strings;

package cpucycles_h is

   pragma Linker_Options("-lcpucycles");

   pragma Linker_Options("-L/Users/rodchap/lib");

  -- version 20230115
  -- public domain
  -- djb
  -- 20230115 djb: cpucycles_version()
  -- 20230114 djb: improve punctuation
   cpucycles : access function return Long_Long_Integer  -- cpucycles.h:15
   with Import => True,
        Convention => C,
        External_Name => "cpucycles";

   function cpucycles_implementation return Interfaces.C.Strings.chars_ptr  -- cpucycles.h:16
   with Import => True,
        Convention => C,
        External_Name => "cpucycles_implementation";

   function cpucycles_version return Interfaces.C.Strings.chars_ptr  -- cpucycles.h:17
   with Import => True,
        Convention => C,
        External_Name => "cpucycles_version";

   function cpucycles_persecond return Long_Long_Integer  -- cpucycles.h:18
   with Import => True,
        Convention => C,
        External_Name => "cpucycles_persecond";

   procedure cpucycles_tracesetup  -- cpucycles.h:19
   with Import => True,
        Convention => C,
        External_Name => "cpucycles_tracesetup";

end cpucycles_h;

pragma Style_Checks (On);
pragma Warnings (On, "-gnatwu");

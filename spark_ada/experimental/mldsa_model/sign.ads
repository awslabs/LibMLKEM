with MLDSA; use MLDSA;
package Sign
  with Spark_Mode => On
is

   procedure Keypair_Internal (PK   :    out Bytes_PK;
                               SK   :    out Bytes_SK;
                               Seed : in     Bytes_Seed)
     with Global => null;

   procedure Signature_Internal (Sig    :    out Bytes_Crypto;
                                 OK     :    out Boolean;
                                 M      : in     Byte_Seq;
                                 Prefix : in     Byte_Seq;
                                 Rnd    : in     Bytes_Rnd;
                                 SK     : in     Bytes_SK;
                                 ExtMu  : in     Boolean)
     with Global => null,
          Pre => M'First = 1 and
                 Prefix'First = 1 and
                 ((ExtMu and M'Last = CRHBYTES) or
                  (not ExtMu and M'Last >= 1));




   function Verify_Internal (Sig    : in Bytes_Crypto;
                             M      : in Byte_Seq;
                             Prefix : in Byte_Seq;
                             PK     : in Bytes_PK;
                             ExtMu  : in Boolean) return Boolean
     with Global => null,
          Pre => M'First = 1 and
                 Prefix'First = 1 and
                 ((ExtMu and M'Last = CRHBYTES) or
                  (not ExtMu and M'Last >= 1));

end Sign;

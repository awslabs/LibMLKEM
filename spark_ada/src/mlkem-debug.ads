--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

package MLKEM.Debug
  with SPARK_Mode => On
is

   procedure Put_Line (S : in String; D : in Byte_Seq)
     with Global => null;

end MLKEM.Debug;

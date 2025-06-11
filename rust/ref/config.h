/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [FIPS140_3_IG]
 *   Implementation Guidance for FIPS 140-3 and the Cryptographic Module
 *   Validation Program National Institute of Standards and Technology
 *   https://csrc.nist.gov/projects/cryptographic-module-validation-program/fips-140-3-ig-announcements
 */

#ifndef MLK_CONFIG_H
#define MLK_CONFIG_H

/******************************************************************************
 * Name:        MLK_CONFIG_PARAMETER_SET
 *
 * Description: Specifies the parameter set for ML-KEM
 *              - MLK_CONFIG_PARAMETER_SET=512 corresponds to ML-KEM-512
 *              - MLK_CONFIG_PARAMETER_SET=768 corresponds to ML-KEM-768
 *              - MLK_CONFIG_PARAMETER_SET=1024 corresponds to ML-KEM-1024
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#ifndef MLK_CONFIG_PARAMETER_SET
#define MLK_CONFIG_PARAMETER_SET \
  768 /* Change this for different security strengths */
#endif

/******************************************************************************
 * Name:        MLK_CONFIG_FILE
 *
 * Description: If defined, this is a header that will be included instead
 *              of this default configuration file mlkem/src/config.h.
 *
 *              When you need to build mlkem-native in multiple configurations,
 *              using varying MLK_CONFIG_FILE can be more convenient
 *              then configuring everything through CFLAGS.
 *
 *              To use, MLK_CONFIG_FILE _must_ be defined prior
 *              to the inclusion of any mlkem-native headers. For example,
 *              it can be set by passing `-DMLK_CONFIG_FILE="..."`
 *              on the command line.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_FILE "config.h" */

/******************************************************************************
 * Name:        MLK_CONFIG_NAMESPACE_PREFIX
 *
 * Description: The prefix to use to namespace global symbols from mlkem/.
 *
 *              In a multi-level build (that is, if either
 *              - MLK_CONFIG_MULTILEVEL_WITH_SHARED, or
 *              - MLK_CONFIG_MULTILEVEL_NO_SHARED,
 *              are set, level-dependent symbols will additionally be prefixed
 *              with the parameter set (512/768/1024).
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#if !defined(MLK_CONFIG_NAMESPACE_PREFIX)
#define MLK_CONFIG_NAMESPACE_PREFIX MLK_DEFAULT_NAMESPACE_PREFIX
#endif

/******************************************************************************
 * Name:        MLK_CONFIG_MULTILEVEL_WITH_SHARED
 *
 * Description: This is for multi-level builds of mlkem-native only. If you
 *              need only a single parameter set, keep this unset.
 *
 *              If this is set, all MLK_CONFIG_PARAMETER_SET-independent
 *              code will be included in the build, including code needed only
 *              for other parameter sets.
 *
 *              Example: mlk_poly_cbd3 is only needed for
 *              MLK_CONFIG_PARAMETER_SET == 512. Yet, if this option is set
 *              for a build with MLK_CONFIG_PARAMETER_SET == 768/1024, it
 *              would be included.
 *
 *              To build mlkem-native with support for all parameter sets,
 *              build it three times -- once per parameter set -- and set the
 *              option MLK_CONFIG_MULTILEVEL_WITH_SHARED for exactly one of
 *              them, and MLK_CONFIG_MULTILEVEL_NO_SHARED for the others.
 *
 *              See examples/multilevel_build for an example.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_MULTILEVEL_WITH_SHARED */

/******************************************************************************
 * Name:        MLK_CONFIG_MULTILEVEL_NO_SHARED
 *
 * Description: This is for multi-level builds of mlkem-native only. If you
 *              need only a single parameter set, keep this unset.
 *
 *              If this is set, no MLK_CONFIG_PARAMETER_SET-independent code
 *              will be included in the build.
 *
 *              To build mlkem-native with support for all parameter sets,
 *              build it three times -- once per parameter set -- and set the
 *              option MLK_CONFIG_MULTILEVEL_WITH_SHARED for exactly one of
 *              them, and MLK_CONFIG_MULTILEVEL_NO_SHARED for the others.
 *
 *              See examples/multilevel_build for an example.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_MULTILEVEL_NO_SHARED */

/******************************************************************************
 * Name:        MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
 *
 * Description: This is only relevant for single compilation unit (SCU)
 *              builds of mlkem-native. In this case, it determines whether
 *              directives defined in parameter-set-independent headers should
 *              be #undef'ined or not at the of the SCU file. This is needed
 *              in multilevel builds.
 *
 *              See examples/multilevel_build_native for an example.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS */

/******************************************************************************
 * Name:        MLK_CONFIG_USE_NATIVE_BACKEND_ARITH
 *
 * Description: Determines whether an native arithmetic backend should be used.
 *
 *              The arithmetic backend covers performance critical functions
 *              such as the number-theoretic transform (NTT).
 *
 *              If this option is unset, the C backend will be used.
 *
 *              If this option is set, the arithmetic backend to be use is
 *              determined by MLK_CONFIG_ARITH_BACKEND_FILE: If the latter is
 *              unset, the default backend for your the target architecture
 *              will be used. If set, it must be the name of a backend metadata
 *              file.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#if !defined(MLK_CONFIG_USE_NATIVE_BACKEND_ARITH)
/* #define MLK_CONFIG_USE_NATIVE_BACKEND_ARITH */
#endif

/******************************************************************************
 * Name:        MLK_CONFIG_ARITH_BACKEND_FILE
 *
 * Description: The arithmetic backend to use.
 *
 *              If MLK_CONFIG_USE_NATIVE_BACKEND_ARITH is unset, this option
 *              is ignored.
 *
 *              If MLK_CONFIG_USE_NATIVE_BACKEND_ARITH is set, this option must
 *              either be undefined or the filename of an arithmetic backend.
 *              If unset, the default backend will be used.
 *
 *              This can be set using CFLAGS.
 *
 *****************************************************************************/
#if defined(MLK_CONFIG_USE_NATIVE_BACKEND_ARITH) && \
    !defined(MLK_CONFIG_ARITH_BACKEND_FILE)
#define MLK_CONFIG_ARITH_BACKEND_FILE "native/meta.h"
#endif

/******************************************************************************
 * Name:        MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202
 *
 * Description: Determines whether an native FIPS202 backend should be used.
 *
 *              The FIPS202 backend covers 1x/2x/4x-fold Keccak-f1600, which is
 *              the performance bottleneck of SHA3 and SHAKE.
 *
 *              If this option is unset, the C backend will be used.
 *
 *              If this option is set, the FIPS202 backend to be use is
 *              determined by MLK_CONFIG_FIPS202_BACKEND_FILE: If the latter is
 *              unset, the default backend for your the target architecture
 *              will be used. If set, it must be the name of a backend metadata
 *              file.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#if !defined(MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202)
/* #define MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202 */
#endif

/******************************************************************************
 * Name:        MLK_CONFIG_FIPS202_BACKEND_FILE
 *
 * Description: The FIPS-202 backend to use.
 *
 *              If MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202 is set, this option
 *              must either be undefined or the filename of a FIPS202 backend.
 *              If unset, the default backend will be used.
 *
 *              This can be set using CFLAGS.
 *
 *****************************************************************************/
#if defined(MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202) && \
    !defined(MLK_CONFIG_FIPS202_BACKEND_FILE)
#define MLK_CONFIG_FIPS202_BACKEND_FILE "fips202/native/auto.h"
#endif

/******************************************************************************
 * Name:        MLK_CONFIG_FIPS202_CUSTOM_HEADER
 *
 * Description: Custom header to use for FIPS-202
 *
 *              This should only be set if you intend to use a custom
 *              FIPS-202 implementation, different from the one shipped
 *              with mlkem-native.
 *
 *              If set, it must be the name of a file serving as the
 *              replacement for mlkem/fips202/fips202.h, and exposing
 *              the same API (see FIPS202.md).
 *
 *****************************************************************************/
/* #define MLK_CONFIG_FIPS202_CUSTOM_HEADER "SOME_FILE.h" */

/******************************************************************************
 * Name:        MLK_CONFIG_FIPS202X4_CUSTOM_HEADER
 *
 * Description: Custom header to use for FIPS-202-X4
 *
 *              This should only be set if you intend to use a custom
 *              FIPS-202 implementation, different from the one shipped
 *              with mlkem-native.
 *
 *              If set, it must be the name of a file serving as the
 *              replacement for mlkem/fips202/fips202x4.h, and exposing
 *              the same API (see FIPS202.md).
 *
 *****************************************************************************/
/* #define MLK_CONFIG_FIPS202X4_CUSTOM_HEADER "SOME_FILE.h" */

/******************************************************************************
 * Name:        MLK_CONFIG_CUSTOM_ZEROIZE
 *
 * Description: In compliance with FIPS 203 Section 3.3, mlkem-native zeroizes
 *              intermediate stack buffers before returning from function calls.
 *
 *              Set this option and define `mlk_zeroize` if you want to
 *              use a custom method to zeroize intermediate stack buffers.
 *              The default implementation uses SecureZeroMemory on Windows
 *              and a memset + compiler barrier otherwise. If neither of those
 *              is available on the target platform, compilation will fail,
 *              and you will need to use MLK_CONFIG_CUSTOM_ZEROIZE to provide
 *              a custom implementation of `mlk_zeroize()`.
 *
 *              WARNING:
 *              The explicit stack zeroization conducted by mlkem-native
 *              reduces the likelihood of data leaking on the stack, but
 *              does not eliminate it! The C standard makes no guarantee about
 *              where a compiler allocates structures and whether/where it makes
 *              copies of them. Also, in addition to entire structures, there
 *              may also be potentially exploitable leakage of individual values
 *              on the stack.
 *
 *              If you need bullet-proof zeroization of the stack, you need to
 *              consider additional measures instead of of what this feature
 *              provides. In this case, you can set mlk_zeroize to a no-op.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_CUSTOM_ZEROIZE
   #if !defined(__ASSEMBLER__)
   #include <stdint.h>
   #include "sys.h"
   static MLK_INLINE void mlk_zeroize(void *ptr, size_t len)
   {
       ... your implementation ...
   }
   #endif
*/

/******************************************************************************
 * Name:        MLK_CONFIG_CUSTOM_RANDOMBYTES
 *
 * Description: mlkem-native does not provide a secure randombytes
 *              implementation. Such an implementation has to provided by the
 *              consumer.
 *
 *              If this option is not set, mlkem-native expects a function
 *              void randombytes(uint8_t *out, size_t outlen).
 *
 *              Set this option and define `mlk_randombytes` if you want to
 *              use a custom method to sample randombytes with a different name
 *              or signature.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_CUSTOM_RANDOMBYTES
   #if !defined(__ASSEMBLER__)
   #include <stdint.h>
   #include "sys.h"
   static MLK_INLINE void mlk_randombytes(uint8_t *ptr, size_t len)
   {
       ... your implementation ...
   }
   #endif
*/

/******************************************************************************
 * Name:        MLK_CONFIG_INTERNAL_API_QUALIFIER
 *
 * Description: If set, this option provides an additional function
 *              qualifier to be added to declarations of internal API.
 *
 *              The primary use case for this option are single-CU builds,
 *              in which case this option can be set to `static`.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_INTERNAL_API_QUALIFIER */

/******************************************************************************
 * Name:        MLK_CONFIG_EXTERNAL_API_QUALIFIER
 *
 * Description: If set, this option provides an additional function
 *              qualifier to be added to declarations of mlkem-native's
 *              public API.
 *
 *              The primary use case for this option are single-CU builds
 *              where the public API exposed by mlkem-native is wrapped by
 *              another API in the consuming application. In this case,
 *              even mlkem-native's public API can be marked `static`.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_EXTERNAL_API_QUALIFIER */

/******************************************************************************
 * Name:        MLK_CONFIG_CT_TESTING_ENABLED
 *
 * Description: If set, mlkem-native annotates data as secret / public using
 *              valgrind's annotations VALGRIND_MAKE_MEM_UNDEFINED and
 *              VALGRIND_MAKE_MEM_DEFINED, enabling various checks for secret-
 *              dependent control flow of variable time execution (depending
 *              on the exact version of valgrind installed).
 *
 *****************************************************************************/
/* #define MLK_CONFIG_CT_TESTING_ENABLED */

/******************************************************************************
 * Name:        MLK_CONFIG_NO_ASM
 *
 * Description: If this option is set, mlkem-native will be built without
 *              use of native code or inline assembly.
 *
 *              By default, inline assembly is used to implement value barriers.
 *              Without inline assembly, mlkem-native will use a global volatile
 *              'opt blocker' instead; see verify.h.
 *
 *              Inline assembly is also used to implement a secure zeroization
 *              function on non-Windows platforms. If this option is set and
 *              the target platform is not Windows, you MUST set
 *              MLK_CONFIG_CUSTOM_ZEROIZE and provide a custom zeroization
 *              function.
 *
 *              If this option is set, MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202 and
 *              and MLK_CONFIG_USE_NATIVE_BACKEND_ARITH will be ignored, and no
 *              native backends will be used.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_NO_ASM */

/******************************************************************************
 * Name:        MLK_CONFIG_KEYGEN_PCT
 *
 * Description: Compliance with @[FIPS140_3_IG, p.87] requires a
 *              Pairwise Consistency Test (PCT) to be carried out on a freshly
 *              generated keypair before it can be exported.
 *
 *              Set this option if such a check should be implemented.
 *              In this case, crypto_kem_keypair_derand and crypto_kem_keypair
 *              will return a non-zero error code if the PCT failed.
 *
 *              NOTE: This feature will drastically lower the performance of
 *              key generation.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_KEYGEN_PCT */

/******************************************************************************
 * Name:        MLK_CONFIG_KEYGEN_PCT_BREAKAGE_TEST
 *
 * Description: If this option is set, the user must provide a runtime
 *              function `static inline int mlk_break_pct() { ... }` to
 *              indicate whether the PCT should be made fail.
 *
 *              This option only has an effect if MLK_CONFIG_KEYGEN_PCT is set.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_KEYGEN_PCT_BREAKAGE_TEST
   #if !defined(__ASSEMBLER__)
   #include "sys.h"
   static MLK_INLINE int mlk_break_pct(void)
   {
       ... return 0/1 depending on whether PCT should be broken ...
   }
   #endif
*/

/*************************  Config internals  ********************************/

/* Default namespace
 *
 * Don't change this. If you need a different namespace, re-define
 * MLK_CONFIG_NAMESPACE_PREFIX above instead, and remove the following.
 *
 * The default MLKEM namespace is
 *
 *   PQCP_MLKEM_NATIVE_MLKEM<LEVEL>_
 *
 * e.g., PQCP_MLKEM_NATIVE_MLKEM512_
 */

#if MLK_CONFIG_PARAMETER_SET == 512
#define MLK_DEFAULT_NAMESPACE_PREFIX PQCP_MLKEM_NATIVE_MLKEM512
#elif MLK_CONFIG_PARAMETER_SET == 768
#define MLK_DEFAULT_NAMESPACE_PREFIX PQCP_MLKEM_NATIVE_MLKEM768
#elif MLK_CONFIG_PARAMETER_SET == 1024
#define MLK_DEFAULT_NAMESPACE_PREFIX PQCP_MLKEM_NATIVE_MLKEM1024
#endif

#endif /* !MLK_CONFIG_H */

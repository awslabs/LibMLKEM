# LibMLKEM - A new, formal reference implementation of FIPS 203 ML-KEM

This library implements ML-KEM, better known as "Kyber", but as
specified in the 24th August 2023 Draft of FIPS 203.

This implementation is written in SPARK - a subset of Ada that is designed
for static verification - and has been subject to verification
with the SPARK toolset.

If the reader is not familiar with SPARK, then [start here](https://learn.adacore.com/).

## IMPORTANT WARNING

This implementation is absolutely NOT intended for production or any use
in a "high assurance" setting. In particular:

* While the code is written in a "constant time" style, this property is not formally verified at
the level of the generated code and micro-architecture, and is not guranteed to be preserved by all compilers.

* Secondly, intermediate values are not sanitized at present, as required by FIPS 203 3.3 (line 699)

* Finally, performance is unlikely to be competetive with other, more optimized, implementations.

## Goals

### From-scratch implementation

This code has been written "from scratch", without reference to any existing
implementation of Kyber, as a way of reviewing FIPS 203 from a clean slate.

### Readability and correspondence with FIPS 203

The code is designed to be trivially traceable to the specifications
and pseudo-code in FIPS 203, in terms of naming and structure.
Names of functions and intermediate variables match as closely
as possible, excepting that the code sticks to the lower-half
of the Latin-1 character set, so (for example) the code
has a variable called "A_Hat" where the specification uses
the UNICODE code-point "Latin Capital A with Circumflex".

Theoretically, the code and the compiler could cope with UNICODE
identifiers, but many editors and IDE's can't, so the code
sticks with simple un-accented names.

### Hybrid static and dynamic verification

This implementation takes a hybrid verification approach that combines
static verification with dynamic testing. Specifically:

* Static verification of the absence of undefined behaviour, plus
memory-safety and type-safety with respect to the stated types,
pre-conditions, post-conditions, and assertions. The proof
is "auto-active" in that it is completely automated
using the standard provers that ship with the SPARK toolset,
and based on the types and assertions in the code alone.

* Static verification of worst-case memory consumption.

* Dynamic testing of functional behaviour with respect to the
[Known-Answer-Tests (KATs)](https://github.com/post-quantum-cryptography/KAT/tree/main/MLKEM)
kindly contributed by Kris Kwiatkowski at PQShield.com, and also the tests
contributed by Filippo Valsorda [here](https://github.com/C2SP/CCTV/tree/main/ML-KEM).

### Minimal dependencies and SBOM

In line with SPARK's design as a "bare metal" programming language,
this implementation has only two dependencies:

* LibKeccak - a SPARK implementation of SHA3 from Daniel King. This is imported
as a sub-module of this repository.

* GNU libc. The compiler generates calls to memset() (for initialization of array objects)
and memcpy() (for assignment and concatenation of arrays) and nothing else.

No other components of the Ada runtime library are used.

## Not Goals

### Performance

Performance is not a design goal of the current implementation.
Benchmarks and potential performance improvements may be added in the future.

At this stage, there has been no attempt at all to optimize performance of this code.
The code follows the intent and letter of the specification, even where this might
involve some overhead.

## To Do

The code currently implements ML-KEM-768, and executes the tests for that
variant only.

The code does compile, prove, and run fine if you change the values of
the K, Eta_1, Eta_2, DU and DV constants in
[mlkem.ads](https://github.com/awslabs/LibMLKEM/blob/660ddd586851b401ef44ed49ac82e7af816b3310/spark_ada/src/mlkem.ads#L24) to select the
appropriate values for ML-KEM-512 and ML-KEM-1024, but I have not
automated that choice and added test programs for those variants yet.

In the longer term, the whole package could be made to be generic
over the five main parameters.

## Verification Status

### Proofs

The SPARK Toolset verifies the goals stated above (memory-safety, type-safety,
and absence of UB), and is "sound and complete" in
that all verification conditions are discharged automatically, and we believe
there are no false-negatives based on the long-standing soundness case for the
SPARK toolset itself.

There are also a small number of proofs that go deeper, including:

* Functional correctness of the "*", "+", "-", and "ModQ" opertors for the Zq type.

* Functional correctness of the Byte_Seq_Equal function and MLKEM_Decaps.CSwap procedure.

### KATs

The main program in `tests/tkats.adb` reproduces the KATs published by PQShield
exactly. The main program `tests/tunlucky.adb` reproduces Valsorda's "unlucky sampling"
test case from [here](https://github.com/C2SP/CCTV/tree/main/ML-KEM/unluckysample). Finally,
the main program `tests/tmodulus.adb` reproduces the "bad modulus" tests for invalid EK values,
from the same source.

### Structural Coverage Analysis

A Makefile called `cover.mk` is also supplied that compiles the library
and test program with `--coverage`, runs the KATs, then runs `gcov` on the results,
so

```
cd tests
make -f cover.mk
```

generates files `tests/tkats.adb.gcov` and `obj/mlkem.adb.gcov`.

Inspection of the latter shows 100% statment coverage.
Other than that, coverage analysis yields little useful information.

### Worst-case memory consumption

The code is "heap free" in that it doesn't use pointers, allocators,
or de-allocation at all. Worst-case memory consumption therefore reduces
to an analysis of worst-case stack usage (WCSU).

The "GNATStack" tool can be used to compute worst-case stack usage,
although GNATStack does not ship as standard as part of the GNAT/GCC
compiler or the SPARK Toolset.

At -O1 Optimization, using GCC 13.1.0 on ARM64 macOS, worst-case
stack usage is reported as

```
30432 bytes for MLKEM.MLKEM_KeyGen
29408 bytes for MLKEM.MLKEM_Decaps
25808 bytes for MLKEM.MLKEM_Encaps
```

reflecting the size of the keys, ciphertext and intermediate
results needed by the top-level functions.

The `stack.mk` makefile produces WCSU results for the three main
entry points. Run `make -f stack.mk` to reproduce if you happen
to have the GNATstack tool available.

### Code Size - binary and source

Run `make -f size.mk` to get binary code size results for the library at
various optimization levels. These figures do _not_ include the
LibKeccak library for SHA3.

For example, At -O3, the MLKEM package generates 11360 bytes
of executable code and requires 1096 bytes of read-only constants.

In terms of source lines, the "GNATMetric" tools reports the MLKEM
package as containing 811 logical lines of code, comprising
322 statements and 489 declarations. The `gcov` tool reports
555 source lines that actually generate executable code.

## Getting the tools

This library was developed on an Apple M1-based MacBook Pro,
running macOS Ventura. Results have also been reproduced on
Intel x86_64 running Ubuntu 22.04. Your mileage on
other platforms may vary.

To compile and reproduce the proofs, you need:

1. The "Alire" Ada package manager and builder tool.
2. A recent build of GCC that has the Ada compiler enabled, including the "gprbuild" build tool.
3. The SPARK verification tools if you want to reproduce the proofs.

Binaries of the tools are available from:

### Intel-based macOS

[Alire tool](https://alire.ada.dev/)

[GCC 13.1.0 for x86_64/macOS](https://github.com/simonjwright/distributing-gcc/releases/tag/gcc-13.1.0-x86_64)

[SPARK Toolset 12.1.0 for macOS](https://github.com/alire-project/GNAT-FSF-builds/releases/tag/gnatprove-12.1.0-1)

### Apple Silicon/ARM-based macOS

[Alire tool](https://alire.ada.dev/)

[GCC 13.1.0 for ARM/macOS](https://github.com/simonjwright/distributing-gcc/releases/tag/gcc-13.1.0-aarch64-2)

[SPARK Toolset 12.1.0 for macOS](https://github.com/alire-project/GNAT-FSF-builds/releases/tag/gnatprove-12.1.0-1)

### Intel Linux (Ubuntu 22.04 or similar)

1. Install extra command-line tools, libraries, and the CVC4 prover:

```
sudo apt install unzip make libc_dev cvc4
```

2. Download the "Alire" Ada package manager:

```
wget https://github.com/alire-project/alire/releases/download/v1.2.2/alr-1.2.2-bin-x86_64-linux.zip
```

then use "unzip" to decompress it. Add the "alr" binary to your PATH. Log out and
back in again to let the new PATH work.

3. Use "alr" to install GNAT and GPRBUILD

```
alr toolchain --select
```

and pick the latest release of "GNAT_Native" and "GPRBUILD" tools to install.

4. Use alr to download the SPARK toolset below $HOME

```
cd
alr get gnatprove
```

5. Add GNAT, gprbuild, and gnatprove to PATH.

Locate GNAT and gprbuild under $HOME/.config/alire/cache/dependencies/*/bin

For example, in my $HOME/.profile, I have
```
# Alire
PATH=$HOME/tools/bin:$PATH
# GNAT
PATH=$HOME/.config/alire/cache/dependencies/gnat_native_13.2.1_788a01f9/bin:$PATH
# GPRBUILD
PATH=$HOME/.config/alire/cache/dependencies/gprbuild_22.0.1_24dfc1b5/bin:$PATH
# SPARK
PATH=$HOME/gnatprove_13.2.1_28fc3583/bin:$PATH
```

### IDEs and Visual Studio Code

An IDE is strictly optional. No IDE is required to compile the code or reproduce the proofs.

The best IDE for SPARK is probably Visual Studio Code. There is an implementation of the
[Language Server Protocol for Ada](https://marketplace.visualstudio.com/items?itemName=AdaCore.ada)
that provides most common features.

It's best to compile the code first, so that VSCode can pick up the cross-reference
information generated by the compiler.

## Cloning, building and running the tests

### Clone this repo and initialize submodules

```
git clone https://github.com/awslabs/LibMLKEM.git
cd LibMLKEM
git submodule init
git submodule update
```

### Initial configuration and build of LibKeccak

```
cd spark_ada/libkeccak
alr build
```

### Build LibMLKEM

```
cd spark_ada
gprbuild -Pmlkem
```

should result in lib/libmlkem.a

### Compile and run KATs

```
cd tests
make -f fast.mk
```

should result in:

```
--- Building LibMLKEM ---
cd ..; gprclean -Pmlkem; gprbuild -Pmlkem -XMLKEM_BUILD_MODE=O2 -XMLKEM_RUNTIME_CHECKS=disabled -XMLKEM_CONTRACTS=disabled
Compile
   [Ada]          mlkem.adb
   [Ada]          mlkem-debug.adb
   [Ada]          mlkem-tests.adb
   [Ada]          t.adb
Build Libraries
   [gprlib]       mlkem.lexch
   [archive]      libmlkem.a
   [index]        libmlkem.a
--- Building tkats ---
gprbuild -Ptkats -XMLKEM_HOSTOS=Darwin
Compile
   [Ada]          tkats.adb
   [Ada]          tunlucky.adb
   [Ada]          tmodulus.adb
Bind
   [gprbind]      tkats.bexch
   [Ada]          tkats.ali
   [gprbind]      tunlucky.bexch
   [Ada]          tunlucky.ali
   [gprbind]      tmodulus.bexch
   [Ada]          tmodulus.ali
Link
   [link]         tkats.adb
   [link]         tunlucky.adb
   [link]         tmodulus.adb
-macosx_version_min has been renamed to -macos_version_min
--- Running tkats ---
./tkats >new.txt
--- Running tunlucky ---
./tunlucky >unlucky_results.txt
--- Running tmodulus ---
./tmodulus >modulus_results.txt
--- Diffing PQShield KAT results - blank response means success  ---
diff new.txt ../../KAT/MLKEM/kat_MLKEM_768.rsp
--- Diffing Unlucky KAT result - blank response means success  ---
diff unlucky_results.txt unlucky_ref.txt
--- Diffing Modulus KAT result - blank response means success  ---
diff modulus_results.txt modulus_ref.txt
```

showing no differences between the computed results and the reference results.

## Reproducing the proofs

The configuration and options for the proof tools are stored in
the `mlkem.gpr` file.  Reproducing the proof of just the
MLKEM package:

```
cd spark_ada
gnatprove -Pmlkem -u src/mlkem.adb
```

That should show lots and lots of proofs marked with "Info" indicating success, and
zero "Warning" or "Error" lines.

A more details summary of the proof can be inspected in `obj/gnatprove/gnatprove.out`
In short:

```
Summary of SPARK analysis
=========================

-------------------------------------------------------------------------------------------------------------------------
SPARK Analysis results        Total         Flow                                           Provers   Justified   Unproved
-------------------------------------------------------------------------------------------------------------------------
Data Dependencies                30           30                                                 .           .          .
Flow Dependencies                 .            .                                                 .           .          .
Initialization                  127          127                                                 .           .          .
Non-Aliasing                      .            .                                                 .           .          .
Run-time Checks                 263            .                 263 (CVC4 3%, Z3 92%, altergo 5%)           .          .
Assertions                      125            .    125 (CVC4 5%, Trivial 6%, Z3 78%, altergo 11%)           .          .
Functional Contracts             49            .              49 (Trivial 20%, Z3 73%, altergo 8%)           .          .
LSP Verification                  .            .                                                 .           .          .
Termination                       .            .                                                 .           .          .
Concurrency                       .            .                                                 .           .          .
-------------------------------------------------------------------------------------------------------------------------
Total                           594    157 (26%)                                         437 (74%)           .          .
```

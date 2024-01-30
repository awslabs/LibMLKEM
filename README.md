# LibMLKEM - A new, formal reference implemenation of FIPS 203 ML-KEM

This library presents a new and formally verified implementation of
FIPS 203 ML-KEM (the algorithm formerly known as Kyber),
as specified in the 24th August 2023 Draft of FIPS 203.

The goals of producing these implementations are:

* To act as a vehicle for detailed review of FIPS 203.

* To produce a reference implementation of ML-KEM which is
completely independent of all other known implementations of Kyber.

* To test the capability of contemporary formal languages and verification
tools, such as [SPARK](https://www.adacore.com/sparkpro),
[CBMC](https://diffblue.github.io/cbmc/) and [Kani](https://github.com/model-checking/kani),
and to act as a challenge problem for those languages and tools.

* To act as a set of verification challenges for the underlying SMT provers, in particular CVC5.

* As a demonstration of "hybrid" static and dynamic verification. In particular,
our goal is static proof of the absence of undefined behaviour,
memory-safety, and type-safety, while dynamic known-answer tests (KATs) are used to demonstrate
functional correctness.

## Important warning

These implementations are absolutely NOT intended for production or any use
in a "high assurance" setting. In particular:

* While the code may be written in a "constant time" style, this property is not formally verified at
the level of the generated code and micro-architecture, and is not guranteed to be preserved by all compilers.

* Secondly, intermediate values are not sanitized at present, as required by FIPS 203 3.3 (line 699)

* Finally, performance is unlikely to be competetive with other, more optimized, implementations.

# Languages and tools

At this point, the first implementation is in the SPARK Ada subset -
a subset of Ada that is amenable to formal verification with the
SPARK Pro toolset. The SPARK implementation meets all of the
verification goals stated above, ands also provides static verification
of worst-case stack usage, and structural coverage analysis of the KATs.

See the README file in the `spark_ada` subdirectory for more
information.

Additional implementations and verification using other languages and
tools such  Dafny, CBMC (for C) and Kani (for Rust) may follow.

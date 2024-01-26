# The Lean Standard Library Roadmap

## Vision

Lean needs a mature standard library that is designed for the entire
Lean user base.  Particular communities, such as the math community, may
have their own common libraries, but standard will provide the common
set of definitions, theorems, and tactics to facilitate collaboration
across the Lean user base.

Standard will be the default library for Lean, and be a key part of the
user's experience.  Standard definitions and documentation must be
designed with new users in mind as tutorials and other new user
documentation should be able to assume Std is in scope.  Std must be an
exemplar library for writing good documentation, testing and other
extensions in Lean.  Std must stay up to date with Lean including
support for all Lean release candidates. Std must also provide a stable
interface so packages can efficiently upgrade to new versions.

The scope of the standard library includes the following areas:

 * Tactics for **proof automation**
 * **Data structure libraries** for functional and
   concurrent programming.
 * Monadic transformers and **verification support**.
 * **Broadly useful typeclasses** with or without lemmas.
 * **IO operations** for concurrency, file system operations, launching
   new processes and networking.  The IO layer should support both
   synchronous and asynchronous operations.
 * **Usability extension mechanisms** including commands for finding lemmas,
   providing hints, linting, and and other more speculative automation.
 * **Metaprogramming operations** that help build new tactics.

## Type Classes Standardization.

Lean needs typeclasses for common properties such as associativity so
that tactics that depend on common properties can be writen
independently of the operations that satisfy those properties.  Mathlib
provides many of the classes, but the classes tend to be specialized for mathematical purposes rather than programming and other development purposes.  The standard
library will need to provide various type classes for algebraic
properties.  As part of introducing the new classes, we will work with
Mathlib maintainers to minimize disruption for Mathlib.

## Lemma Completeness

The data types in Lean and standard should have a comprehensive and
consistent set of lemmas for reasoning about datatypes in Lean core and
the standard library.  For example, operations that return lists should
have lemmas about how to interpret the length and contents of the
returned list.

To help ensure this, we will be building lightweight linting tooling to
specify and validate policies such as every operation intended for
specifications (rather than meta-programming) has lemmas about the
results of that operation.  These will be run to validate the presence
of lemmas, the naming schemes, and help produce documentation.

## Monadic Verification

Lean provides strong support for monadic programming but does not
currently provide similiar capabilities for monadic verification.  The
standard library should provide monadic verification capabilities
including pre and post-conditions of monadic code as well as
loop-invariants.  Key challenges that will need to be addressed include:
(1) ensuring a consistent experience when verifying code in different
monads while allowing the pre and post-conditions to refer to monadic
state; (2) use of symbolic execution to unfold large monadic
computations while ensuring verification formulas are tractable; (3)
addressing some foundational issues with references in `ST` and `IO`.

### Primitive data types

Leah has builtin support for a variety of primitive types including
natural numbers, unsigned fixed-width integers (e.g., `UInt8`),
double-precision floating point numbers, `String`, arrays (including
scalar arrays), and other types.  This builtin support improves
efficiency over the generic object representation and can facilitate
better interoperability between Lean and C code.

The standard library and Lean should additional types to improve the
interoperability of Lean with other languages.  In particular, Lean
should support fixed precision *signed* integers including `Int8`,
`Int16`, `Int32` and `Int64`.  We also aim to provide aliases from C
primitive types such as `int`, `long`, `ptrdiff_t` etc to facilitate
Lean and C integration.

### Data structures

The standard library should provide common data structured needed in
applications including ordered-maps, hash tables, arrays, lists, tries,
sequences.  These need to be both performant and come with lemmas so
they can be easily reasoned about in specifications.  Lean's runtime
supports destructive updates when data structures are not shared, and
the standard library needs to provide data structures suitable for both
good shared and destructive use-cases.  Furthermore, Lean provides
concurrency primitives, and the standard library needs to design data
structures for concurrent accesses and updates.

## Asynchronous IO

Lean currently only provides IO functions that block the kernel thread
while executing.  Unfortunately, this doesn't scale well in applications
that involve large numbers of potential IO operations since each waiting
system kernel call blocks a kernel thread while it is completed.  The
standard library aims to provide a comprehensive asynchronous concurrent
IO library for file access and monitoring, networking, IPC and general
event-based programming that abstracts over the underlying kernel APIs
that Lean supports.

## Proof automation

The standard library will tactics and other proof automation for the
broader Lean community.  Our priorities in 2024 are:

* Fast and efficient arithmetic constraint solving that can be
  used independently and integrated into other decision procedures.

* Support for an Isabelle Hammer-type tactic that can call a portfolio
  of external solvers.

* Additional simplification procedures for efficient evaluation of
  ground terms arrising from industrial verification problems.

* Increased support for rewriting and simplification modulo
  associativity and commutativity.

* Library search routines such as `exact?` and `apply?` for helping
  users find lemmas they do not know about.

## Documentation

The standard library will aim to provide comprehensive documentation.
For data types, this means providing documentation about the purpose of
the data type, invariants on the type's state, and operations on the
type including a description of the operation and expected performance.
We will also consider verification aspects in this documentation
including descriptions of lemmas and tactics relevant when verifying
theorems involving the data type.  For tactics, we will describe the
tactics,

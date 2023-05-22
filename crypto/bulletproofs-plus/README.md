# Bulletproofs+

An implementation of [Bulletproofs+](https://eprint.iacr.org/2020/735.pdf).
This library follows the paper's specifications and terminology, implementing
the weighted inner product proof, the range proof, the aggregate range proof,
before finally the arithmetic circuit proof.

Additionally, a system for writing arithmetic circuits has been added. This is
completely custom. It ensures consistency between usage of variables, exposes
multiplication and a generally inefficient addition, and a few helpful gadgets.

This library is written to be curve agnostic. It can be used with secp256k1,
Ed25519, the pasta curves, or tevone.

## Status

Several optimizations are possible, such as:

- Removal of scalar matrix for a more direct structure
- Support for batch verification
- Removal of `Circuit::prove` and `Circuit::verify` for simply `Circuit::compile`
- More post-processing of constraints within `Circuit::compile`
- Implementation of ECC addition via the constraints from
  [Curve Trees](https://eprint.iacr.org/2022/756.pdf) A.4
- Hand-written constraints in the currently provided gadgets (instead of the
  automatically generated ones)
- More efficient interim calculations

Despite that, this library is performant enough to write and work with circuits.
Accordingly, optimization has been delayed until after the initial proof of
concept is ready.

This library runs post-processing passes on its constraints which are slow.
One of the noted optimizations is to compile-once, instead of compiling per
instance. If the constraints are largely hand-written, these post-processing
passes (and their complexity) can be removed. This decision will need to be made
when the rest of the library is sufficiently optimized to enable evaluation.

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

- Implementation of a proper vector commitment scheme
- Removal of `Circuit::prove` and `Circuit::verify` for simply `Circuit::compile`
- Post-processing of gates/constraints in `Circuit::compile`
- Reduction of the amount of `clone`s

Despite that, this library is performant enough to write and work with circuits.
Accordingly, optimization has been delayed until after the initial proof of
concept is ready.

This library uses asserts instead of `Result`. It also has extraneous asserts
which should be moved to debug.

The included vector commitment scheme code was largely tacked on and is
accordingly much uglier than the rest of the code in this library. It could use
a lot of love.

The transcript policies of this library need to be reviewed.

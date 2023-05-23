# Curve Trees

An implementation of [Curve Trees](https://eprint.iacr.org/2022/756), with some
modifications.

## Modifications

- This library is premised on BP+, not BP, which offers a proof for an identical
  relationship as expected from BP.
- It's planned to use the ECC addition provided by BP+. At time of writing,
  the BP+ ECC addition gadget uses the complete Weierstrass formulas, not the
  method described in A.4.

## Status

- An in-memory tree is implemented. A production usage would require:
  1) Moving the paths to the DB.
  2) A more-efficient in-memory algorithm. The current one grows by power of
     two, and doesn't archive no longer needed left hand nodes.
  3) A pop algorithm, so reorgs can be successfully handled.

- This library uses asserts instead of `Result`. It also has extraneous asserts
  which should be moved to debug.

## Notes

- The paper describes Pedersen hashes as native to Bulletproofs. While they are,
  somewhat, neither BP nor BP+ allow writing constraints around them. The
  authors modified their fork of dalek's Bulletproofs to support such
  constraints. This has yet to be formalized, though a write-up can be found
  [here](https://hackmd.io/6g5oC5xWRLOoYcTnYBuE7Q).

  If the idea passes an initial sanity check, it'll be used. Before deployment,
  formal proofs and peer review would be needed. Alternatively, `h + b`
  additional Bulletproofs can be used, where `h` is the amount of Pedersen
  hashes needed and `b` is the amount of Bulletproofs used for the circuit.

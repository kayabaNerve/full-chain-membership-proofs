# Curve Trees

An implementation of the ideas behind
[Curve Trees](https://eprint.iacr.org/2022/756), albeit not the exact protocol.

This library is premised on BP+, not BP, which offers a proof for an identical
arithmetic circuit relationship as BPs. Despite this, Curve Trees actually
expects a distinct relationship supporting vector commitments. The authors notes
can be found [here](https://hackmd.io/6g5oC5xWRLOoYcTnYBuE7Q).

The BP+ library utilized implements its own vector commitment scheme pending
formalization of the author's work.

This work uses the BP+ library's provided ECC gadgets, which include a DLog PoK
which is roughly 33% more efficient than the incomplete addition series
described in the Curve Trees paper.

## Status

- An in-memory tree is implemented. A production usage would require:
  1) Moving the paths to the DB.
  2) A more-efficient in-memory algorithm. The current one grows by power of
     two, and doesn't archive no longer needed left hand nodes.
  3) A pop algorithm, so reorgs can be successfully handled.

- This library uses asserts instead of `Result`. It also has extraneous asserts
  which should be moved to debug.

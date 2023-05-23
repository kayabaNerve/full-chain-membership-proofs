# COPZ DLEq

An implementation of
[discrete logarithm equality across groups](https://eprint.iacr.org/2022/1593).

This library is tailored for:
- Proving equality of Pedersen commitments, assumed to be prior proven to
  containing just 64-bit values.
- Curves with 194 to 256 bits

## Status

The paper cited needs peer review. This implementation is constant-time yet
likely can be significantly optimized, such as with batch verification.

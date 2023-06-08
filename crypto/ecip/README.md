# EC IP

An implementation of elliptic curve divisor construction, intended for Eagen's
[EC IP work](https://eprint.iacr.org/2022/596).

## Status

This library should be accurate, yet doesn't support odd amounts of points.
This is theoretically possible, there's simply an unresolved quirk which has
yet to be identified.

This library uses asserts instead of `Result`. It also has extraneous asserts
which should be moved to debug.

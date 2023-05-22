# Tevone

Implementation of tevador's first efficient cycle candidate from
https://github.com/monero-project/research-lab/issues/100#issuecomment-1435944171.

## Status

This library should be complete and constant time. It was implemented using
crypto-bigint's Residue type. While that enables basic tests for accuracy, it's
no where near performant enough for benchmarking, nor does it take advantage of
the form of the curve's primes *which is why this curve was chosen in the first
place*.

In order to be used in production, this library needs to be rewritten with
custom field implementations.

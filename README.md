# Curve Trees

This branch hosts a curve trees proof of concept, built with the explicit goal
of being transformed into an deployable library.

The crypto libraries are largely copied from Serai. Unique to this effort are:

- tevone: An implementation of the first curve cycle mentioned in
  https://github.com/monero-project/research-lab/issues/100#issuecomment-1437597717.
- ecip: Construction of elliptic curve divisors, intended for usage as commented
  by Eagen in their EC IP work.
- bulletproofs-plus: An implementation of BP+, keeping strictly to the paper.
- curve-trees: An implementation of curve trees.
- copz-dleq: An implementation of COPZ's cross-group DLEq proof, enabling Monero
  to move to a curve cycle.

The READMEs of each provide further context on their status.

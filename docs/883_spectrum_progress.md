# E883 spectrum: remaining work

Status, 2026-09-23: the exact spectrum is still open. The complete Lean lower
bound includes all positive orders congruent to 1 or 2 modulo 3 (including 7).
Order 3 is excluded in Lean.

## An explicit idempotent model of order 21

The following new witness was independently checked in Python but has not yet
been formalized or added to the proved spectrum catalogue. On Z/21 define

\[
 x\diamond y=x+f(y-x)
\]

with f, listed at arguments 0 through 20, equal to

```
0,4,11,13,1,9,19,8,7,5,17,2,18,3,16,20,14,10,12,6,15
```

Idempotence is f(0)=0. Translation equivariance reduces E883 to the 21 checks

\[
 f\bigl(f(d)+f(d-f(d))-d\bigr)=-d\pmod {21}.
\]

All pass. This supplies an order divisible by three outside the existing loop
family. Because the model is idempotent, it can also be used in future pairwise
balanced gluing constructions.

## Limits of the searches

A finite-domain Z3 search with Latin constraints reported that no six-element
E883 quasigroup exists. Finite E883 magmas are quasigroups, but this solver result
has not been turned into a Lean exclusion certificate. Unrestricted searches at
orders 9 and 12 timed out and establish neither existence nor nonexistence.
An independent one-hot Latin-square SAT encoding also refuted order 6. At
orders 9, 12, and 15 it reached a 200,000-conflict budget without a result.

A separate complete SAT search within the restricted family of cyclic,
idempotent operations x diamond y = x+f(y-x) found no examples at orders
6, 9, 12, 15, or 18. Those answers only exclude this restricted family; they do
not exclude general E883 models. Searches in that family at orders 24, 27, and
30 reached their conflict budgets without a result.

No complete characterization is claimed here. The unresolved multiples of
three are the main obstacle to an exact spectrum.

# Five central vertices at minimum four exclude first-output degree seven

Research note, 19 September 2026. This is an analytic finite E1485
proof, not yet formalized in Lean.

**Theorem.** Suppose the minimum translation degree is four and
there are exactly five central vertices. The least degree of a
noncentral product of two tops is five or six, not seven.

This is the `r=4` case of the stronger
[one-extra-central-vertex theorem](1485_one_extra_central_first_output_gap.md):
for every `r≥4`, exactly `r+1` central vertices force
`r<p≤2r−2`.

The general proof uses the row-local degree bound, the regular
central-middle matrix of a first output, and the elementary fact
that an exact crown intersection family of at least four pairs
cannot contain a singleton set. No finite enumeration is used.

The earlier [five-central partition note](1485_min_four_five_central_partitions.md)
retains the additional one-square/four-domino classification and
the conditional central-profile count `(9,3,3,1)`. Those stronger
profile details are no longer needed for this exclusion.

First-output degrees five and six, and the five-central branch as
a whole, remain open in this note. No equality between the least
noncentral ordinary degree and the first top-output degree is assumed.

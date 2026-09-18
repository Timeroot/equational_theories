# Minimum degree two: complementary degree four is sharp-regular

Research note, 18 September 2026. This is a pen-and-paper consequence
of the [full central core](1485_full_central_core.md), which is known
for every finite E1485 magma of minimum degree two, and the
[degree gaps and low-degree regularity](1485_min_two_neighbor_gap.md).

**Theorem.** In a finite E1485 magma of order `n` and minimum
translation degree two, every vertex of degree `n/4` has exactly two
sharp predecessors and two sharp successors.

This local argument has been superseded by the
[general full-core sharp-regularity theorem](1485_full_core_sharp_regularity.md),
which proves the conclusion at every degree. The overlap estimate below
remains valid but is no longer needed to establish regularity.

## The strengthened overlap bound

Write `B` for the canonical two-regular relation. For any vertex `a`,
let `B(a)={b,c}`, ordered so that `d(b)≤d(c)`, and put `j=d(b)`.
The full-core overlap theorem gives

\[
 j=\frac n{d(a)},\qquad
 |\operatorname{Row}(b)\cap\operatorname{Row}(c)|=d(c)-j.
 \tag{1}
\]

The top successor sets of the two canonical neighbors `b,c` partition
the top class. In particular they are disjoint. The intersection in
(1) therefore excludes both top successors of `b`, giving

\[
 d(c)-j\le j-2,
 \qquad\boxed{d(c)\le2j-2.} \tag{2}
\]

This improves the earlier bound `d(c)≤2j`. The column-dual bound
holds for `B^-(a)` as well.

## Applying the bound at complementary degree four

Suppose `d(a)=n/4`. Its smaller canonical successor has degree four.
Equation (2) bounds its other canonical successor's degree by six.
The only possible degrees between four and six are four and six,
because degree five is excluded by the full-core gap theorem.

If both successors have degree four, both edges are sharp by the
degree-product criterion. If one successor `c` had degree six, it
would itself be sharp-regular by the low-degree regularity theorem.
Every canonical predecessor of `c` would then be sharp. Since
`a B c`, this would force `d(a)d(c)=n`, contrary to
`(n/4)·6>n`. Thus degree six cannot occur here, and both successors
of `a` are sharp. The dual argument proves the predecessor assertion.

## Consequence for the order-forty-eight degree pattern

At order 48 with minimum degree two, the possible translation degrees
are

\[
 2,4,6,8,12,24.
\]

Degrees two and 24 are sharp-regular by the central and top theorems;
degrees four and six are sharp-regular by the low-degree theorem;
the present result adds degree twelve.

If `a` has degree eight, its sharp canonical neighbors have degree
six. Equation (2) bounds any other canonical neighbor's degree by
ten. Among the occurring divisors of 48, the only possible nonsharp
canonical neighbor degree is therefore eight itself. Thus any
remaining nonsharp canonical edge has both endpoints of degree eight.
This is a restriction, not an exclusion of that last possibility.

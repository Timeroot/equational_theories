# The finite spectrum of E1489

**Status:** fully formalized in Lean, 2026-09-23. The exact theorems are
`Spectrum.spectrum_1489`, `Spectrum.Catalogue.exact_1489`, and
`Spectrum.Catalogue.exact_2098`. The stronger existence theorem
`Spectrum.idempotent_models_1489` uses only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`, with no native checks. The exact spectra
add the two existing native-checked finite exclusion certificates.

## Theorem

There is an idempotent magma of every positive order other than 2 and 4 satisfying

\[
  x=(y\diamond x)\diamond\bigl(y\diamond(x\diamond y)\bigr).
\]

There is no E1489 magma, idempotent or otherwise, of order 2 or 4. Consequently
the finite spectrum of E1489, and of its dual, is exactly
\(\mathbb N_{>0}\setminus\{2,4\}\).

## 1. Gluing idempotent models

Suppose a family of subsets (blocks) of a set X contains each unordered pair of
distinct points in exactly one block. Equip every block with an idempotent
E1489 operation. Define the operation on distinct x,y using their unique block,
and put x diamond x = x.

The resulting operation restricts to the prescribed operation on every block:
uniqueness handles distinct arguments, and idempotence handles equal arguments.
All subterms of E1489 on x,y remain in their common block. Thus E1489 holds
globally. The identity also holds when x=y by idempotence.

## 2. A flexible interval of orders

A transversal design TD(7,q) consists of seven disjoint groups of q points and
q squared transversal blocks. Every transversal meets each group once, and
every pair from different groups belongs to exactly one transversal.

Keep five entire groups, r points of the sixth group, and s points of the seventh,
where 0 <= r,s <= q. Use the seven retained groups as blocks, together with the
retained portions of the transversals. The latter have sizes 5, 6, or 7.
These blocks contain every pair exactly once: pairs in one group use that group;
pairs in different groups use their unique transversal.

If idempotent E1489 models exist at orders q, r, s, 5, 6, and 7, gluing gives a
model of order 5q+r+s. Empty groups may simply be omitted.

For q >= 7, every integer t in [0,2q] is r+s with 0 <= r,s <= q and neither
r nor s equal to 2 or 4:

- If t <= q and t is neither 2 nor 4, use (t,0).
- For t=2 or 4, use (1,t-1).
- If t>q and t-q is neither 2 nor 4, use (q,t-q).
- Otherwise use (q-1,t-q+1). Here q-1 >= 6 and the second summand is 3 or 5.

Thus, in a strong induction on n, any available TD(7,q) with
5q <= n <= 7q constructs the required model: all group sizes are strictly
smaller than n.

## 3. Transversal designs at a dense family of orders

For a field F with at least seven elements choose distinct c_0,...,c_6 in F.
The groups are {i} times F and the transversal indexed by (a,b) in F squared is

\[
  \{(i,a+c_i b):0\leq i<7\}.
\]

Two points in different groups determine a unique (a,b), by subtracting their
equations and dividing by the nonzero difference of the c_i.

Products of transversal designs give transversal designs: take group coordinates
and transversal parameters componentwise. In particular TD(7,q) exists for

\[
  q=b\,7^k,\qquad
  b\in\{7,9,11,13,17,23,31,41\},\quad k\geq0.
\]

For the bases use the prime fields, except for 9, where the field is
F_3[T]/(T squared + 1). Then repeatedly take the product with the order-seven
design.

The intervals [5b,7b) for these eight bases cover every integer from 35 through
286: successive intervals overlap. Multiplication by seven leaves overlap
between consecutive scales, since the last interval at one scale ends at 287
and the first at the next begins at 245.

More explicitly, every n >= 35 admits q of the displayed form with
5q <= n < 7q. For n<287 this follows from the eight intervals. For n>=287,
apply induction to floor(n/7), then multiply its q by seven.

## 4. Finite seeds

Explicit idempotent tables cover every positive order below 35 except 2 and 4.
The [checked data file](../data/spectrum/1489_idempotent_seeds.json) records the
full tables; their size is small enough for ordinary Lean kernel reduction. They can be obtained as follows.

- Orders 3, 6, and 8 use finite tables already in the spectrum witness cache.
- At orders 5, 7, 11, 17, 19, 23, and 25 use
  x diamond y = (1-b)x+by modulo n, choosing a root of b cubed - b + 1 = 0.
- Orders 10 and 12 use newly found finite tables.
- Orders 14 and 20 use x diamond y = x+f(y-x) modulo n, with f respectively:

```
14: 0,8,2,3,11,3,7,13,8,9,1,2,9,13
20: 0,4,17,5,2,5,4,2,3,2,6,9,6,16,8,18,7,17,18,11
```

- A TD(3,m), given by triples (a,b,a+b) over the cyclic group of order m,
  gives order 3m from an order-m model. Adding one common point to the three
  group blocks gives order 3m+1 from an order-(m+1) model. These cover all
  remaining multiples of three and orders congruent to one modulo three below 35.
- At order 26 use TD(5,5), adjoining one common point to its five group blocks.
  The group blocks have size 6 and the transversal blocks have size 5.
- At order 29 use a checked group-divisible triple design with eight groups of
  size 3 and one group of size 5. At order 32 use one with four groups of size 6
  and one group of size 8. Fill each group with its idempotent model and each
  triple with the order-three model.

The certificates were checked by evaluating idempotence and E1489 on every
ordered pair. Their discovery procedures are not assumptions of the proof.

## 5. Conclusion

Strong induction, Sections 2 and 3, and the seeds of Section 4 construct
idempotent E1489 models at every positive order other than 2 and 4. The existing
Lean exclusions at orders 2 and 4 apply without an idempotence assumption.
Reversing multiplication gives the same spectrum for the dual law.

No asymptotic design-existence theorem or unproved bound on its threshold is
used: the transversal designs, interval coverage, and finite starting range are
all explicit.

## Lean sources

- [Idempotent1489.lean](../equational_theories/Spectrum/Idempotent1489.lean):
  idempotent models and gluing along pairwise balanced blocks.
- [TransversalSeven.lean](../equational_theories/Spectrum/TransversalSeven.lean):
  field designs, products, the dense sequence of orders, and splitting sizes.
- [TransversalGluing1489.lean](../equational_theories/Spectrum/TransversalGluing1489.lean):
  two truncated groups, pair uniqueness, and the interval construction.
- [Idempotent1489Seeds.lean](../equational_theories/Spectrum/Generated/Idempotent1489Seeds.lean):
  ordinary-kernel checks of all finite seeds, generated reproducibly by
  `scripts/spectrum_1489_seeds.py`.
- [Equation1489.lean](../equational_theories/Spectrum/Equation1489.lean):
  strong induction, the all-orders existence theorem, and exact spectrum.

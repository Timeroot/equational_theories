# E63 order 158: conditional constructions and search record

**2026-09-24: still open.** No order-158 model was found in this search pass.
No nonexistence result for order 158 is claimed. All searches from this pass
have stopped. The results below are computational research, not Lean proofs,
and do not change the website's proved spectrum.

The twelve models recovered in the preceding pass have orders
22, 29, 34, 46, 47, 58, 62, 74, 106, 110, 114, 118. They instantiate Bennett's
published constructions, rather than direct model-finder searches for complete
E63 tables of those orders. Solvers found the small design ingredients used
for 46 and 47; the other ten use explicit constructions and previously available
ingredients. Every resulting table is checked directly against E63 and
Latinness. Bennett's Theorem 5.50 itself lists 158 as a possible exception.

The [search manifest](../data/spectrum/63_order158_search.json) records the
restricted searches and their limits. The
[partial-table search and checker](../scripts/spectrum_63_partial.py) preserves
three sufficient construction routes. None of their missing ingredients has
been found.

The [small source archive](../data/spectrum/63_order158_search_sources.tar.gz)
retains the original exploratory scripts and their result records. Those
scripts refer to the original temporary work directory; use the portable
script below for new partial-table searches. The archive contains no negative
proof certificates.

## Partial tables

Work in the equivalent finite E229 presentation

\[
  (y*(y*x))*y=x.
\]

A single-hole partial table on n points with an h-point hole P is undefined
exactly on P×P. Each row and column indexed by a point of P permutes the
complement of P. Each other row and column permutes the whole point set.
E229 holds whenever x and y are not both in P, with all three products defined.
**Outside points need not be idempotent** unless that is an explicit search
restriction.

A partial table of type `s₁^a₁ … sₖ^aₖ` instead partitions its whole point set
into holes of the indicated sizes. Entries are defined exactly between
different holes. Each row and column permutes the complement of its hole,
and E229 holds on all pairs from different holes. In particular, a defined
product is outside both input holes. These are the partitioned incomplete
Latin squares used below.

## Three sufficient ingredients

1. **An order-34 E229 model containing an order-3 submodel.** Equivalently,
   find a single-hole partial table of order 34 with hole size 3, then fill the
   hole using the known order-3 model. The singular product with an idempotent
   order-5 model and the known order-31 model gives
   `5*(34−3)+3 = 158`. Our existing order-34 model has no order-3 submodel:
   all 5,984 three-element subsets were checked for closure. A different
   order-34 table is needed for this route.

2. **A single-hole partial table of order 25 with hole size 6.** Take TD(8,19),
   whose eight groups have size 19, and add six common points P. Fill seven
   groups together with P using the partial table, leaving P×P undefined.
   Fill the last group together with P using the complete order-25 model
   `5×5`, which supplies P×P too. Fill transversal blocks using the idempotent
   order-8 model. This has `8*19+6 = 158` points.

   No order-6 model is required. The last filling may send products from P×P
   outside P. Every E229 product involves y. If y is outside P, no product
   uses two points of P. If y is in P and x is in one of the first seven
   groups, left multiplication by y stays in that group. The remaining
   instances take place entirely in the complete last filling. Row and
   column permutations follow from the partial Latin conditions and the
   transversal design.

3. **A 23-point partial table of type `3^7 2^1`.** Start with TD(8,7).
   Give all points in its first seven groups weight 3. In its last group,
   give three points weight 3, one point weight 2, and the remaining three
   points weight 0. The inflated groups have sizes `21^7 11^1`, totaling
   `7*21+11 = 158`.

   Inflate each transversal block using a partial table of type `3^7`,
   `3^8`, or `3^7 2^1`, depending on the last point's weight. The first two
   come from direct products of the idempotent order-7 or order-8 model
   with the order-3 model, deleting products within the 3-point fibers.
   The third is the missing ingredient. Fill the seven 21-point groups
   using the known `5*(5−1)+1` model, and the 11-point group using the affine
   order-11 model. Between different inflated groups, E229 stays within a
   single inflated transversal block; within a group, its filling supplies
   the identity. The partial Latin conditions give global Latinness.

The portable script checks any supplied partial table independently before
using it. Its `assemble` command implements all three routes, evaluates every
E229 instance on the resulting 158-point table, converts by rowwise left
division, and checks every E63 instance before writing a certificate.

## Search results and limits

* Unrestricted searches for the first two partial-table ingredients each ran
  for 300 seconds in CaDiCaL, 600 seconds in a solver guided by an existing
  complete model, and about 600 seconds in Mace4. None finished with a model
  or a nonexistence result.
* The 23-point partial-table search ran for 600 seconds in CaDiCaL and
  630 seconds in a phase-guided SAT search. Neither resolved it. A further
  120 searches pinned one hole-point's translation: two sampled compatible
  permutations for each of 60 possible cycle-length partitions. Seventy-four
  were reported UNSAT and 46 timed out. These are **not** all permutations
  relative to the fixed hole partition, so this is not an exhaustive split.
  Eleven more strongly pinned cases were also reported UNSAT.
* Alternative constructions were blocked by restricted ingredients: partial
  orders 10 with a 2-hole and 11 with a 3-hole, both requiring all eight
  outside points to be idempotent, were reported UNSAT. For a partial order-15
  table with a 4-hole and eleven outside idempotents, all six canonical
  first-row cycle types were reported UNSAT. In that last setting, a hole
  point's translation has no 1- or 2-cycles: a fixed point of its right
  translation, combined with outside idempotence and E229, would identify
  an outside point with the hole point. Since R=L⁻², the six partitions of
  11 into parts at least 3 give the stated split.
* A cyclic pairwise balanced design on two copies of the integers modulo 79,
  with blocks of sizes 5, 7, and 8, would also suffice. A restricted pattern
  with an additional multiplicative symmetry of order 3 was reported
  infeasible. Its best near-design misses the required difference balance
  by three duplicate differences. Six less restricted 900-second local
  searches did not repair it. Eleven alternative seven-base-block split
  patterns, searched for 180 seconds each, also gave no design. These are
  bounded searches, not exhaustive exclusions of cyclic designs.
* Adding a seventh column to our specific six-column difference matrix over
  the integers modulo 21 was reported UNSAT. A suitable alternative matrix
  would give TD(8,21), whose last group could be truncated to 11 points,
  yielding 158. Only the extension of that particular matrix was excluded.

The restricted UNSAT results in this pass have **no independently checked
proof traces**. They should not be confused with the checked order-10 and
order-14 exclusions from earlier passes. Timeouts give no negative evidence
of nonexistence.

## Two useful necessary conditions

An E229 quasigroup Q with a proper subquasigroup P of size p has `|Q| ≥ 3p`.
For y outside P, the sets P, Lᵧ(P), and Lᵧ²(P) are pairwise disjoint.
Latin cancellation puts Lᵧ(P) outside P; E229 identifies Lᵧ²(P) with
Rᵧ⁻¹(P), which is also outside P. Injectivity of Lᵧ separates the two images.
If y is idempotent, y is outside all three sets, giving `|Q| ≥ 3p+1`.
Thus many tempting singular-product factorizations of 158 cannot work.

Also, **an order-158 E229 model must be noncommutative**. In a commutative
E229 quasigroup, each Lᵧ has cube equal to the identity. Its fixed-point
count is therefore congruent to the order modulo 3, so at order 158 every
Lᵧ would have at least two fixed points. But Latinness makes the sum of
these fixed-point counts exactly 158: for each x there is exactly one y
with y*x=x. This is a contradiction. The partial-table searches above
did not impose commutativity.

These arguments are pen-and-paper observations, not new Lean declarations.

## Reproduction

Search requires `python-sat` and `cadical` on PATH; certificate checking and
assembly use only the standard library. For example:

```sh
python3 scripts/spectrum_63_partial.py search --hole 34 3 \
  --seconds 600 --output /tmp/e63-hole34
python3 scripts/spectrum_63_partial.py search --hole 25 6 \
  --seconds 600 --output /tmp/e63-hole25
python3 scripts/spectrum_63_partial.py search --sizes 3,3,3,3,3,3,3,2 \
  --seconds 600 --output /tmp/e63-pils23
# Only if a search produced a table:
python3 scripts/spectrum_63_partial.py check /tmp/e63-hole34/result.json
python3 scripts/spectrum_63_partial.py assemble /tmp/e63-hole34/result.json \
  --output /tmp/e63-order158.json
```

Positive controls found and directly checked a single-hole order-7 table with
one hole point and a partial table of type `2^4`. The construction machinery
was checked on an order-64 inflation, an order-75 shared-hole filling, and an
order-48 singular product using known ingredients. The weighted 158-point
design's pair coverage was also checked independently of its missing table.
No successful order-158 assembly has yet been possible.

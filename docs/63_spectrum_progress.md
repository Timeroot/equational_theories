# E63: an explicit finite reduction of the spectrum problem

> Formalization update: the positive spectrum bound and all twelve recovered
> witnesses are now proved in Lean. See [the proof guide](63_lean_spectrum.md).
> The original research certificate below also records stronger pointed and
> idempotent claims, which are separate from the formalized spectrum bound.


Status, 2026-09-24: **the exact spectrum remains open**. This page preserves
the original pointed/idempotent construction argument and its independently
checked finite certificate. The resulting spectrum bound and the twelve
recovered positive orders are now formalized using a smaller set of
construction rules; see the proof guide linked above. The exclusions at
10 and 14 still have no Lean proofs.

Write S for the positive finite spectrum of

\[
  x=y\diamond\bigl(x\diamond(x\diamond y)\bigr).
\]

## Current result

There are pointed E63 models at **every order at least 159**. Here pointed
means that the model has a specified idempotent element. Below 159, the same
construction certificate leaves only the following orders unconstructed:

```
2, 6, 10,
14, 18, 22, 26, 29, 30, 34, 38, 42, 46, 47, 58, 62, 74,
90, 106, 110, 114, 118, 158.
```

Orders 2 and 6 already have Lean exclusions. Finite searches described below
exclude 10 and now also 14, without adding Lean proofs. A newly recovered paper
by F. E. Bennett supplies constructions for thirteen more of the displayed
orders. Twelve have now been reconstructed and directly checked locally:
**22, 29, 34, 46, 47, 58, 62, 74, 106, 110, 114, 118**.

Thus our replayable construction certificates still lack the positive case
**90**, which Bennett covers, and the six orders
**18, 26, 30, 38, 42, 158** left unsettled by the combination of that paper
and our checked exclusions. In particular, **order 18 is still open**.
Absence from a construction list is not a nonexistence result. The twelve new model certificates and an explicit cofinite spectrum bound
are now formalized; see [the Lean proof guide](63_lean_spectrum.md).
The older certificate below remains a separately checked research artifact;
the Lean proof uses a smaller set of construction rules.

A subsequent [order-158 search pass](63_order158_search.md) found no model.
It records three sufficient partial-table ingredients and a portable search,
checking, and conditional assembly script. The failed restricted searches do
not exclude order 158; it remains one of the six unsettled orders.

A [construction-focused pass at orders 26 and 30](63_orders26_30.md) also
leaves both orders open. It proves that ordinary singular-product and GDD
constructions cannot reach either order, gives new partial-table restrictions,
and excludes single-cycle automorphism constructions by a combination of
paper arguments and small finite certificates.

The latest six-hour order-18 search campaign ended at 11:31 UTC on
2026-09-24. Five of its six initially outstanding branches were closed:
53 of the complete 55-case split now have directly checked UNSAT traces,
and a structural reduction with separately checked certificates closes a
54th. The final branch, `nonidem-3-3-3-3-3-3`, is still unresolved, and any
surviving E229 model must be commutative. The model searches are stopped;
the machine-readable state is
[63_order18_progress.json](../data/spectrum/63_order18_progress.json).

The certificate is [63_constructions.json](../data/spectrum/63_constructions.json).
Its independent checker is [spectrum_63_research.py](../scripts/spectrum_63_research.py):

```sh
python3 scripts/spectrum_63_research.py
```

It checks 559 idempotent construction nodes and 1585 pointed construction nodes,
including every order from 159 through 1607. It uses no SAT solver. Zero is an
empty-group marker in this data, not an element of the positive spectrum.

## 1. The key improvement: filling groups need not be idempotent

Every finite E63 model has bijective left translations: the identity supplies
a preimage for every element under every left translation.

In an **idempotent** E63 model, evaluation at distinct x,y never uses a diagonal
entry. Indeed,

1. x diamond y differs from x, by injectivity of left translation by x.
2. x diamond (x diamond y) differs from y: otherwise E63 and idempotence give
   x = y diamond y = y.

Consequently all three multiplications in E63 have distinct arguments. This
permits a stronger construction than ordinary idempotent block gluing.

Take a group-divisible design: its points are partitioned into groups, and each
pair of points in different groups belongs to exactly one transversal block.
Each transversal meets any group at most once. Put idempotent E63 operations on
the transversals, and **arbitrary E63 operations on the groups**. Use the group
operation for a pair in one group and the transversal operation otherwise.

For an input pair in one group, the entire identity is evaluated in that group.
For an input pair in different groups, evaluate it in their transversal. The
two observations above ensure that every multiplication has arguments in
different groups, so the evaluation never consults a group operation. E63
therefore holds globally, even when the group operations are not idempotent.

One may additionally adjoin a single common point to every group and fill each
enlarged group with a pointed E63 model, identifying their specified idempotents.
Operations on overlaps agree, since the only overlap is that one point. Input
pairs involving the common point are evaluated in the corresponding enlarged
group. The preceding argument still handles every other pair.

The resulting model is pointed: without the added point, choose an idempotent
from one of the pointed group models; with the added point, use that point.
If all group models are idempotent, the whole model is idempotent.

## 2. Explicit construction rules

### Affine starting models

Let b be an automorphism of an abelian group satisfying

\[
  P(b)=b^5+b^4+1=(b^2+b+1)(b^3-b+1)=0.
\]

Then x diamond y = -b^3 x + b y satisfies E63. Expanding its right side gives

\[
  -b^4(1+b)x+(-b^3+b^3)y=x.
\]

Zero is idempotent. If b^3-b+1=0, the formula is
(1-b)x+b y and every element is idempotent.

These supply the following certificate rules, applied independently to each
prime power p^a dividing the desired order.

- **Idempotent:** if T^3-T+1 has a root modulo p, use that scalar on a copies
  of F_p. Otherwise this cubic is irreducible, and every a divisible by three
  is obtained using copies of F_(p^3).
- **Pointed:** if P has a root modulo p, every a is possible. Otherwise both
  its quadratic and cubic factors are irreducible. Every a >= 2 is 2r+3s,
  so products of models over F_(p^2) and F_(p^3) give order p^a.

Products of pointed models are pointed; products of idempotent models are
idempotent. These rules require only root checks in prime fields. In particular
there are idempotent models at orders 5, 7, 8, and 11.

### Transversal designs

There is a TD(k,q) whenever

\[
  k\le 1+\min_{p^a\parallel q}p^a.
\]

For a field F of order p^a, use groups indexed by distinct elements of
F union {infinity}. A block indexed by (A,B) has coordinate A+cB in a finite
group c and coordinate B in the infinity group. Two points in different groups
determine a unique block. Taking componentwise products proves the displayed
condition for general q.

The certificate also uses four explicit difference matrices, stored in
[63_difference_matrices.json](../data/spectrum/63_difference_matrices.json).
Every column-pair difference is independently checked to enumerate its finite
abelian group exactly once. Adding every group element to each matrix row,
and adjoining the row index as an extra coordinate, gives the following designs:

| q | Group | Matrix columns | Transversal design |
|---|---|---|---|
| 12 | Z/2 x Z/6 | 6 | TD(7,12) |
| 21 | Z/21 | 6 | TD(7,21) |
| 28 | Z/2 x Z/2 x Z/7 | 6 | TD(7,28) |
| 36 | Z/2 x Z/2 x Z/3 x Z/3 | 9 | TD(10,36) |

The numerical tables are reproduced from SageMath's design database, which
attributes the order-12 matrix to Hanani (1975), Lemma 3.21, and the other three
to *Handbook of Combinatorial Designs*, III.3.50, III.3.54, and III.3.59.
The checker does not import or execute SageMath; its checks establish the
required difference-matrix properties directly.

Keep k full groups and optionally r and s points of two additional groups,
where 0 <= r,s <= q. Adjoin e common points, where e is either 0 or 1.
The total order is

\[
  n=kq+r+s+e.
\]

The retained transversals have sizes between k and k+t, where t is the number
of nonempty truncated groups. If these sizes have idempotent E63 models and
the enlarged groups of sizes q+e, r+e, s+e have pointed models, Section 1
constructs a pointed model of order n. Empty groups are ignored. The same rule
constructs an idempotent model if all the group models are idempotent.

### Sharing an entire submodel

There is a useful further product rule. Let H and M be pointed E63 models of
orders h and m, with distinguished idempotent 0 in M. The product H x M
contains H x {0} as a submodel. Take k copies of this product, identify these
submodels, and use TD(k,h(m-1)) on the k disjoint remainders. Fill each
transversal with an idempotent order-k model. The argument of Section 1 still
works: operations on the common H agree; all other within-group calculations
stay in one copy; cross-group calculations use only their transversal.
The resulting pointed model has order

\[
  h\bigl(k(m-1)+1\bigr).
\]

It is idempotent if H and M are idempotent. This gives, in particular:

| Resulting order | h | m | k | Required design |
|---|---|---|---|---|
| 87 | 3 | 5 | 7 | TD(7,12) |
| 154 | 7 | 4 | 7 | TD(7,21) |
| 203 | 7 | 5 | 7 | TD(7,28) |

The checker independently constructs and evaluates the entire multiplication
tables for these three models. Order 269 follows from TD(8,36), keeping seven
full groups and 17 points of the eighth. Idempotent group models are available
at 36 and 17, and the transversal blocks have sizes seven and eight.

These are exactly the rules checked for the finite certificate. Every
construction depends on smaller orders in the same class; a pointed model may
also refer to an idempotent model of the same order.

## 3. Induction proving the explicit cutoff

The certificate supplies pointed models at every order 159 <= n < 1608.
Suppose n >= 1608, and assume all smaller orders at least 159 are available.
Put a = ceil(n/8). Among a,a+1,...,a+5 there is an integer q coprime to 30.
Every prime-power factor of q is at least seven, so TD(8,q) exists.

Let r=n-7q. Since q >= ceil(n/8), we have r <= q. Also

\[
  r\ge(8a-7)-7(a+5)=a-42\ge159.
\]

Both q and r are smaller than n and at least 159. Keep seven full groups and r
points of the eighth. Fill the groups with the pointed models supplied by the
induction hypothesis and the transversals with idempotent models of orders
seven and eight. This constructs the required n-element model.

Thus the finite certificate and this induction prove existence at every
order n >= 159. There is no appeal to an unspecified Wilson-theorem threshold.

## 4. An independently evaluated order-41 example

Use TD(5,8), with groups indexed by 0,...,4 in F_8, and adjoin one common point.
Fill each group plus that point with F_3^2 and operation u diamond v = v-u.
Fill each transversal with i diamond j = 3(i+j) modulo five.

The resulting model has 5*8+1=41 elements. All its squares equal the common
point. The research checker independently constructs the table and evaluates
all 1681 E63 instances, both Latin conditions, and the constant-diagonal
property. Order 41 was outside the affine starting family.

## 5. A smaller finite search and the exclusion of 10

For a finite E63 model define x*y to be left division, and write L_y and R_y
for translations of this new operation. E63 gives

\[
  R_y=L_y^{-2}.
\]

Equivalently, (y*(y*x))*y=x, which is E229 and is equivalent to E125 in the
finite setting. This reduces the table search to implications

```
y*x=a and y*a=b  =>  b*y=x.
```

Two consequences sharply reduce the first-row possibilities.

- The cycle of y under L_y has length one or three, because
  R_y(y)=L_y(y) and hence L_y^3(y)=y.
- L_y has no cycle of length two. If it swapped x and z, then R_y(x)=x,
  so L_x(y)=x. The preceding property implies y lies in the cycle of x
  under L_x, whose length divides three. Therefore
  R_x(y)=L_x^(-2)(y)=L_x(y)=x, contradicting L_y(x)=z != x.

Relabeling therefore makes the first row one of the canonical permutations
whose distinguished cycle has length one or three and whose other cycle
lengths are never two. At order 10 there are 23 such cases. The Latin-square
SAT encoding refuted all 23, reproducing the reported exclusion. This is a
solver result with a mathematical completeness argument for the case split;
it is not a newly checked Lean/LRAT exclusion certificate.

The reproducible search is [spectrum_63_search.py](../scripts/spectrum_63_search.py),
and its recorded order-10 results are
[63_order10_search.json](../data/spectrum/63_order10_search.json). It requires
`python-sat`:

```sh
python3 scripts/spectrum_63_search.py --order 10
```

If all elements are required to be idempotent, L_y fixes only y. This also
allows small idempotent-only exclusions, but such exclusions must not be
confused with exclusions for the full spectrum. The bounded searches originally
left order 14 unresolved; the exhaustive follow-up below now excludes it.

### Exhaustive order-14 follow-up

The runner [spectrum_63_exhaustive.py](../scripts/spectrum_63_exhaustive.py)
uses a smaller, exhaustive split:

1. If all elements are idempotent, choose any element as 0. Its left
   translation fixes precisely 0: if `L_0(y)=y`, then `R_0(y)=y`, whereas
   idempotence and cancellation in row y force `y=0`. Thus the distinguished
   cycle is a singleton and the other cycles have lengths at least three.
   There are ten partitions of 13 into such lengths.
2. Otherwise choose a non-idempotent element as 0. Its distinguished cycle
   has length three; the remaining cycle lengths are one or at least three.
   There are 26 partitions of 11 into such lengths.

Within the second case, choose 0 among non-idempotent elements to minimize
the number of fixed points of its left translation. If this number is f, every
non-idempotent row must have at least f fixed points. This is valid symmetry
breaking: the choice of 0 is made before canonically labeling its cycles.
It preserves a representative of every model, including models with no
idempotent element.

The Boolean variable `v(x,y,z)` represents `x*y=z`. Exactly-one constraints
make the table Latin. For every x,y,a,b, let A, B, C assert respectively
`y*x=a`, `y*a=b`, `b*y=x`. E229 says `A and B imply C`. Cancellation also
gives `A and C imply B` and `B and C imply A`; supplying all three clauses
improves propagation. The translation-cycle consequences proved above are
also supplied. There are no affine, associativity, submodel, or constant-diagonal
assumptions. The idempotent condition is used only in its own branch.

CaDiCaL 2.1.2 refuted **all 36 cases**, without a preset search time limit.
The strengthened run took about 80 seconds including input generation; its
longest solver call took about 47 seconds. The earlier version without the
minimum-fixed-point condition was stopped after the complete strengthened
run finished. Its incomplete cases are not used in the exclusion.

Results are recorded in [63_order14_search.json](../data/spectrum/63_order14_search.json).
The independent checker [spectrum_63_verify_search.py](../scripts/spectrum_63_verify_search.py)
regenerates every CNF, verifies the complete case list, and checks each compressed
DRAT proof with `drat-trim`. Its detailed result is
[63_order14_proofcheck.json](../data/spectrum/63_order14_proofcheck.json).
**All 36 proofs passed this independent check.** The CNF inputs, compressed
proofs, solver logs, and checker logs are retained in
[63_order14_certificates.tar.gz](../data/spectrum/63_order14_certificates.tar.gz),
with the archive hash in
[63_order14_certificates.json](../data/spectrum/63_order14_certificates.json).
This separates the mathematical completeness argument from the checked SAT
computation; neither is yet formalized in Lean.

To check the archived computation again, build `drat-trim` from commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, extract the archive, and run:

```sh
mkdir -p /tmp/e63-order14-check
tar -xzf data/spectrum/63_order14_certificates.tar.gz -C /tmp/e63-order14-check
python3 scripts/spectrum_63_verify_search.py \
  --report data/spectrum/63_order14_search.json \
  --artifact-dir /tmp/e63-order14-check \
  --checker /path/to/drat-trim \
  --output /tmp/e63-order14-verified.json
```

Controls recover E63 models of orders 3, 5, 7, 8, and 11, each evaluated directly
against the repository's E63 equation. The same encoding refutes all 12 cases
of the smaller order-10 split, and all 12 DRAT proofs were independently checked.

Immediately after the order-14 exclusion, before recovering Bennett's
constructions, the remaining local candidates were

```
18, 22, 26, 29, 30, 34, 38, 42, 46, 47, 58, 62, 74,
90, 106, 110, 114, 118, 158.
```

Excluding 14 does not exclude its multiples: in particular, order 42 remains
undecided. The construction for every order at least 159 is unchanged.

### Order-18 follow-up: additional exhaustive symmetry reductions

The next target, order 18, initially had 100 cases under the same complete
split: 25 idempotent cases and 75 non-idempotent cases. A counting improvement
below reduces this to **55 cases**. The initial pass is recorded in
[63_order18_search.json](../data/spectrum/63_order18_search.json), and the current
combined result is [63_order18_combined_search.json](../data/spectrum/63_order18_combined_search.json).
Partial refutations do not exclude order 18. The machine-readable
[progress checkpoint](../data/spectrum/63_order18_progress.json) distinguishes
solver refutations, independently checked traces, and unresolved cases. At
08:31 UTC on 2026-09-24, 53 of the 55 cases were refuted and independently checked, and two remained open:
`nonidem-3-3-3-3-3-3` and `nonidem-3-3-4-4-4`. All 53 completed main-case traces have passed independent checking,
including the two large older traces and the new `3,5,5,5` trace. No order-18
table had been found. The later Bennett construction update above reduces the
other gaps; it does not settle order 18.

Write f(x) for the number of fixed points of `L_x`. Since each column y
contains the value y exactly once, `sum_x f(x)=n`. Every idempotent element
contributes at least one fixed point. If there are any non-idempotent elements,
they cannot all contribute at least two: with I idempotent and N non-idempotent
elements that would give `sum_x f(x) >= I+2N > n`. Thus the minimum fixed-point
count among non-idempotent rows is **zero or one**. Choosing 0 to attain this
minimum removes 45 of the original 100 order-18 cases without a SAT search.
The `--minimum-fixed-bound --min-fixed` options use this smaller complete split.

If that minimum is one, every row has at least one fixed point, so the same
sum forces **exactly one fixed point in every row**. A separate strengthened
pass supplies these exactly-one constraints directly. This is a consequence
of the minimum-row choice and the Latin property, not an assumption about
the desired models. The original, larger case splits and certificates remain
reproducible with the default options.

The runner now also supports two further symmetry reductions, which preserve
a representative of every model:

- `--min-commuting`: since `R_x=L_x^-2`, we have `x*y=y*x` exactly when
  `L_x^3(y)=y`. Thus the number of commuting partners of x equals the number
  of fixed points of `L_x` plus three times its number of three-cycles.
  Among non-idempotent elements with the minimum fixed-point count, choose
  0 with the minimum commuting-partner count. A different non-idempotent row
  must either have more fixed points, or at least as many commuting partners.
  In the all-idempotent branch every row has one fixed point, so simply choose
  a row with minimum commuting-partner count.
- `--lex-rows 2`: after fixing the first row, relabelings may rotate its other
  cycles and interchange cycles of equal length. These permutations fix 0 and
  commute with its left translation. Choose a representative with the least
  first-two-row prefix in this finite relabeling orbit, then require that its
  prefix be lexicographically no greater than the prefix under each generator.
  Every orbit has such a minimum. These comparisons preserve both the fixed
  first row and the earlier choice of 0.

The CNF encodes commuting partners by equality of opposite table entries and
encodes lexicographic comparisons directly with one-hot table variables.
Controls at orders 7, 9, and 11 recover independently checked E63 models with
both reductions enabled. A stronger optional comparison includes every
nonidentity power of each cycle rotation and every swap of equal-length
cycles. The same orbit-minimum argument applies. All such permutations for
the 55 reduced order-18 cases were checked to fix 0 and commute with the
prescribed first row; the strengthened encoding also recovered and directly
verified a known-positive model of order 11. Each saved case records which reductions it used;
the proof checker regenerates exactly that input. Refutations obtained with
fewer reductions remain valid for the corresponding strengthened case.

There is also a deduction from the already refuted idempotent branches. All
18 idempotent first-row types containing a 3-cycle or a 4-cycle were refuted
without the global commuting-count choice. Because any element of an
idempotent model could have been relabeled as 0, these refutations forbid
3-cycles and 4-cycles in *every* left translation of an idempotent order-18
model. Consequently distinct elements cannot commute, and no right translation
can have a 2-cycle (`R_x=L_x^-2`). These two additional constraints are supplied
to a separate pass on the remaining seven idempotent types. They are derived
order-18 facts, not general E229 identities. The input metadata records their
use, and the checker requires the 18 dependency cases to be present without
the derived constraints or the global commuting-count choice, preventing a
circular exclusion argument.

Two further optional encodings are being tried on the remaining order-18
branches. First, every right translation is an even permutation, since
`R_x=L_x^-2`. A circuit for inversion parity makes this consequence explicit.
The circuit was checked against every permutation through order 5, and the
combined encoding recovered directly verified E63 models at orders 4, 7 and 11.

Second, reserve the idempotent `1,17` branch for models in which *every* row
has that cycle type. A model with any other row type is covered by that other
idempotent branch, so the joint case split remains exhaustive. For prime
`n-1`, requiring `L_x^(n-1)(x+1)=x+1` forces the entire complement of x to be
one cycle: its orbit length divides `n-1`, and Latin cancellation with
idempotence rules out a fixed point other than x. This stronger final branch
is tagged `idempotent_single_cycle`. The checker requires all other row types
in the split and rejects competing nonvacuous global commuting-count choices.
A positive control at order 8 recovered a table with a fixed point and a
7-cycle in every row, checked directly after solving. These reductions do not
by themselves settle order 18.

### Applying the completed cases to every minimum row

The resumed order-18 search reached 52 solver refutations and three unresolved
cases, all non-idempotent. The one-fixed-point branch was refuted in 388.872
seconds by the new filter; its trace has now passed independent DRAT checking. The previous run stopped at its proof-storage
reserve; deleting only unfinished traces recovered about 20 GB. Completed
traces were preserved. The initial resumed pass uses a 1 GiB trace cap per solver. Later full-prefix
passes use a monitored 2 GiB soft limit and retain the shared-memory reserve.

All 26 completed non-idempotent cases were refuted without the global
minimum-commuting-count choice. Their proofs have now been independently
checked. Consequently, within a model, these exclusions apply to **every**
non-idempotent row attaining the minimum fixed-point count, since any such
row could be relabeled as 0.

If the minimum is zero, each zero-fixed-point row must have one of the types
`3,3,3,3,3,3`, `3,3,4,4,4`, or `3,5,5,5`. Their commuting-partner counts are
respectively 18, 6, and 3. The secondary minimum-commuting choice further
restricts which of these types can occur in each branch. If the minimum is
one, the total-fixed-point argument makes every row have exactly one fixed
point. Every non-idempotent row must then have type `1,3,3,3,4,4`, with exactly
10 commuting partners. Idempotent rows are exempt from this latter filter.

There is a compact encoding of the permitted cycle lengths. For a given row
x and point y, put `z=R_x(y)`. Since `R_x=L_x^-2`, the statements

- `L_x(y)=z`,
- `R_x(z)=y`,
- `R_x(z)=L_x(y)`

mean respectively that the cycle length divides 3, 4, or 5. Taking the
appropriate disjunction, together with the permitted commuting counts,
restricts every minimum row. The already established absence of 2-cycles
removes that divisor of 4. The implementation is tagged
`nonidempotent_cycle_filter`; the checker requires all relevant excluded
row types as independent dependencies and forbids circular use of this filter
or a global commuting-count choice in those dependencies.

The three permutation identities were checked exhaustively on permutations
through order 7. The resumed searches also compare four-row prefixes under
all individual cycle rotations and equal-cycle swaps; positive controls at
orders 7 and 11 passed direct validation. These reductions still leave order
18 open until the remaining cases are settled.

Two further universal consequences are encoded in separate profiles.
Nonfixed commuting partners of x are exactly the points in 3-cycles of `L_x`,
so their count is divisible by three. A three-state residue circuit enforces
this; it was checked on every assignment through eight literals (including
negated literals), and full model controls passed at orders 4, 7 and 11.

Also, a finite E229 loop has odd order. With identity e, E229 gives
`(x*x)*x=e`; applying E229 at the pair x,x and cancelling the right translation
also gives `x*(x*x)=e`. Put `z=x*x`. Comparing `z*x=e` with
`z*(z*z)=e` gives `z*z=x`. The only fixed point of squaring is e, since
`x*x=x=x*e` implies x=e. Thus all other elements occur in pairs. A row fixing
every point is automatically a two-sided identity because `R_x=L_x^-2`, so
no such row can occur at even order. This is recorded as `no_even_identity`;
positive controls at orders 4 and 8 passed. The hardest six-3-cycle case is
also being tried with all 17 nonzero rows in the symmetry-comparison prefix.

A further propagation profile records `commuting_triangles`. Write C(x,y)
for x*y=y*x. The commuting partners of x form `Fix(L_x^3)`, which is invariant
under both `L_x` and `R_x=L_x^-2`. Thus, if z=x*y, then
`C(x,y)=C(x,z)=C(y,z)`. The encoding states these equivalences directly for
every multiplication entry. It also records that a row has either zero or at
least four noncommuting partners: these are the points in cycles of lengths
other than one or three, and two-cycles are already excluded. Positive
controls at orders 3, 4, 7, 11 and 12 passed independent table evaluation.
These are universal consequences, with no additional case dependencies.

Separate bounded searches test row types without assuming that the chosen
row minimizes the fixed-point count. An initial pass over all 45
non-idempotent types with at least two fixed points refuted 31, with all 31
traces independently checked. The other 14 timed out. Their inputs were
regenerated sequentially and their hashes checked after detecting a shared
variable-pool concurrency error in the initial input-generation batch; the
missing attempt was rerun. These auxiliary exclusions are not counted as
additional closures of the main 55-case partition.

### A uniform square consequence for the remaining 3,5,5,5 type

Splitting the canonical `3,5,5,5` input on `1*1` refuted every value except
zero. All 17 refutations have passed independent DRAT checking, with every
input regenerated. The certificate is
[63_order18_square_involution.json](../data/spectrum/63_order18_square_involution.json).
Its parent input uses the checked zero-row cycle filter and the universal
consequences above. Its minimum-commuting bound is three, a vacuous bound
for a non-idempotent row; its minimum-fixed-point bound is zero. Thus **any**
zero-fixed-point row of this type can be selected as 0. Relabeling then makes
its square 1, so the exclusion says `(x*x)*(x*x)=x` for every such row.

The new flag `zero_three_square_involution` applies this consequence to every
zero-fixed-point row with exactly three commuting partners, which is precisely
the remaining `3,5,5,5` type. The verifier checks the separate 17-branch
certificate as well as the earlier zero-row exclusions; the dependency parent
cannot use this new flag. This strengthens the remaining search but does not
yet exclude order 18.

### Restricting every non-idempotent row with at least two fixed points

The auxiliary search also rules out all 33 such row types containing a cycle
whose length is outside `{1,3,4}`. All 33 traces have passed independent DRAT
checking, and the complete excluded-type list and every input have been
regenerated. The certificate and verification record are
[63_order18_positive_rows.json](../data/spectrum/63_order18_positive_rows.json)
and [its proofcheck](../data/spectrum/63_order18_positive_rows_proofcheck.json).
Unlike the original minimum-row cases, these inputs make no minimum-fixed
or minimum-commuting choice. The exclusions therefore apply to every
non-idempotent row with at least two fixed points.

Thirty-one types were excluded directly. The remaining two, with cycles
`3,1,1,1,1,1,3,7` and `3,1,1,3,3,7`, use the earlier zero-row cycle filter;
their dependency inputs do not use this new consequence or the square
consequence above. The last seven-cycle search took 373 seconds and its
independent proof check took 623 seconds.

The flag `positive_fixed_short_cycles` encodes the result by exempting
idempotent rows and rows with at most one fixed point, then requiring
`L_x(y)=R_x(y)` or `R_x^2(y)=y` at every point of each remaining row.
These alternatives say that the cycle divides three or four. The known
order-12 model passes a control check of the encoding. This further reduces
the three open main cases; it does not settle any of them by itself.

The same result now covers **exactly one fixed point** as well. The twelve
excluded types were refuted using the checked zero-row, square, and
at-least-two-fixed-point consequences. Every trace passed independent DRAT
checking, with the inputs regenerated and the twelve-type list audited; see
[63_order18_one_fixed_rows.json](../data/spectrum/63_order18_one_fixed_rows.json)
and [its proofcheck](../data/spectrum/63_order18_one_fixed_rows_proofcheck.json).
The only remaining one-fixed-point non-idempotent type is `3,1,3,3,4,4`.

The extension `one_fixed_short_cycles` therefore restricts every
non-idempotent row with a fixed point to cycle lengths one, three and four.
It additionally records that its number of noncommuting partners is divisible
by four: these are exactly the points in its four-cycles. The guarded residue
circuit passed all Boolean assignments through eight inputs, and the full
extended filter accepts the independently checked order-12 control. The
verifier checks all three layers of auxiliary dependencies before accepting
a new main-case proof using this extension.

**New main-case closure:** this strengthened search refuted the full
`nonidem-3-5-5-5` case in 1010.303 seconds. Its independent trace check
passed in 1797.508 seconds. This leaves the two types listed at the start of this section;
order 18 remains open.

In each of those remaining minimum-commuting branches, zero-fixed-point
non-idempotent rows already have only three- and four-cycles. Combining that
fact with the positive-fixed-point exclusions gives the same cycle restriction
for **every non-idempotent row**, without first deciding whether it has a fixed
point. The propagation variant `all_nonidempotent_short_cycles` implements
this and the corresponding divisibility by four of its noncommuting count.
It requires the earlier filters and the appropriate minimum-commuting branch;
it makes no use of the new `3,5,5,5` refutation.

A further propagation option, `short_cycle_steps`, records
`L_x²(y)=R_x(y)` whenever a non-idempotent row x has only short cycles and
x and y do not commute. Such a point must lie in a four-cycle, on which
`L_x²=L_x^-2`. The generator requires the preceding non-idempotent short-cycle
filter before enabling this option, and the proof checker regenerates it.
The identity passed permutation controls through order 8 and a directly
verified 20-element control built from a transversal design of five groups
of order 4. That control has non-idempotent rows with genuine four-cycles,
so the new clauses are tested beyond the commuting case.

### Removing the remaining idempotent-row exceptions in A/B

A separate complete list of 103 idempotent-root row types containing a cycle
outside `{1,3,4}` has now been refuted and independently checked. The root
has a prescribed one-cycle; no global idempotence assumption is made. Some
inputs use the already checked short-cycle restriction on non-idempotent
rows, and the final cases also require a zero-fixed row. Both properties
already hold in A/B and survive relabeling the chosen idempotent element.
Thus these are conditional exclusions for the two remaining branches.

The certificate is [63_order18_idempotent_rows.json](../data/spectrum/63_order18_idempotent_rows.json),
with [independent checks](../data/spectrum/63_order18_idempotent_rows_proofcheck.json).
The verifier regenerates the complete 103-type list and every input, audits
the conditional scope, and checks the traces or their matching cached hashes.
The new `all_row_short_cycles` flag therefore applies the cycle and
noncommuting-degree restrictions to **every** row in A/B. It is not used
as a new assumption in any of its own auxiliary dependency inputs.

There is a useful parity consequence. In a model where all rows have only
1/3/4 cycles, any noncommuting pair lies in a unique five-point block with the
following off-diagonal table (the diagonal entries are unspecified):

| * | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| 0 | * | 2 | 3 | 4 | 1 |
| 1 | 3 | * | 4 | 2 | 0 |
| 2 | 4 | 0 | * | 1 | 3 |
| 3 | 1 | 4 | 0 | * | 2 |
| 4 | 2 | 3 | 1 | 0 | * |

To derive this, start with a noncommuting pair 0,1 and label its `L_0`
four-cycle `1 -> 2 -> 3 -> 4 -> 1`. These points differ from 0, since
0's own cycle has length one or three. The commuting-triangle property
makes every pair among these five points noncommuting. Applying
`L_x²(y)=R_x(y)` successively gives the displayed table: for example,
`1*0=3`, `0*1=2` imply `1*3=2`; `3*0=1`, `0*3=4` imply `3*1=4`;
then `1*3=2`, `3*1=4` imply `1*2=4`. The other entries follow in the same
way, with the four-cycle condition supplying their final entries.
Every pair in this block recovers the same block from its four-cycle,
so two distinct blocks intersect in at most one point.

Each block contributes four noncommuting occurrences of each of its five
values. All remaining off-diagonal occurrences are commuting and come in
opposite pairs. Since each value occurs exactly n times in a Latin table,
its diagonal multiplicity has the same parity as n. In particular it is even
at order 18. The `diagonal_fiber_parity` option encodes these even counts;
it requires the certified all-row short-cycle restriction. Its XOR circuit
was checked on all Boolean inputs through length 8 (also with negated inputs),
and the full constraint accepts independently verified models of orders
12 and 20, including the noncommutative 20-point control.

## 6. Bounded searches for positive certificates

The model-search runner is
[spectrum_63_atp.py](../scripts/spectrum_63_atp.py); the recorded attempts are in
[63_atp_search.json](../data/spectrum/63_atp_search.json). These searches target
the then-20 undecided orders, starting at 14 and proceeding in increasing order.
The runner also maintains product closure: a witness at 14 would remove 42 from
the search list, one at 22 would remove 110, and one at 38 would remove 114.
Only one direct witness per newly needed order is retained in the witness list.

The unrestricted first pass uses both Vampire 5.1.0 and Mace4 2017-11A, with both
E63 itself and the E229 presentation from Section 5. Each attempt has a 512 MB
memory cap and a time limit of 10 seconds up to order 47, or 5 seconds above it.
A separate wall-time limit also bounds elapsed time, including when a CPU-time
limit takes longer to reach on a busy machine.
Vampire receives explicit domain-closure and distinctness axioms; Mace4 receives
equal start and end sizes. A returned table must have exactly the requested
order, be Latin, and satisfy every instance of its search equation. E229 tables
are then converted by left division and checked again against the original E63.

Additional short passes use explicit cancellation axioms, fixed affine
submodels of orders 3 and 5, and, at the two odd candidate orders 29 and 47,
idempotent or constant-diagonal restrictions. These are positive-model search
heuristics; exhausting a restricted search would not settle the unrestricted
spectrum. The report records the restriction and resource limits for each pass.

**Outcome:** the 176 recorded attempts produced no new model: 140 reached their
time limit and 36 reached their memory limit. At that point the 20 undecided orders and
the cutoff 159 were unchanged. No nonexistence result follows from these runs,
and there is no new positive table to formalize. Two additional short Vampire
attempts at order 14 without named domain constants also timed out.

The solver/parser checks recover the known models of orders 3 and 5 in both
presentations using both solvers, and orders 7 and 8 using Mace4. An unassisted
3-second control search at known-positive order 11 times out, illustrating how
little a short unsuccessful search says about existence. The checker also
rejects a Latin table of order 2 that fails E63.

To repeat the unrestricted pass with locally installed executables:

```sh
python3 scripts/spectrum_63_atp.py \
  --vampire /path/to/vampire --mace4 /path/to/mace4 \
  --workdir /tmp/e63-models --output /tmp/e63-models.json
```

### More intensive search

The follow-up runner [spectrum_63_campaign.py](../scripts/spectrum_63_campaign.py)
adds a resumable portfolio with a 4096 MB cap per solver, three-minute general
searches, and one-minute searches with selected first-row cycle types. Orders
are still processed in increasing order, with product closure updated before
each new order. The checkpoint is
[63_atp_aggressive_search.json](../data/spectrum/63_atp_aggressive_search.json).
It records unfinished versus completed orders separately; failed individual
profiles are not spectrum exclusions.

**Outcome (2026-09-24):** after 82 minutes, the intensive pass completed 715
direct Vampire/Mace4 attempts across all 20 missing orders, with individual
limits up to 15 minutes and 4096 MB. There were 638 solver time limits, 40
external wall-time limits, seven memory limits, and 30 exhausted restricted
cases. None produced a model. At that point the 20 undecided orders and cutoff 159 were
unchanged, with no new positive certificate to formalize. Every input
hash and raw-log path was audited; 13 retained positive control tables also
passed the repository's independent equation evaluator.

The added translation hints say that each left translation has no two-cycle
and that the cycle containing its own left factor has length dividing three.
Section 5 proves these for E229. Left division inverts left translations, so
the same hints apply to E63. Fixing a canonical first row preserves every model
with that cycle type, but the portfolio samples only some types at larger
orders. This change recovers the known order-11 model in under a tenth of a
second when the first row has cycle lengths `1,5,5`.

Before the ascending portfolio, order 14 received six five-minute unrestricted
attempts and a complete list of its 71 canonical first-row types, with 30 seconds
per type in Mace4. No model was found: 49 cycle cases timed out and 22 restricted
cases exhausted their search. That bounded pass did not settle order 14.

Idempotent searches at orders 29 and 47 received 15-minute limits. At order 29,
a further complete list of 230 canonical first-row types compatible with
idempotence received 30 seconds per type; all 230 timed out. Under concurrent
machine load, some attempts reached the external wall-time cap before their
solver CPU-time quota. These outcomes are recorded separately in the report.

Another propagation variant supplies all three translation identities at once.
E229 gives `R_y L_y² = id`; finiteness makes `L_y` bijective and hence
`R_y = L_y⁻²`. It follows that `L_y² R_y = id` (E73) and
`L_y R_y L_y = id` (E125). Thus these extra constraints preserve every finite
E229 model. The `--all-translations --laws 229` options enable this variant;
any returned table is still converted and checked directly against E63.

A separate constructive search targeted order 158 via a pairwise balanced
design on `{0,1} × Z/79Z`, with blocks of sizes 5, 7, and 8. Each base block
is developed by simultaneous translation in the second coordinate. A complete
certificate would cover each of the 39 nonzero differences up to sign within
each orbit once, and all 79 directed differences between the two orbits once.
Putting the known idempotent E63 operations on the blocks would then give a
158-element model by Section 1.

Three distributions of seven or eleven base blocks were tried with Mace4 and
CP-SAT, supplemented by local search and exact partial-table repairs. No complete
design certificate was obtained. Incomplete difference packings were checked
separately and never accepted as magma witnesses. These construction searches
also supply no exclusion at order 158.

## Later formalization: minimize explicit model tables

Use product closure instead of separate order-9 and order-12 tables: `9=3*3`
and `12=3*4`. More generally, retain only construction seeds that are needed by
the finite certificate and the induction. If a seed requires an idempotent
operation or a distinguished idempotent, its replacement must preserve that
property as well as the cardinality. For example, the idempotent order-8 seed
cannot be replaced using a product of smaller available orders. This cleanup
is deferred until the construction is formalized.

## Relation to the existing literature

These are the T2-quasigroups of A. V. Scerbacova and V. A. Shcherbacov,
[*About spectrum of T2-quasigroups*](https://arxiv.org/abs/1509.00796).
Their affine polynomial agrees with P above, and their Theorem 5.4 proves
eventual idempotent existence using Wilson's theorem. The explicit cutoff and
finite reduction here instead use the stronger group-filling rule of Section 1.

The same finite spectrum transfers to E73, E118, E125, E1692 and the appropriate
dual laws through the equivalences already recorded in
[Transfer.lean](../equational_theories/Spectrum/Transfer.lean).

### A further reduction to commutative order-18 models (not Lean)

The 53 checked main exclusions and the 103 checked conditional idempotent-row
exclusions imply that every possible order-18 model has only cycles of lengths
1, 3 and 4 in its left translations. The two unresolved main cases are still
`3^6` and `3^2 4^3`. The following separate argument substantially narrows them.
Its combinatorial steps are mathematical arguments, not Lean theorems.

Every row has a three-cycle. This is automatic for a non-idempotent row.
Suppose instead that e is idempotent and its row has only fixed points and
four-cycles. Its commuting partners are precisely F = Fix(L_e). If x is in F
and x differs from e, then x is not idempotent, by cancellation in `xe=xx`.
Put s=xx. E229 applied to (x,e) gives `sx=e`; x and its square commute, so
`xs=e`. The commuting-triangle property gives `se=es`, hence s is in F.
Applying E229 to (s,e), and using `se=s`, gives `(ss)s=e=xs`; right
cancellation gives `ss=x`. Squaring therefore restricts to an involution on F
whose only fixed point is e. Thus |F| is odd. But 18=|F|+4b makes it even,
a contradiction.

The noncommuting pairs decompose into the five-point blocks described above;
each four-cycle in row x belongs to one block containing x. Write b_x for the
number of those blocks, a_x for the number of three-cycles, and f_x for the
fixed-point count. Then

```
f_x + 3 a_x + 4 b_x = 18,     a_x >= 1,     b_x <= 3,
sum_x f_x = 18,              sum_x b_x = 5 B,
```

where B is the total number of blocks. Summing the first equality modulo 3
shows that B is a multiple of 3. The incidence bound gives B <= 10, so
B is 0, 3, 6 or 9. Let n_i count points in exactly i blocks. Since two blocks
meet in at most one point,

```
n_2 + 3 n_3 <= B(B-1)/2.
```

Also `f_x >= 2` when b_x=1 and `f_x >= 1` when b_x=2, because
`f_x = -b_x (mod 3)`. For B=3, the incidence equations give
`2 n_1 + n_2 = 30 - 3 n_2 - 6 n_3 >= 21`, contradicting
`sum f_x=18`. Thus B=0, 6 or 9.

For B=6, the incidence equations and fixed-point bound give
`n_0+n_3 <= 3` and `n_0 >= 2`. There are exactly three incidence types:

* `(n_0,n_1,n_2,n_3)=(3,0,15,0)`: all pairs of the six blocks intersect
  at distinct points, with three points in no block. The minimum fixed counts
  sum to 15; precisely one row has three additional fixed points. Up to
  symmetry, that row is either a point in no block or a pair-intersection.
* `(2,2,14,0)`: one pair of blocks is disjoint, and each of those two blocks
  has one private point. All other pairs intersect, with distinct
  intersections; there are two points in no block. All fixed counts are
  minimal.
* `(2,3,12,1)`: three blocks have a common point, each has a private point,
  and all remaining pairs intersect at distinct points. There are two points
  in no block. Again all fixed counts are minimal.

For B=9, the equations give `n_0=n_1=0` and `n_2=n_3=9`, with every pair
of blocks intersecting. In the dual description, nine triples and nine pairs
partition the edges of K9. Each dual vertex belongs to three triples and two
pairs, so the pairs form a 2-regular graph. Its cycle type is one of
`3+3+3`, `3+6`, `4+5`, or `9`. Exhaustive triangle-exact-cover enumeration of
the complement gives respectively 12, 6, 0 and 2 labeled decompositions.
Under the automorphism group of the pair graph these give respectively
1, 1, 0 and 1 types. This enumeration is a small finite computation; it is
separate from the SAT searches. Thus there are three nine-block types.

There is no need to enumerate the orientations of the five-point operations
on these blocks. On each block, replace the off-diagonal multiplication by
the displayed canonical five-point table, independently of the other blocks.
Every block row and column still permutes the other four points. Distinct
blocks intersect in at most one point, so Latinness is preserved. All
commuting entries and all diagonal entries are unchanged. For a noncommuting
input pair, E229 is evaluated entirely at off-diagonal entries within its
block, where the canonical table satisfies it. For a commuting input pair,
the commuting-triangle property ensures that all entries consulted commute,
so the original evaluation is unchanged. Thus this normalization preserves
existence, commutation, the diagonal, and all row fixed-point counts. It need
not preserve the isomorphism class of the original operation.

The four six-block cases and three nine-block cases were all refuted in under
two seconds each. All seven CNFs were regenerated and all seven DRAT traces
independently checked. Their inputs additionally include the previously
justified short-cycle and even-diagonal-fiber constraints. A nontrivial
positive control normalized the blocks of the known noncommutative order-20
model and directly rechecked E229 and every unchanged commuting entry.

**The commutative case is still open.** Its rows have only fixed points and
three-cycles, so every row fixed-point count is a multiple of three, and their
sum is 18. In particular there is a zero-fixed-point row, which may be
canonically labeled with cycle type `3^6`. No timeout in these searches is
being treated as a nonexistence result. The new seven-case refutation does
not itself settle the order-18 spectrum question.

The seven block-system traces are preserved in
[63_order18_block_certificates.tar.gz](../data/spectrum/63_order18_block_certificates.tar.gz),
with [the manifest](../data/spectrum/63_order18_block_systems.json) and
[the independent check report](../data/spectrum/63_order18_block_systems_proofcheck.json).
The portable script recomputes the nine-block exact covers, regenerates all
eight canonical CNFs, checks their hashes, and checks each available proof:

```sh
mkdir -p /tmp/e63-block-proofs
tar -xzf data/spectrum/63_order18_block_certificates.tar.gz -C /tmp/e63-block-proofs
python3 scripts/spectrum_63_block_systems.py \
  --output /tmp/e63-block-check \
  --verify data/spectrum/63_order18_block_systems.json \
  --artifact-dir /tmp/e63-block-proofs \
  --checker /path/to/drat-trim
```

This checker passed with all seven noncommutative cases verified and the
commutative case marked `GENERATED`, not refuted. Its mathematical premises
remain the earlier 53 main and 103 auxiliary exclusions described above.

### Fixed-point fibers in the remaining commutative case

Write u(x) for the unique e with `ex=x`, and write s(x)=xx. Commutativity
makes `xe=x` too. In the commutative E229 presentation, `L_x^3=id`, so
`x(xx)=u(x)`. In particular, for x in `F_e = Fix(L_e)`, `x s(x)=e`.
If x,y are in F_e and have the same square z, then `zx=e=zy`; Latin
cancellation gives x=y. Thus **squaring is injective on every fixed-point
fiber F_e**. Equivalently, elements with the same square have distinct local
units u(x).

At order 18, each f_e=|F_e| is a multiple of three, since all row cycles have
length one or three. Their sum is 18, so u has at most six distinct values.
Every nonempty diagonal fiber has even cardinality, by symmetry of the Latin
table; hence squaring has at most nine distinct values. Injectivity on F_e
therefore gives f_e <= 9. This provides a mathematical explanation for the
separately checked exclusions of maximum fixed counts 12 and 15.

There are two useful sharper consequences:

* If a row has nine fixed points, its squares exhaust all nine possible
  diagonal values. Every nonempty diagonal fiber then has size exactly two.
* If a diagonal fiber has six elements, their local units are all distinct.
  There are exactly six nonempty F_e, and each has size three.

The strengthened searches encode these consequences. They have not yet
resolved the commutative case. A broader split records the function u up to
relabeling. Its image has size m <= 6, and its positive fiber sizes are
`3 w_1,...,3 w_m` with positive weights summing to six. Enumerate the weighted
functional graph of u restricted to its image; all other points are leaves
whose counts at each image vertex are determined by the weights. Canonical
rooted-tree and directed-cycle codes give 468 types. A two-cycle is impossible:
`u(x)=y` and `u(y)=x` would give `xy=x=y`. Removing those types, and maximum
fixed counts greater than nine, leaves 270 types for computational searches.
These are subcases of the one remaining commutative branch, not additional
open orders. Scout timeouts leave their corresponding types unresolved.

No closure property of F_e or of the image of u is assumed. In particular,
explicit commutative order-12 countermodels show that the image of u need not
be closed under multiplication, and that a diagonal fiber can meet a
three-cycle of its own value's translation in exactly two points. Neither
proposed property was added to any exclusion search.

The recent counterexamples are retained in
[63_commutative_structure_counterexamples.json](../data/spectrum/63_commutative_structure_counterexamples.json),
with their E229 tables and explicit witnesses. The same order-12 example also
refutes closure of an idempotent value's diagonal fiber. An order-7 affine
example refutes the proposed identity `u^4=u`. These counterexamples are
research safeguards, not extra assumptions in the order-18 searches.
A further retained order-12 example shows that even when e is idempotent,
`Fix(L_e)` need not be closed under squaring: with e=1 and x=8, one has
`ee=e`, `ex=x`, `xx=9`, but `e9=11`.

The local-unit enumeration is now independently audited by explicitly applying
all permutations of the at-most-six image points and comparing their orbits
with every labeled weighted function. This checks coverage and absence of
isomorphic duplicate representatives without relying on the rooted-tree
canonicalization used to produce the cases.

The first batch supplied 52 independently checked proofs: 48 for two-cycle
cases that also have the elementary contradiction above, and four additional
cases. The latter exclude both remaining two-point images of u and two
three-point-image cases. The other cases remain open unless separately
excluded; time-limited searches supply no negative conclusion.

The [unit-map manifest](../data/spectrum/63_order18_commutative_units.json),
[proofcheck](../data/spectrum/63_order18_commutative_units_proofcheck.json), and
[compressed traces](../data/spectrum/63_order18_unit_certificates.tar.gz) are
retained. Reproduce the enumeration and the 52 available checks with:

```sh
mkdir -p /tmp/e63-unit-proofs
tar -xzf data/spectrum/63_order18_unit_certificates.tar.gz -C /tmp/e63-unit-proofs
python3 scripts/spectrum_63_commutative_units.py \
  --output /tmp/e63-unit-check \
  --verify data/spectrum/63_order18_commutative_units_proofcheck.json \
  --artifact-dir /tmp/e63-unit-proofs \
  --checker /path/to/drat-trim
```

The complete first scout pass ended with 266 configurations unresolved, 52
refuted with checked traces, and 150 further configurations excluded
analytically. This still leaves the commutative order-18 existence question
open. The separate complete split on the first non-root diagonal entry has
three unresolved cases (values 0, 1 and 3 in the canonical `3^6` first row);
the other fifteen values have checked exclusions. Longer searches use the
commutative reduction and the square/unit counting bounds in those three cases.

The next local-unit pass also uses the following explicit consequences, with
the local-unit function pinned in each case:

* `xx=z` if and only if `xz=u(x)`, because `L_x` is bijective and
  `L_x^3=id`.
* If `x != u(x)`, then `xx != u(u(x))`. Indeed, setting `e=u(x)` and
  `z=u(e)`, the alleged equality would give `zx=e=ze`, hence `x=e` by
  Latin cancellation.
* A square fiber has at most m elements when u has image size m, by the
  injectivity statement above. At even order its size is even, so the bound
  may be rounded down to the nearest even integer.
* If a local-unit fiber has size n/2 at even order n, its squares exhaust
  the n/2 diagonal values, each occurring exactly twice. Every square then
  occurs once inside that fiber and once outside it. In particular,
  squaring is also injective on its complement.

These are consequences of the stated identities, not conjectural closure
assumptions. The portable local-unit checker recognizes the manifest flag
`square_unit_strengthening` and regenerates these additional clauses.
Its encoding has also passed a pinned commutative order-12 positive control.

An initial snapshot of this stronger pass contains 25 further independently
checked exclusions, bringing the local-unit split to 77 checked cases, 150
other analytically excluded cases, and 241 still unresolved cases. The
stronger proofs are in
[this additional archive](../data/spectrum/63_order18_strong_unit_certificates.tar.gz),
with [a proofcheck manifest](../data/spectrum/63_order18_strong_units_proofcheck.json).
They can be regenerated and checked by the same portable script:

```sh
mkdir -p /tmp/e63-strong-unit-proofs
tar -xzf data/spectrum/63_order18_strong_unit_certificates.tar.gz -C /tmp/e63-strong-unit-proofs
python3 scripts/spectrum_63_commutative_units.py \
  --output /tmp/e63-strong-unit-check \
  --verify data/spectrum/63_order18_strong_units_proofcheck.json \
  --artifact-dir /tmp/e63-strong-unit-proofs \
  --checker /path/to/drat-trim
```

These are partial exclusions within the final commutative branch. They do not
yet supply a proof that order 18 is absent from the spectrum.

Two longer follow-ups produced additional UNSAT traces for `units-3-45` and
`units-3-44`, both now independently checked. The current total is therefore
79 checked local-unit types, 150 other analytically excluded types, and
239 unresolved types. Their
[separate manifest](../data/spectrum/63_order18_strong_units_deep_proofcheck.json)
records the verification status and the hashes of regenerated inputs and
proofs. These larger traces are retained on local disk, outside the repository
archive. To regenerate their inputs, use:

```sh
python3 scripts/spectrum_63_commutative_units.py \
  --output /tmp/e63-deep-unit-inputs \
  --generate units-3-45 --generate units-3-44 --strengthen-square-units
```

The manifest records the solver commands, with paths to adjust for the new
input directory. The portable verifier also accepts this manifest using its
`--verify`, `--artifact-dir`, and `--checker` options; the completed first check
took approximately eleven minutes.

## Bennett's constructions and twelve recovered model certificates

F. E. Bennett, *Quasigroup Identities and Mendelsohn Designs*, Canadian Journal
of Mathematics 41 (1989), 341–368,
[doi:10.4153/CJM-1989-017-0](https://doi.org/10.4153/CJM-1989-017-0),
Theorem 5.50, constructs every positive order except 2 and 6 and the possible
exceptions `{10,14,18,26,30,38,42,158}`. In particular, the paper explicitly
leaves order 18 unsettled. It supplies substantially sharper small-order
constructions than the separate 2015 paper on T2-quasigroups discussed earlier.

Bennett writes the identity as `(yx · y)y=x`, or `R_y^2 L_y=id`.
Taking the opposite quasigroup gives `L_y^2 R_y=id`; bijectivity then gives
`R_y L_y^2=id`, which is E229. Taking rowwise left division converts E229
to E63. Thus the spectrum assertion applies to E63. Our explicit models below
are constructed directly in the E229 presentation, then converted and checked
against every E63 instance as well as Latinness.

The [compact construction manifest](../data/spectrum/63_bennett_constructions.json)
records twelve additional model orders, their recipes, idempotents, and hashes
of their complete E63 tables. The
[standalone generator and verifier](../scripts/spectrum_63_bennett.py)
uses only the Python standard library. It reconstructs the tables rather than
requiring large stored multiplication tables:

```sh
python3 scripts/spectrum_63_bennett.py
# Optional: export the complete E63 tables.
python3 scripts/spectrum_63_bennett.py --tables /tmp/e63-bennett-tables.json
```

The construction ingredients are:

* Singular products give 22, 29, 34, 58 and 106; a direct product gives 110.
* A checked `{5,7,8}`-GDD of type `1^42 4^1`, filled with the four-point
  model, gives 46. Its [certificate](../data/spectrum/63_bennett_gdd46.json)
  contains a small partial difference matrix over the integers modulo seven.
  Seven translates of each of its three complete rows give seven-point blocks
  through three distinguished points. Its six rows with one missing coordinate
  give five-point blocks. Six eight-point blocks join the fourth distinguished
  point to the six seven-point coordinate groups. The verifier independently
  checks every required pair of the resulting design exactly once.
* Deleting three points of a single block in TD(8,8), then adding a common
  point and filling groups with models of orders 8 and 9, gives 62.
* A truncated TD(8,9), with seven order-12 fillings sharing a three-point hole
  and an order-11 final filling, gives 74.
* Deleting a point of TD(5,23), and treating its incident blocks as groups,
  gives the design used for 114. The analogous deletion in TD(5,8), followed
  by a threefold inflation and fillings of orders 13 and 22, gives 118.
* A checked 4-GDD of type `2^9 5^1`, doubled using Bennett's incomplete
  eight-point C3 table of type `2^4`, then filled with idempotent models of
  orders 5 and 11 sharing one point, gives 47. The
  [23-point design](../data/spectrum/63_bennett_gdd23.json) has 39 blocks;
  the verifier checks every required pair is covered exactly once. Its
  discovery used a solver, but replaying the certificate does not.

Here is the singular product used by our generator. Let V be an idempotent
E229 quasigroup, Q an E229 quasigroup containing a subquasigroup P of size p,
and B any E229 quasigroup on the q-p remaining labels. On
`P ∪ ((Q\P) × V)`, put a copy of Q on each fiber together with P. Between
different V-fibers, multiply the first coordinates in B and the fiber indices
in V. This gives order `v(q-p)+p`. For inputs in one fiber the identity is
checked in Q. For distinct fiber indices, idempotence and Latin cancellation
ensure that all three multiplications in E229 use distinct fiber indices,
so the identity is checked coordinatewise in B and V. Row and column
bijectivity follow from those of Q, B and V.

The shared-hole construction used for 74 permits the last filling to change
the multiplication within P. To see why this is valid for E229, every
multiplication in `(y(yx))y` involves y. If y is outside P, no such multiplication
uses two elements of P. If y is in P and x is outside, its left translation
preserves the complement of the subquasigroup P, so again no multiplication
uses two elements of P. Hence changing the table on P affects only identities
whose two inputs lie in P; the last filling handles those identities.

Bennett's Lemma 5.46 also covers 90. That published construction
is not currently claimed as a locally replayed multiplication-table certificate.
It remains separate from the twelve explicitly reconstructed models and from
the six unsettled orders above. The website's Lean-proved spectrum has not been
changed by this research update.

The missing local ingredient for 90 is an order-16 E229 quasigroup containing
an order-5 subquasigroup. The paper uses seven such fillings and a final
order-13 filling on a truncated TD(8,11), sharing five points. Our straightforward
implementation of the cited `5*(4-1)+1` singular product gives a valid order-16
model with constant diagonal, but inspecting all 4368 five-element subsets
finds no closed one in that particular table. Additional searches for a
suitable order-16 filling were inconclusive. This rejects only that candidate
filling; it does not establish nonexistence at either 16 or 90.

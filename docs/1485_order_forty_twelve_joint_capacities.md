# Order forty, twelve/eight: joint profile capacities

Research note, 20 September 2026. This is a **checked finite exclusion**
of the six normalized non-`3333/3333` cases below. The reduction is
analytic and every finite refutation has passed independent LRAT checking.
The `3333/3333` case has an explicit positive necessary-incidence
control for these constraints; it is excluded by the separate
[balanced-case proof](1485_order_forty_twelve_balanced_incidence.md),
not by this page. No Lean theorem is asserted.

Assume the degree classes have sizes `(4,12,8,16)` at degrees
`(4,5,8,10)`, with balanced sharp degrees `(2^4,1^4)` on `B`.
Both `A` profile families are assumed to use single, distinct cosets,
whose four disjoint transversals are `P_p` and `Q_q`.
This hypothesis must be supplied by the separate mixed-coset exclusion,
not inferred from the capacities on this page. The
[no-high profile note](1485_order_forty_twelve_no_high_profiles.md)
and the [separate `4431` exclusion](1485_order_forty_twelve_thin_exclusion.md)
reduce the multiplicities on each
side to `4422`, `4332`, or `3333`.

## 1. The same twelve vertices carry both color systems

Distinct degree-five vertices have distinct whole profile pairs.
Consequently `A` is a twelve-cell subset `S` of the four-by-four
`P×Q` grid. Its four missing cells form the hole set `H`.

Each `a=(p,q)∈S` has sharp successor `F(a)∈B` and sharp
predecessor `G(a)∈B`. The binary matrix `C` is exactly

\[
C_{bd}=1\quad\Longleftrightarrow\quad
\text{there is a unique }a\in S\text{ with }G(a)=b,\ F(a)=d.
\]

The uniqueness follows from joint injectivity of `(G,F)`. Both
fibers over `b` have size `j_b`. Within an `F` fiber the `p`
labels are distinct; within a `G` fiber the `q` labels are distinct.
Thus two independently feasible color systems do not suffice: they
must be realized by these same twelve `C` edges.

Set `M_bp=|TopPred(b)∩P_p|` and `N_bq=|TopSucc(b)∩Q_q|`.
If the multiplicities are `u_p,v_q`, their exact margins are

\[
\sum_pM_{bp}=\sum_qN_{bq}=4,\qquad
\sum_bM_{bp}=20-4u_p,\quad
\sum_bN_{bq}=20-4v_q.
\tag{1}
\]

All entries lie between zero and three: a whole partition line would
make an internal-edge top return have size zero or four, whereas its
size is `1+β=1+η∈{1,2,3}`.

Let `I_d` be the predecessor colors in `F⁻¹(d)`, and `J_b`
the successor colors in `G⁻¹(b)`. On every internal edge `bDd`,
the two exact line-return formulas are

\[
\sum_{p\in I_d}M_{bp}+\eta(b,d)=3,\qquad
\sum_{q\in J_b}N_{dq}+\beta(b,d)=3.
\tag{2}
\]

Here `β(b,d)=Σ_x C_bx D_dx` and `η(b,d)=Σ_y D_yb C_yd`
are equal on the edge. These formulas do not posit uniform reverse
fibers or an affine structure on low-sharp profiles.

## 2. Affine medium-profile marginals

The [no-two-fours transversality argument](1485_order_forty_twelve_no_high_profiles.md#2-a-non-affine-sharp-degree-two-successor-profile-has-a-rigid-exceptional-set)
shows that if `u` contains at most one four, every medium-sharp
successor profile is an affine `P`-transversal. Its intersections
with the `Q` partition have rank two or rank one; rank zero would
make it a forbidden whole `Q` line. Hence each medium row of `N`
is `1111` or a permutation of `2200`.

Dually, if `v` contains at most one four, each medium row of `M`
has those forms. No such restriction is imposed from a `4422`
opposite multiplicity, or on a low-sharp row.

## 3. Hole capacities do not require affine coordinates

Fix `b∈B` and a hole `(p,q)`. Write `m=M_bp`, `n=N_bq`.
There are exactly `mn` pairs in

\[
(TopPred(b)\cap P_p)\times(TopSucc(b)\cap Q_q).
\]

No such pair can have a degree-five replacement, because `(p,q)`
is a hole. Thus its middle `b` is good unless the pair is central-valued.
Each `P` or `Q` line has distinct adjacent central labels. Among
these `mn` pairs, therefore, at most `min(m,n)` are central-valued.
The number of good pairs in this hole lies in

\[
mn-\min(m,n)\ \le\ g_b(p,q)\ \le\ mn.
\tag{3}
\]

Every good top pair with product `b` belongs to a hole: on an
occupied cell its degree-five vertex is a lower-degree replacement.
The [exact good-pair formula](1485_general_return_matching.md#5-bad-extension-balance-on-every-internal-edge)
gives

\[
g_b=12-3j_b-\tau_b,\qquad
\tau_b=\sum_{v,d}D_{vb}D_{bd}C_{vd}.
\]

Consequently the global necessary bounds are

\[
\boxed{
\sum_{(p,q)\in H}(M_{bp}N_{bq}-\min(M_{bp},N_{bq}))+\tau_b
\le12-3j_b
\le\sum_{(p,q)\in H}M_{bp}N_{bq}+\tau_b.}
\tag{4}
\]

There are also directional capacities. For any top predecessor `t`
of `b`, the four-element fiber `L_t⁻¹(b)` already contains the
`j_b` sharp `A` successors. It contains at most `4−j_b` good
top successors. Summing this bound over the `M_bp` choices of `t`
in `P_p` and using (3) gives

\[
\boxed{
\sum_{q:(p,q)\in H}(M_{bp}N_{bq}-\min(M_{bp},N_{bq}))
\le M_{bp}(4-j_b).}
\tag{5}
\]

The dual inequality sums over `p` at fixed `q`, with right side
`N_bq(4−j_b)`. These are upper bounds, not assertions that all
such top fibers have the same pattern of missing points.

## 4. Complete profile-grid normalization

Taking the opposite operation exchanges the two multiplicity patterns,
so list unordered pairs in the order `4422`, `4332`, `3333`.
Within each side, only labels of equal multiplicity are permuted.
The holes have row degrees `4−u` and column degrees `4−v`.
There are exactly the following orbits:

| `u` | `v` | Orbit | Hole cells `(p,q)` |
| --- | --- | ---: | --- |
| 4422 | 4422 | 0 | `(2,2),(2,3),(3,2),(3,3)` |
| 4422 | 4332 | 0 | `(2,1),(2,3),(3,2),(3,3)` |
| 4422 | 3333 | 0 | `(2,0),(2,1),(3,2),(3,3)` |
| 4332 | 4332 | 0 | `(1,1),(2,3),(3,2),(3,3)` |
| 4332 | 4332 | 1 | `(1,3),(2,3),(3,1),(3,2)` |
| 4332 | 3333 | 0 | `(1,0),(2,1),(3,2),(3,3)` |
| 3333 | 3333 | 0 | `(0,0),(1,1),(2,2),(3,3)` |

For example, the `4332/4332` hole graph has degrees `2,1,1`
on both active sides. Its two orbits distinguish whether the two
degree-two vertices are adjacent. All other displayed margins have
one orbit: the degree-one vertices are interchangeable. The generator
also exhausts all `16 choose 4` hole sets, filters by the exact
margins, and explicitly takes the margin-preserving permutation orbits.
Thus this normalization omits no profile grid. It does not assert that
arbitrary line relabelings preserve a fixed affine coordinate convention;
none of the encoded inequalities requires such a convention.

## 5. Encoding and independently checked refutations

[1485_n40_twelve_joint_capacity_cnf.py](../scripts/1485_n40_twelve_joint_capacity_cnf.py)
starts from the predecessor-line encoder, including exact `C,D`
margins, repeated-middle implication, internal edge balance, and
one-`A` five-cycle closure. It adds actual `F,G` maps on the
twelve occupied cells, their fiber and color conditions, the dual
matrix and return identities (1)–(2), §2's applicable affine marginal
conditions, and all of (4)–(5).

Three-bit monotone unary representations give each line intersection.
For values `m,n∈{0,1,2,3}`, the nine products of unary thresholds
sum to `mn`; removing the three diagonal products subtracts exactly
`min(m,n)`. This verifies the nonnegative-event encoding of (3)–(5).
All finite products and cardinalities use the previously audited exact
gate/threshold helper; repeated events retain their multiplicities.

Controls test all sixteen values of `(m,n)`, check the orbit inventory,
and evaluate every clause on a concrete positive `3333/3333` joint
system, including both actual sharp maps. Removing one required sharp
image from that assignment is rejected. The positive system is not a
magma model and must not be reported as an existence result.

All six other orbit systems have retained text LRAT refutations from
CaDiCaL 2.1.2 with `--lrat --no-binary --check`. Every solver returned
status 20, and the independent `lrat-check` accepted every proof with
status zero. The checker comes from `marijnheule/drat-trim`, commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, with source SHA256
`bf07c2ac96b9035da1ebcc578cb95e956a2b795629d613154cdb307f8a8f4a95`.

The [six-case archive](../data/1485_certificates/a12_joint/README.md)
contains the compressed refutations, exact generator/CNF/proof hashes,
and separate generation, solving, and checking times. The transparent
encoder, complete normalization, and independently checked refutations
together exclude the six stated cases; an unverified SAT verdict is
not used as a premise.

Observed totals were **18.810 seconds generation, 768.787 seconds
solving, and 11.092 seconds independent checking**, excluding archival
compression. The slowest solver run took 230.429 seconds; its independent
check took 3.301 seconds. The archive is 64,794,552 bytes compressed,
with all compressed and uncompressed hashes rechecked after archival.
An independent complete replay regenerated all six CNFs, matched every
hash, and checked every archived LRAT proof in **47.141 seconds**.

For the surrounding twelve/eight branch, the
[all-mixed exclusion](1485_order_forty_twelve_mixed_exclusion.md)
provides the single-coset reduction and the
[balanced-case proof](1485_order_forty_twelve_balanced_incidence.md)
treats the one case left by this table. Those remain separate proof
dependencies, not hypotheses silently added to these six CNFs.

# Eighteen tops cannot have eight all-four degree-five profiles

Independently audited proof, 20 September 2026.
Assume order forty, minimum degree four, eight central elements,
eighteen tops, and eight degree-five elements, all with four top
neighbors in each direction. There are six degree-eight elements.
The singleton-source saturation lemma reduces the proof to one
analytic mixed-count contradiction and an extension of the previously
audited 200-fixture check. No SAT or balanced-degree-eight
assumption is used, and nothing here is yet formalized in Lean.

For a top write `P,C` for its central block sizes, `α,β` for its
degree-five successor and predecessor counts, and

\[
                 v^+=7-2C-\alpha,\qquad v^-=7-2P-\beta.
\]

The [all-four reduction](1485_order_forty_eight_central_all_four.md)
gives `1≤P,C≤3`, `α≤f(C),β≤f(P)` with `f=(4,3,1)`, and

\[
 \sum v^+=\sum v^-=30,\quad \sum Pv^+=\sum Cv^-=32,
 \quad\sum(P-1)v^+=\sum(C-1)v^-=2.                    \tag{1}
\]

Each central row has `v^+` sum four, and each central column has
`v^-` sum four. The top-count bounds used below are

\[
 I,O\ge3,\quad I+P+\beta\le10,\quad O+C+\alpha\le10,
 \qquad O-I=5(C-P)+3(\alpha-\beta).                   \tag{2}
\]

The [singleton-source saturation theorem](1485_singleton_source_first_degree_saturation.md)
gives `α≤3` at `C=1`, and `β≤3` at `P=1`, since
`h=18>4²`. Thus singleton blocks contribute at least two units
to the corresponding deficits. Equation (1) immediately gives

\[
                     n13=n31=0,\qquad n12,n21\le1.   \tag{3}
\]

## 1. Every label supports a singleton; there are four or five triples

Let `p,q` count predecessor and successor triple blocks. Define
`n_pc` as the paired block count and put

\[
 U=n_{12},\qquad V=n_{21},\qquad U,V\le1.
\]

The predecessor singleton and double counts are `4+p` and
`14−2p`. Since `Σ(3−P)C=32`,

\[
 \sum_{P=2}C=32-2(4+p+U)=24-2p-2U\le3(14-2p).
\]

Thus `4p≤18+2U≤20`, giving `p≤5`; dually `q≤5`.
This uses neither the one-hole theorem nor a three-element profile.

Also `W^+:=Σ_(P>1)Pv^+≤4`. A row without a singleton-`P`
top would consume its full deficit four from this sum. Some positive
nonsingleton block would meet that row, but the same block meets
another row, giving an additional positive contribution. This is
impossible. Every label therefore supports a singleton `P` block,
and dually a singleton `C` block. Consequently

\[
                              p,q\in\{4,5\}.          \tag{4}
\]

If `p=4`, its eight singleton `P` labels are distinct. At their
rows the nonsingleton-`P` deficit is at most the global weighted
sum two in (1), so the unique singleton top has `v^+≥2`.
Hence `n13=0`. A type `(1,2)` top then has `α≤1`, while
its contribution to (1) forces `β≥3`. Equation (2) rules out
`α=0` and `β=4`, leaving

\[
 (\alpha,\beta)=(1,3),\qquad(v^+,v^-)=(2,2).          \tag{5}
\]

It consumes the entire dual weighted sum. Thus `n12≤1` when
`p=4`. Transposed conclusions hold when `q=4`.

## 2. Both triple counts four force the old 200-fixture profile

Put `x=n11,u=n12,v=n21,t=n33`. With (3), the four central
moments give

\[
\begin{aligned}
 x&=8-t,\\
 p&=4+u-t,&q&=4+v-t,\\
 n32&=4+u-2t,&n23&=4+v-2t,\\
 n22&=2-2u-2v+4t.                                   \tag{6}
\end{aligned}
\]

Since `p,q≥4`, we have `t≤min(u,v)`. The choice
`u=v=1,t=0` gives `n22=-2`, excluding `(p,q)=(5,5)`.
For `p=q=4`, (6) gives `u=v=t≤1`.
If this value is one, the unique `(1,2)` top and unique `(2,1)`
top consume the two weighted deficits, by (5) and its dual. Let
the first top's singleton `P` label be `r` and the second top's
singleton `C` label be `c`. The row at `r` needs two further
units of outgoing deficit, forcing `r` into the second top's `P`
block. The dual column argument forces `c` into the first top's
`C` block. Their rectangles overlap at `(r,c)`, impossible.
Thus the only remaining counts at `(p,q)=(4,4)` are

\[
               n11=8,\qquad n22=2,\qquad n23=n32=4.   \tag{7}
\]

Their eight unit rectangles have distinct predecessor and successor
labels, so every row and column is `3221`. Let `e_z` count
the two `(2,2)` predecessor blocks through `z`, and `f_z` the
corresponding successor count. The triple-block multiplicities are
`λ_z=2−e_z`, `μ_z=2−f_z`, and `Σe=Σf=4`. Thus

\[
       16\ge\sum_z\lambda_z\mu_z=16+\sum_z e_zf_z.
\]

The two deficiency supports are disjoint and every predecessor
triple meets every successor triple exactly once. These facts
follow here directly from (7), without a small first profile.

All hypotheses of the normalized
[200-fixture construction](1485_order_forty_eight_central_eighteen_two_small.md#common-finite-central-profile-lemma)
now hold. Its generator does not encode the size of a first profile.
The following separate check shows that those same 200 central
systems admit no **four-element** first-output profile either.
This excludes (7).

### The four-profile extension of the finite lemma

The original central generator is unchanged. The new wrapper is
[1485_m8_eighteen_four_profile_check.py](../scripts/1485_m8_eighteen_four_profile_check.py).
On every fixture it enumerates all four-element subsets of the full
eighteen-top set whose `P` blocks partition the eight labels, and
does the same for `C`. For each resulting pair `U,V`, it tests
that `(|C_u∩P_v|)_(u∈U,v∈V)` is a permutation matrix. These are
exactly the necessary
[first-output profile conditions](1485_first_successor_degree_profiles.md).
All four-block patterns are included.

| Normalized grid | Fixtures with 11 / 11 partition choices | Fixtures with 13 / 13 choices | Compatible pairs |
| --- | ---: | ---: | ---: |
| One eight-cycle | 8 | 32 | 0 |
| Two four-cycles | 32 | 128 | 0 |

Every fixture is independently checked as a central rectangle
system, and its profile result is compared with a literal-set oracle.
A partial incidence fixture makes both oracles accept a marked
four-profile; a damaged version rejects it. The partial fixture is
not claimed to be a magma. The wrapper also reruns the original
normalization and positive controls and refuses Python's `-O` mode.

```sh
python3 scripts/1485_m8_eighteen_four_profile_check.py
```

The initial complete run took 7.270 seconds. A separate root replay
using the generic full-subset oracle from the fifteen-top work also
found zero four-profiles on all 200 fixtures, in 4.753 seconds including
generation. The wrapper's full source and both oracles were
independently audited. The root's complete production-wrapper replay
then passed in 7.241 seconds, with the stated inventories and all
200 literal-oracle comparisons.

## 3. Mixed triple counts force too many maximal intersections

Suppose `p=4,q=5`; the reverse case is dual. Equation (6) and
`u,v≤1` give `u=t=0,v=1`. The matrix is

\[
                    \begin{pmatrix}8&0&0\\1&0&5\\0&4&0\end{pmatrix}.
\]

There is one unit in every row. Let `D` be the two-element `P`
block of the unique `(2,1)` top. Rows in `D` have two singleton
successor blocks and are `3311`; all others are `3221`.
Predecessor triples are precisely the `(3,2)` tops, so their
multiplicity is zero on `D` and two outside. Every column has a
singleton-`C` top by §1, hence has pattern `3311` or `3221`.
Successor triples are precisely the five `(2,3)` tops, so their
multiplicity `μ` is at most two and `Σμ=15`. The total
maximal-block intersections are consequently at least

\[
                    2\sum_{z\notin D}\mu_z\ge2(15-4)=22,
\]

but there are only twenty maximal-block pairs, each intersecting
in at most one label. This excludes the mixed case and its dual.
All possibilities in (4) are now impossible, completing the exclusion
of `m=8,h=18,a=8,q=0`.

Together with the previous
[one-small-profile](1485_order_forty_eight_central_eighteen_one_small.md)
and [two-small-profile](1485_order_forty_eight_central_eighteen_two_small.md)
exclusions, and the weighted bound `q≤2`, this excludes **all**
eighteen-top configurations with eight degree-five elements. It does
not exclude the eighteen-top cases with seven degree-five elements
or the whole order-forty frontier.

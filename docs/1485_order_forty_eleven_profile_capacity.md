# Order forty: profile capacities in the eleven-by-nine branch

Research note, 20 September 2026. This is a **checked finite exclusion**:
the degree-class sizes `(4,11,9,16)` at degrees `4,5,8,10` cannot
occur in an E1485 magma of order forty. The reduction is analytic;
the contradiction uses 37 retained LRAT refutations, each checked by
an independent proof checker. This is not a purely analytic proof or
a Lean theorem, and does not exclude other degree-class splits.

Use the four degree classes `Z,A,B,T` of degrees `4,5,8,10` and
sizes `4,11,9,16`. Every vertex has four top neighbors in each
direction. The positive balanced sharp degrees `j_b` on `B` sum
to eleven, so their two possible distributions are

\[
\boxed{(3,1^8)\quad\text{or}\quad(2,2,1^7).}
\]

Write `D` for internal `B` adjacency, with margins `4−j_b`, and
`C` for sharp two-step adjacency through `A`, with margins `j_b`.
The onto sharp maps `F,G:A→B` have fibers of size `j_b`.
As before `U_a,V_a` are the top profiles of `a∈A`, and
`X_b=TopPred(b)`.

## 1. No profile occurs four times

Suppose a predecessor profile `U` occurs `u≥4` times. Its `F`
images are distinct: equal `F` at two distinct `A` vertices would
require their predecessor profiles to be disjoint.

At most two vertices of `B` have sharp degree greater than one,
so choose two sharp-degree-one `F` images `d,e` of these occurrences.
Each has three internal predecessors. Their predecessor union `P`
has size at least three.

For every `b∈P`, the internal-edge fiber formula at its edge into
`d` or `e` gives

\[
|X_b\cap U|=3-\eta\ge2,
\qquad \eta\in\{0,1\}.
\]

The same top-incidence capacity as in the
[ten-by-ten note](1485_order_forty_ten_profile_expansion.md) gives

\[
6\le\sum_{b\in B}|X_b\cap U|
=20-\sum_{a\in A}|U\cap U_a|
\le20-4u\le4,
\]

a contradiction. Thus every predecessor profile has multiplicity
at most three, and the dual statement holds for successor profiles.

## 2. Some repeated triple contains two low-sharp F images

By the [large-class profile theorem](1485_min_four_large_five_class.md),
after choosing an orientation there are two possibilities.

If one predecessor family uses a single Klein-four coset, its
multiplicities must be `(3,3,3,2)`. Otherwise the two-by-two-coset
exceptional pattern has a full three-by-three rectangle of nine ordinary
profiles, and two exceptional profiles. Its three ordinary predecessor
profiles each occur three times.

In either case there are three disjoint triple fibers in `A`.
In the one-high-sharp distribution every such fiber has at least two
low-sharp `F` images. In the two-medium distribution the two medium
`F` fibers contain only four `A` vertices altogether. They cannot
supply two members to each of the three triples. Hence at least one
triple has two distinct low-sharp `F` images `d,e`.

Let `U` denote that triple profile and put

\[
P=Pred_D(\{d,e\}),\qquad h=|P|.
\]

Each vertex in `P` contributes at least two to its `U` intersection,
while the total capacity is at most eight. Therefore

\[
\boxed{3\le h\le4.}                                  \tag{1}
\]

## 3. The exact eta constraint is stronger than small expansion

Because `d,e` have sharp degree one, each has a unique `C`
predecessor; denote these by `γ(d),γ(e)`. On any internal edge
`bDs`, where `s∈{d,e}`,

\[
|X_b\cap U|=3-\eta(b,s),\qquad
\eta(b,s)=D_{\gamma(s),b}\in\{0,1\}.                  \tag{2}
\]

If `b` points to both `d,e`, the two eta values must therefore
agree. For `b∈P`, let `ε_b` be this eta value, using either
available edge. If `q` is the number of `A` profiles outside the
Klein-four coset containing `U`, the exact capacity refinement gives

\[
\boxed{\sum_{b\in P}(3-\varepsilon_b)\le8-q.}          \tag{3}
\]

In the exceptional two-by-two pattern, `q=1`. Equations (1)–(3)
then force `h=3` and `Σε_b≥2`. In the single-coset case `q=0`:
`h=3` requires `Σε_b≥1`, while `h=4` requires all four eta
values to be one.

Small expansion alone is insufficient in the two-medium distribution:
there are internal incidence pairs obeying the basic degree, repeated
middle, edge-balance, one-`A` closure, and mixed-capacity tests with two
low-sharp columns sharing just three predecessors. The equality of eta
values in (2), and the remaining profile information, must not be dropped.

## 4. Exact line-capacity equations in the single-coset case

Now restrict to sharp distribution `(2,2,1,1,1,1,1,1,1)` and a
single predecessor coset with four disjoint transversals `U_0,...,U_3`.
Label their multiplicities `(3,3,3,2)` and put

\[
M_{bp}=|X_b\cap U_p|.
\]

The four transversals partition the sixteen tops. The top-degree
incidence calculation gives

\[
\boxed{
\sum_pM_{bp}=4,
\qquad (\sum_bM_{bp})_{p=0}^3=(8,8,8,12).
}                                                       \tag{4}
\]

For each `d∈B`, let `I_d` be the set of colors of the profiles
in `F⁻¹(d)`. These colors are distinct, so `|I_d|=j_d`; globally
their color multiplicities are again `(3,3,3,2)`.

The top part of `R_d⁻¹(b)` on an edge `bDd` is

\[
X_b\setminus\bigcup_{a:F(a)=d}U_a.
\]

Its size is `1+η(b,d)`, where
`η(b,d)=Σ_y D_yb C_yd`. Since the `U_p` are disjoint, this gives
the exact linear edge constraint

\[
\boxed{bDd\ \Longrightarrow\
\sum_{p\in I_d}M_{bp}+\sum_yD_{yb}C_{yd}=3.}          \tag{5}
\]

In this two-medium case all `M_bp≤3`. Otherwise one row of `M`
would consist of a single four and three zeros. Every vertex has an
internal successor, and the left profile sum in (5) would be zero or
four, whereas its required value `3−η` lies between one and three.

Equations (4)–(5) use only line intersections, not full affine coordinates
for the `B` profiles. They do not assume that the other `A` profile
family also uses a single coset.

## 5. The complete normalization inventory

Let `H` be the number of high-sharp labels: one in distribution
`(3,1^8)`, two in `(2,2,1^7)`. Normalize these labels as
`{0,...,H−1}` and the selected low-sharp pair as `S={H,H+1}`.
All remaining labels have sharp degree one.

For the exact predecessor set `P=Pred_D(S)`, record

\[
h=|P|,\qquad a=|P\cap\{0,\ldots,H-1\}|,
\qquad i=|P\cap S|.
\]

Permuting within the high class, within `S`, and within its low-sharp
complement gives the canonical representative

\[
P=\{0,\ldots,a-1\}\cup\{H,\ldots,H+i-1\}
\cup\{H+2,\ldots,H+1+h-a-i\}.
\]

The complete parameter ranges are `0≤a≤H`, `0≤i≤2`, and
`0≤h−a−i≤7−H`. These permutations preserve every mathematical
condition used in the encoding. No matrix entries or other profiles
are normalized without justification.

| Mode | Sharp degrees | `h` | Allowed `(a,i)` | Cases |
| --- | --- | --- | --- | ---: |
| One high | `(3,1^8)` | 3 and 4 | `{0,1}×{0,1,2}` for each `h` | 12 |
| Exceptional two-coset | `(2,2,1^7)` | 3 | `{0,1,2}²` except `(2,2)` | 8 |
| Single coset | `(2,2,1^7)` | 3 | `{0,1,2}²` except `(2,2)` | 8 |
| Single coset | `(2,2,1^7)` | 4 | All of `{0,1,2}²` | 9 |

In the single-coset mode, relabel the three triple profiles so the
selected one is color zero; the normalized pair `S` belongs to its
`F`-color set. The double profile is color three. A genuine profile
system therefore supplies a satisfying assignment of all the color
and matrix variables whenever its incidence pair survives a case.

## 6. Necessary Boolean constraints and encoding audit

The deterministic encoder
[1485_n40_eleven_capacity_cnf.py](../scripts/1485_n40_eleven_capacity_cnf.py)
uses the following common constraints on the binary nine-by-nine
matrices `D,C`:

1. Both margins of `D` equal `4−j`, and both margins of `C` equal `j`.
2. Two distinct internal ordinary middles imply a sharp replacement:
   `(D²)_bd≥2 ⇒ C_bd=1`.
3. The [return-matching bound](1485_general_return_matching.md) gives
   `j_b+j_d>5 ⇒ C_bd=1`. Here its only nonvacuous instance is
   `C_hh=1` in the one-high case.
4. On every edge `bDd`, bad-extension balance gives `β(b,d)=η(b,d)`,
   where `β(b,d)=Σ_x C_bx D_dx` and `η(b,d)=Σ_y D_yb C_yd`.
5. The one-`A` five-cycle rule gives
   `aDbDcDd` and `C_da=1 ⇒ C_ac=C_bd`.

These are the same necessary incidence rules used in the
[twelve-by-eight exclusion](1485_order_forty_twelve_one_high_exclusion.md#2-necessary-boolean-constraints).
Loops and repeated labels are allowed. No additional mixed-return
capacity, all-`B` five-cycle constraint, affine `B`-profile assumption,
or conjectured full-core identity is imposed.

Every mode fixes the exact predecessor union `P` from §5. The one-high
mode requires nothing further. The exceptional mode adds (2)–(3) with
capacity seven. The single-coset mode adds (2)–(3) with capacity eight,
the color memberships `I_d`, and all of (4)–(5).

The shared CNF helper defines conjunctions by equivalences and counts
with exact sequential unary thresholds. Its exhaustive controls include
repeated, negated, and constant literals. Equality of `β,η` is imposed
through thresholds up to `max(j_b,j_d)`; their margins already bound
them by `j_b,j_d`, respectively, so this truncation loses nothing.
Each `M_bp` is represented by its three unary thresholds, with
monotonicity imposed. Products of these thresholds with a color-membership
bit encode the sum in (5), with multiplicity retained.

Further controls verify the exact 12+8+17 inventory, evaluate a concrete
two-medium incidence pair satisfying the common constraints and the
capacity-eight pair test, and confirm that capacity seven rejects that
same pair. All `4^4·2^4` choices of a row of `M` and a selected color
subset are checked against the direct integer sum. A hypothetical magma
therefore gives a satisfying primary assignment, and the exact gate
definitions supply all auxiliary values.

## 7. Independently checked refutations

All 37 CNFs were refuted by CaDiCaL 2.1.2 with
`--lrat --no-binary --check`; every solver run returned status 20.
Every resulting text LRAT proof was then accepted by the independently
compiled `lrat-check` from `marijnheule/drat-trim`, commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`.

| Mode | Cases | Variables | Clauses | Generation | Solving | Independent checking |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| One high | 12 | 5,048 | 30,705–30,706 | 8.534 s | 44.505 s | 2.591 s |
| Exceptional | 8 | 5,096 | 30,864 | 5.679 s | 4.207 s | 0.676 s |
| Single coset | 17 | 18,328–18,338 | 70,416–70,445 | 15.724 s | 31.842 s | 2.258 s |
| Total | 37 | — | — | 29.938 s | 80.554 s | 5.525 s |

These are observed wall-clock totals for the separate stages, not
including archival compression. The slowest individual solver run was
18.389 seconds and the slowest independent check 0.798 seconds.

The [A11 certificate inventory](../data/1485_certificates/a11/README.md)
retains all 37 compressed proofs, exact CNF/proof/archive SHA256 hashes,
individual timings, checker outputs, and a solver-free replay command.
The archive totals 10,172,596 compressed bytes (50,359,406 bytes of
text LRAT). Its CNFs are regenerated deterministically, not inferred
from the solver's reports.

The complete normalization in §5 and these checked refutations exclude
both sharp-degree distributions and both profile alternatives. Thus the
entire eleven-by-nine degree split is excluded. The remaining gap toward
the spectrum characterization is elsewhere, not an unchecked SAT verdict
inside this branch.

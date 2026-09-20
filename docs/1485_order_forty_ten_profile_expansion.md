# Order forty: repeated profiles force poor expansion in the ten-by-ten case

Research note, 20 September 2026. This is a **completed finite-assisted
exclusion of the entire ten-by-ten branch** at order forty and central
count four. The profile reduction is analytic; the final graph lemma
has eight explicit LRAT refutations, all independently verified. This
is not a Lean theorem or an exclusion of every order-forty model.

Use the degree classes `Z,A,B,T` of degrees `4,5,8,10` and sizes
`4,10,10,16`. Every vertex has four top predecessors and successors.
The sharp maps `F,G:A→B` are bijections: every `A` has one sharp
neighbor in each direction, every `B` has a positive balanced sharp
degree, and their ten sharp degrees sum to ten.

Let `D` be ordinary adjacency on `B`, which is 3-regular in both
directions. Let `C_bd=1` record the unique sharp `A` middle from
`b` to `d`. Then `C` is a permutation matrix. Write `U_a,V_a` for
the top predecessor/successor profiles of `a∈A`, and `X_b` for the
top predecessor profile of `b∈B`.

## 1. Every internal edge forces an intersection of size at least two

For `b D d`, put `a_d=F⁻¹(d)`. The exact top part of the
five-element return fiber is

\[
T\cap R_d^{-1}(b)=X_b\setminus U_{a_d}.                 \tag{1}
\]

Indeed a top path `t→b→d` can only have a lower replacement in
`A`; its sharp successor must be `d`, uniquely identifying `a_d`.
Among the non-top predecessors of `b`, its unique sharp `A`
predecessor always belongs to this fiber. Its three `B` predecessors
belong except for those counted by

\[
\eta(b,d)=\#\{y:yDb,\ C_{yd}=1\}\in\{0,1\}.
\]

Thus the fiber has `4−η` non-top members and `1+η` top members.
Since `|X_b|=4`, (1) gives

\[
\boxed{bDd\ \Longrightarrow\
|X_b\cap U_{F^{-1}(d)}|=3-\eta(b,d)\ge2.}               \tag{2}
\]

This is the sharp-degree-one specialization of the
[exact internal-edge fiber formula](1485_order_forty_thirteen_profiles.md#2-no-b-predecessor-profile-is-a-p-line).
It does not assume that `C` is the identity or that `D` is symmetric.

## 2. Repeated-profile expansion bound

Suppose a particular predecessor profile `U` occurs at `u` vertices
of `A`, and let `S` be their distinct `F` images. Thus `|S|=u`.
For every `b∈Pred_D(S)`, equation (2) gives `|X_b∩U|≥2`.

At a top point `t`, its ten ordinary successors consist of one
central vertex, four tops, `ν(t)` vertices of `A`, and `5−ν(t)`
vertices of `B`. Consequently

\[
\begin{aligned}
2|Pred_D(S)|
&\le\sum_{b\in B}|X_b\cap U|\\
&=\sum_{t\in U}(5-\nu(t))\\
&=20-\sum_{a\in A}|U\cap U_a|\\
&\le20-4u.                                             \tag{3}
\end{aligned}
\]

All `A` profiles have a common permutation parity. Profiles in
the same Klein-four coset are identical or disjoint; profiles in
different cosets of that parity meet once. If `e` is the number
of `A` vertices whose predecessor profile lies outside the coset
containing `U`, the exact refinement is therefore

\[
\boxed{2|Pred_D(S)|\le20-4u-e.}                         \tag{4}
\]

Since `D` is 3-regular in both directions, `|Pred_D(S)|≥|S|=u`.
Thus **every predecessor profile has multiplicity at most three**.
By duality the same holds for successor profiles.

For a profile occurring three times, (3) gives

\[
\boxed{|S|=3,\qquad 3\le|Pred_D(S)|\le4.}              \tag{5}
\]

If any other predecessor coset occurs, `e≥1` improves the upper
bound to three.

## 3. A repeated triple is unavoidable in one orientation

The [large-class profile theorem](1485_min_four_large_five_class.md)
has two possibilities at `|A|=10`.

If one family uses a single coset, its ten profiles occupy four
transversals, so one occurs at least three times. Section 2 makes
its multiplicity exactly three.

Otherwise the two-by-two-coset exceptional pattern applies. The eight
ordinary vertices occupy eight distinct cells of a three-by-three
profile rectangle, while two exceptional vertices use the omitted
profiles. Two of the ordinary predecessor profiles occur three times;
the same is true on the successor side. On each side there is one
profile in another coset. Equation (4) therefore gives a three-element
set with **exactly three** internal predecessors (and dually successors).

Thus excluding the expansion failure (5), in both orientations,
excludes the whole ten-by-ten branch. No assumption that every profile
family uses a single coset is needed.

## 4. The Petersen internal graph is impossible

Any three vertices of the Petersen graph have at least six neighbors:
each has three neighbors, and any pair has at most one common neighbor,
so inclusion-exclusion gives a lower bound `9−3=6`.
This contradicts (5), in whichever orientation supplies the repeated
profile. Therefore

\[
\boxed{D\text{ cannot be the Petersen graph, for any permutation }C.}
\]

This is a top-profile obstruction, not a consequence of the basic
internal incidence constraints. Indeed `C=I` with Petersen adjacency
satisfies those constraints. Its strongly regular identities are

\[
D^2=2I+J-D,\qquad D^3=3D+2J-2I.
\]

Deleting the backtracking length-three walks gives

\[
G=D^3-5D=2(J-I-D),\qquad K=CD+DC+G=2(J-I).
\]

Thus the uniform mixed-return bound `K≤4` and its internal-return
refinements hold. Edge balance is automatic for `C=I`; the one-`A`
three-edge closure condition is vacuous because Petersen has no
closed walk of length three. This explains why those tests alone
did not eliminate this candidate.

## 5. The certified finite expansion lemma

The following finite graph statement completes the exclusion:

> Let `D` be a binary 3-in/3-out regular matrix on ten vertices,
> and `C` a permutation matrix. Assume that every entry of `D²`
> greater than one is marked by `C`, bad-extension balance holds
> on every internal edge, and every one-`A` five-walk obeys its
> closure identity. Then every three-element set has at least
> five `D` predecessors.

The constraints are invariant under transposing both matrices, so
this one statement also supplies the successor version.
Its necessary hypotheses are recorded explicitly in the
[internal-incidence note](1485_order_forty_thirteen_two_high.md#incidence-data-and-necessary-constraints).
They are valid for the present class sizes independently of that note's
specialized thirteen/seven enumeration.

To check the statement, normalize `S={0,1,2}`. Regularity makes
`h=|Pred_D(S)|≥3`; only `h=3,4` need exclusion. The overlap
`i=|S∩Pred_D(S)|` is `0,1,2,3`. Relabeling gives exactly eight
cases, with

\[
Pred_D(S)=\{0,\ldots,i-1\}\cup\{3,\ldots,h-i+2\}.
\]

All eight cases now have checked refutations, with the encoding and
verification described below. Thus (5) is impossible, and the entire
ten-by-ten degree split is excluded.

A useful analytic reduction for these cases is already available.
If two `D` columns share at least two predecessors, their corresponding
rows are disjoint: a shared successor would give two repeated entries
of `D²` in the same column, contrary to `C` being a permutation.
For three columns with a predecessor union of size at most four,
every pair shares at least two predecessors. Their three rows are
therefore disjoint and together cover nine vertices. This reduction
does not on its own prove that the eight cases are impossible.

## 6. Transparent CNF and independent proof checking

The encoder
[1485_n40_ten_expansion_cnf.py](../scripts/1485_n40_ten_expansion_cnf.py)
uses exactly **200 Boolean variables**, the entries of `D` and `C`.
There are no auxiliary variables, cardinality counters, or SMT conversion.
An exact cardinality `k` is encoded directly: every `k+1` entries
cannot all hold, and every `10-k+1` entries cannot all fail.

For clarity, all remaining clause families are the direct Boolean
translations of these statements, with repeated vertices allowed:

- `D_ab D_bc D_ad D_dc` with `b≠d` implies `C_ac`.
- `D_ab C_ac C_db` implies `D_bc=D_da`. Since `C` is a permutation,
  these are precisely the two possible bad extensions of `aDb`.
- `D_ab D_bc D_cd C_da` implies `C_ac=C_bd`.
- Every row in the specified predecessor set meets `S`, and no row
  outside it meets `S`.

Duplicate literals are removed and tautological clauses discarded.
The program checks the cardinality clauses against every ten-bit truth
assignment. As a substantive positive control, it checks that Petersen
adjacency with `C=I` satisfies **all unnormalized constraints**, and
fails each compressed-predecessor normalization. Removing an adjacency
entry or a permutation entry is correctly rejected. The mathematics,
normalization, and encoder were also audited separately.

The cases with three predecessors have 49,784 clauses; those with four
have 49,782. CaDiCaL 2.1.2 produced text LRAT proofs, independently
checked with `lrat-check` from `marijnheule/drat-trim`, commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`. The checker and its
positive/negative controls are documented in the
[certificate inventory](../data/1485_certificates/README.md).

| Predecessors `h` | Overlap `i` | Proof generation (s) | Independent checking (s) |
|---:|---:|---:|---:|
| 3 | 0 | 0.06 | 0.13 |
| 3 | 1 | 0.92 | 0.31 |
| 3 | 2 | 0.03 | 0.07 |
| 3 | 3 | 0.03 | 0.07 |
| 4 | 0 | 0.09 | 0.09 |
| 4 | 1 | 30.30 | 3.81 |
| 4 | 2 | 0.74 | 0.21 |
| 4 | 3 | 0.06 | 0.08 |

These are observed wall-clock timings under concurrent load, not Lean
elaboration times. CNF generation, including exhaustive controls, took
approximately 0.3–0.6 seconds per case. The slowest solver case was
rerun with an explicit timer and produced a byte-identical refutation.
Every solver exited with UNSAT status 20; every independent proof check
reported `VERIFIED` and exited with status zero.

Compressed proofs and hashes are retained in
[the A10 certificate inventory](../data/1485_certificates/A10.md).
A SAT solver is unnecessary to replay the proofs. The conclusion uses
the analytic reduction plus those certificates, not an unverified
diagnostic solver report.

# Order forty: nine central elements and sixteen tops are impossible

Research note, 20 September 2026. The proof consists of analytic
reductions and two explicit finite graph lemmas. The mixed-case lemma
has independent Python and C++ implementations. This is **not a Lean
theorem**, and does not exclude all models with nine central elements,
all models of order forty, or all non-square/twice-square orders.

## 1. The analytic reduction and the last counting target

The [degree-count note](1485_nine_central_sixteen_degree_counts.md)
reduces a hypothetical order-forty model with minimum degree four,
nine central elements, and sixteen tops to the following data:

- Degree-five class `A=A3⊔A4`, with `|A3|=2`, `|A4|=5`.
  The subscripts give the number of top neighbors in each direction.
- Degree-eight class `B=L⊔H`, with `|L|=|H|=4` and top counts
  three on `L`, five on `H`.
- Sharp in- and out-degrees balance. A unique vertex `k∈L` has
  sharp degree two, and every other member of `B` has sharp degree one.
- Ordinary internal adjacency `D` on `B` has in- and out-degrees
  three at `k`, four at the other three members of `L`, and two
  at every member of `H`.

Let `Q_xy=1` mean that `x⇒a⇒y` is a two-sharp-edge path through
some `a∈A`. Good-middle uniqueness makes `Q` zero-one. Every
member of `A3` contributes a two-by-two rectangle to `Q`, both
contained in `L×L`; each member of `A4` contributes one pair.
These thirteen pairs are all distinct. A two-edge internal `B` path
is bad exactly when its endpoints belong to `Q`.

The [central-pair budget](1485_nine_central_sixteen_degree_counts.md#13-central-pair-capacity-locates-the-exceptional-sharp-degree)
gives at most eight top pairs with product in `L`. On the other hand,
their exact number is

\[
\sum_{x\in L}g_x
=\sum_{x\in L}3(4-j_x)-\tau_L
=33-\tau_L,
\]

where `τ_L` counts bad internal `B` paths whose middle lies in `L`.
Thus it remains to contradict

\[
                            \tau_L\ge25.                 \tag{1}
\]

The same section proves two local facts used below. For an ordinary
edge `xDy`, put

\[
\eta(x,y)=\sum_zD_{zx}Q_{zy},\qquad
\beta(x,y)=\sum_zD_{yz}Q_{xz}.
\]

Then `η=β` on `L→L` edges, `(η,β)=(1,0)` on `L→H`
edges, and `(η,β)=(0,1)` on `H→L` edges. These statements
come from the equality of the two central-block sums in a translation
fiber, not from an assumed uniform auxiliary relation.

## 2. Complete normalization of the sharp data on four vertices

The two `A3` sharp rectangles are disjoint. Hence their predecessor
pairs are disjoint or their successor pairs are disjoint. Passing to
the dual magma if necessary, arrange that their predecessor pairs
partition `L`. Name `k=0`, its partner `1`, and the other pair `2,3`.
Let `s,t` be the two distinct-element successor pairs of these `A3`
vertices. The `A3` contribution on `L` then has rows

\[
                             (s,s,t,t).                  \tag{2}
\]

Every member of `L` now has one sharp successor in `A3`. Thus the
unique remaining sharp edge from `L` into `A4` starts at `0`.
In the opposite direction, exactly one sharp edge from `A4` ends
in `L`; call its target `m`. The column multiplicities of (2),
divided by two, have deficits relative to `(2,1,1,1)` equal to
one at `m` and zero elsewhere. Equivalently, either `s,t` are
disjoint, or they intersect only at `0`. There are exactly twelve
ordered possibilities for `(s,t,m)`, checked explicitly below.

There are two exhaustive cases: these remaining low sharp edges
meet the **same** member of `A4`, or they meet **different** members.

Let `F=D|_(L×L)` and write `e=|F|`. Every vertex has balanced
internal degree, so the numbers of ordinary `L→H` and `H→L`
edges are both

\[
                             \ell=15-e.
\tag{3}
\]

As the four high vertices have internal degree two, `ℓ≤8` and
`e≥7`. The row and column of `F` at `0` have at most three
entries. Finally, for low endpoints outside `Q`, there is at most
one internal path through a low vertex:

\[
                    (F^2)_{xy}\le1\quad\text{if }Q_{xy}=0.
\tag{4}
\]

Two different degree-eight middles would otherwise force a strictly
smaller good middle, necessarily in `A`, contrary to `Q_xy=0`.

## 3. Same member of `A4`: the first finite graph lemma

In this case `Q_L` is (2) plus the pair `(0,m)`. That pair must
not already be in (2), since different products cannot share endpoints.
There are no `Q` pairs between `L` and `H`. Consequently, on
every edge of `F`, the identity `η=β` is expressed entirely in
terms of the two four-by-four matrices `F,Q_L`.

Put `B(F,Q_L)=Σ_(Q_L(x,y)=1)(F²)_xy`. The `L→H` edges
each have `η=1`, so

\[
                          \tau_L=B(F,Q_L)+15-e.          \tag{5}
\]

The [same-case graph lemma](1485_nine_central_same_low_sharp.md)
proves that the right side is at most twenty, contradicting (1).
Its checker also retains `η≤3` on low internal edges, since the
corresponding top fiber is contained in three top predecessors.

## 4. Different members of `A4`: the mixed graph lemma

Now `Q_L` is exactly (2). There is a unique sharp endpoint pair
`(0,g)` from `L` to `H`, and a unique such pair `(h,m)` from
`H` to `L`. The high vertices `g,h` need not be distinct. Define
binary vectors on `L` by

\[
                       v_x=D_{hx},\qquad w_y=D_{yg}.
\]

Their weights are at most two. The cross-edge identities above give

\[
                  v_x\le F_{xm},\qquad w_y\le F_{0y}.
\tag{6}
\]

Indeed, on `h→x`, `β=1` requires `x→m` because `m` is
the unique sharp endpoint from `h`. On `y→g`, `η=1` requires
`0→y` because `0` is the unique sharp predecessor endpoint of `g`.

On every edge `xFy`, the equality `η=β` is exactly

\[
\sum_{z\in L}F_{zx}Q_{zy}+\mathbf1_{y=m}v_x
=\sum_{z\in L}F_{yz}Q_{xz}+\mathbf1_{x=0}w_y.
\tag{7}
\]

Summing (7) over these edges cancels the internal terms. By (6),
the extra sums are respectively `|v|` and `|w|`, proving
`|v|=|w|`. Counting bad predecessors over all edges out of `L`
now gives

\[
                       \tau_L=B(F,Q_L)+15-e+|v|.         \tag{8}
\]

The [mixed-case checker](../scripts/1485_nine_central_sixteen_mixed_check.py)
loops over all `2^16` matrices `F`, all twelve normalized sharp
tables, and every pair of binary vectors satisfying (6) and
`|v|=|w|≤2`. It imposes (4), the row/column degree bounds, and
the exact equation (7). The following are the exhaustive maxima of
(8). Pairs are encoded by four bits, with vertex zero as the low bit.

| `s` | `t` | `m` | Maximum (8) | Partial fixtures |
| --- | --- | ---: | ---: | ---: |
| `0011` | `0101` | 3 | 21 | 57 |
| `0011` | `1001` | 2 | 21 | 57 |
| `0011` | `1100` | 0 | 24 | 605 |
| `0101` | `0011` | 3 | 20 | 25 |
| `0101` | `1001` | 1 | 20 | 36 |
| `0101` | `1010` | 0 | 20 | 88 |
| `0110` | `1001` | 0 | 17 | 67 |
| `1001` | `0011` | 2 | 20 | 25 |
| `1001` | `0101` | 1 | 20 | 36 |
| `1001` | `0110` | 0 | 20 | 88 |
| `1010` | `0101` | 0 | 17 | 67 |
| `1100` | `0011` | 0 | 17 | 38 |

Thus `τ_L≤24`, again contradicting (1). These partial fixtures
are not magma models. In particular the attaining fixture at twenty-four
only verifies that the finite lemma is nonvacuous; it does not assert
the existence of any E1485 model.

## 5. Verification and scope

The analytic degree reductions, local inequalities, normalization,
and reduction to graph constraints must be read separately from the
finite checks; successful enumeration alone does not justify them.
The finite lemmas use only sixteen adjacency bits, not a search of
forty-element operation tables, and require no SAT or floating-point
optimization premise.

The mixed check runs with Python's standard library:

```sh
python3 scripts/1485_nine_central_sixteen_mixed_check.py
python3 scripts/1485_nine_central_same_low_sharp.py --reference-audit 1024
```

It checks 160,508 boundary-vector pairs, leaving 1,189 partial
fixtures, and took **3.909 seconds** on this workspace. An independent
C++ implementation produced exactly the same twelve maxima and counts.
Assertions check every maximum, every fixture count, and an explicit
attaining fixture; `python -O` is refused rather than silently dropping
these checks.

The [same-case inventory](1485_nine_central_same_low_sharp.md)
records all nine normalized cases and its positive and rejected controls.
An independent replay with the displayed larger reference audit checked
589,824 masks, reproduced all 152 accepted partial fixtures and maximum
twenty, and took **6.698 seconds**. Both the mathematical reductions
and the complete checker sources were independently read and audited.
An independent replay of the mixed checker reproduced every count and
maximum in **5.254 seconds**.

Thus both final cases contradict `τ_L≥25`, completing the exclusion
of nine central elements and sixteen tops at order forty. Neither finite
lemma is currently a Lean declaration. The full square-or-twice-square
theorem remains open.

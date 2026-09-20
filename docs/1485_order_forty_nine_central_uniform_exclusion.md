# An odd-degree incidence obstruction excludes uniform degree-eight top counts

Research theorem, 20 September 2026. This is an independently audited
analytic graph obstruction, with a consequence for the remaining
order-forty nine-central branch. It uses no graph enumeration,
projective-plane classification, SAT result, or unproved uniformity
assumption. It is not yet a Lean theorem.

## 1. The general finite graph lemma

Let `k≥3` be odd and `v=k²−k+1`. There are no binary matrices
`D,Q` on `v` vertices satisfying all of the following:

- `D` has row and column degree `k`, and `Q` is a permutation matrix.
- Repeated middles require a sharp replacement:
  `(D²)_xz≥2` implies `Q_xz=1`.
- The one-sharp-middle five-cycle rule holds:

  \[
  aDbDcDd,\quad Q_{da}=1
  \quad\Longrightarrow\quad Q_{ac}=Q_{bd}.               \tag{1}
  \]

Loops and repeated vertices are allowed in (1). Write
`Q_(x,π(x))=1`, and let `J` denote the all-ones matrix.

Every row of `D²` sums to `k²`. Its `v−1=k²−k` positions
outside `Q` have value at most one, and its remaining position
has value at most `k`. All these bounds must be equalities:

\[
                            D²=J+(k-1)Q.                 \tag{2}
\]

The `k` paths from `x` to `π(x)` use every successor of
`x`, so `xDy` implies `yDπ(x)`. Also `D` commutes with
its square and `DJ=JD=kJ`, so (2) gives `DQ=QD`. In
particular `D_(π(x),π(y))=D_xy`.

We claim

\[
                         D_{x,\pi^{-2}(x)}=0
                         \quad\text{for every }x.        \tag{3}
\]

Otherwise `π(x)Dπ⁻¹(x)`. For every choice `b∈Row_D(x)`,
the edge-return implication above gives `bDπ(x)`. Apply (1) to

\[
                         x\to b\to\pi(x)\to\pi^{-1}(x).
\]

The closing pair `Q_(π⁻¹(x),x)` and the pair `Q_(x,π(x))`
are both one. Hence `Q_(b,π⁻¹(x))=1`, forcing
`b=π⁻²(x)`. This cannot hold for `k≥3` distinct successors,
proving (3).

Now put `M=DQ²`. In this permutation convention,
`M_xx=D_(x,π⁻²(x))`, so `M` has zero diagonal. Therefore

\[
              \operatorname{tr}(M²)
              =2\sum_{x<y}M_{xy}M_{yx}
              \quad\text{is even}.
\]

On the other hand, commutation and (2) give

\[
 M²=D²Q⁴=J+(k-1)Q⁵,
 \qquad
 \operatorname{tr}(M²)=v+(k-1)\operatorname{tr}(Q⁵).
\]

Here `v=k²−k+1` is odd and `k−1` is even, making the
trace odd. This contradiction proves the graph lemma.

## 2. Application to the remaining order-forty branch

The [nine-central reduction](1485_order_forty_nine_central_reduction.md)
leaves seventeen tops, seven degree-five vertices `A`, and seven
degree-eight vertices `B`. Each member of `A` has four top neighbors
in each direction. Every member of `B` has one sharp neighbor in
each direction and equal top predecessor/successor counts.

Suppose these seven top counts were all four. Ordinary adjacency
inside `B` would then give a three-regular binary matrix `D` on
seven vertices. The sharp endpoint relation `Q_xy=1`, meaning
`x⇒a⇒y` for some `a∈A`, is a permutation matrix. Two distinct
internal middles force a smaller sharp replacement, giving the second
hypothesis of the graph lemma.

The [one-`A` five-cycle identity](1485_order_forty_thirteen_two_high.md#a-five-walk-with-one-degree-five-vertex)
gives (1): close `aDbDcDd` by the sharp path `d⇒u⇒a`
through `u∈A`. Three two-edge positions touch a sharp edge and
are good. E1485 forbids exactly one of the other two positions
being bad; their badness is precisely `Q_ac=1` and `Q_bd=1`.
This argument includes repeated vertices and loops.

All hypotheses hold with `k=3` and `v=7`, contradicting §1.
Thus the seven degree-eight vertices' top counts **cannot all be four**.

The proof does not force those counts to be uniform. It consequently
does not exclude the entire nine-central case or all models of order
forty. The general lemma also applies to other odd values of `k`
whenever its three explicit graph hypotheses have been established.

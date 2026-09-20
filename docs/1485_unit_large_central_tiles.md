# Unit-or-large central tiles cannot occur at the extremal top count

Research theorem, 20 September 2026. This is an analytic finite E1485
obstruction, independently audited. No enumeration or solver premise
is used, and the theorem is not yet formalized in Lean.

**Theorem.** Let `q≥2`. There is no finite E1485 magma with minimum
translation degree `r=q+1`, exactly `m=q²+1` central elements, and
all central top-block pairs of the forms

\[
(|P_t|,|C_t|)=(1,1)\quad\text{or}\quad(q,q).
\]

Here `P_t=Col(t)∩Z` and `C_t=Row(t)∩Z`. This excludes a family
of central-incidence patterns, not every magma with these values of
`r,m` and not the full spectrum conjecture.

## 1. The large incidence matrices are invertible

Each central row partitions `m=q²+1` labels into `q+1` blocks of
size one or `q`. There must be exactly one unit block and `q` large
blocks. The same holds for each central column. Thus the unit tops
are indexed by central labels `x`, with

\[
P_{u_x}=\{x\},\qquad C_{u_x}=\{\pi(x)\},
\]

for a permutation `π` of `Z`. There are `m` unit tops. The large
tops each occur in `q` central rows, and every central row contains
`q` of them, so there are also exactly `m` large tops.

Let `B',C'` be the central-to-top and top-to-central matrices restricted
to these large tops. The central rectangle partition gives

\[
B'C'=J-Q,
\tag{1}
\]

where `Q` is the permutation matrix of `π`. The matrix `J-Q`
is invertible: multiplying by `Q^{-1}` gives `J-I`, with eigenvalues
`m−1` and `−1`. In particular `B'` is invertible over the rationals.
No assumption that `π` is the identity is needed.

## 2. A first noncentral output must have a unit-heavy profile or one unit

The core is non-full because `m=q²+1<(q+1)²`. Hence there exists
a noncentral product of tops. Choose one of least degree `p`, with
top profiles `U,V` of common size `t`. By the
[first-output theorem](1485_first_top_output_fibers.md), its central-middle
matrix

\[
K_{uv}=|C_u\cap P_v|\quad(u∈U,v∈V)
\]

has positive common row and column sum `e=p-r`, with `e<t`.
The number `p−t` of non-top neighbors is at least one, so

\[
e\ge t-q.
\tag{2}
\]

The `P`-blocks on `U` partition `Z`, and the `C`-blocks on `V`
do likewise. Since each top has equal block sizes in the two directions,
each profile has the same number `k` of large tops and `l` of unit tops:

\[
qk+l=q²+1,\qquad k+l=t.
\tag{3}
\]

Necessarily `0≤k≤q`. If `k=q`, then `l=1`; otherwise `l≥q+1`.

## 3. More than `q` unit tops are impossible

Suppose `1≤k≤q−1`, so `l>q`. A row of `K` indexed by a unit
top in `U` can have ones in at most the `k` large columns of `V`
and one unit column: the singleton `P`-labels of different unit tops
are distinct. Thus `e≤k+1`.

If `e=k+1`, every one of these unit rows must meet every large
column. Their singleton `C`-labels are all distinct, because `π`
is a permutation. Each large `P`-block in `V` would therefore contain
all `l>q` labels, contradicting its size `q`. Hence `e≤k`.
But (2) gives

\[
e\ge t-q=k+l-q>k,
\]

a contradiction. If `k=0`, every column is unit, so `e≤1`, whereas
(2) gives `e≥q²−q+1>1`. This excludes that case too.

## 4. One unit top forces an all-one column

It remains that `k=q`, `l=1`, and `t=q+1=r`. Let `u_x` be
the unit top in `U`. The large `P`-columns in `U` sum to
`1−e_x`. The central column `Col(π(x))` has this same unit top,
and its `q` large `P`-columns have the same sum. Invertibility of
`B'` in (1) therefore forces

\[
U=Col(\pi(x)).
\]

The row of `K` at `u_x` is nonzero since `e>0`. Choose one of
its columns `v`. Then `π(x)∈P_v`. Every top in `U` also has
`π(x)∈C_u`, since `U=Col(π(x))`. This column of `K` has
`t` ones, contradicting its required column sum `e<t`.

All cases are impossible, proving the theorem. The proof places no
upper bound on `p`: it does not assume `p=r+1` or `p≤2r−1`.

## 5. A strict general upper bound on the number of tops

Suppose instead only that `r=q+1`, `m=q²+1`, and every central
block has size at most `q`. Write `h=|T|`, `a_t=q−|P_t|`,
`b_t=q−|C_t|`. The central moments give

\[
\sum a_t=\sum b_t=qh-rm,\qquad
\sum a_tb_t=q²h-2qrm+m².
\]

The inequality `a_tb_t≤(q−1)a_t` implies `h≤2m`.
Equality, and the dual equality, force each pair `(a_t,b_t)` to
be `(0,0)` or `(q−1,q−1)`. Those are exactly the forbidden
large/large and unit/unit tiles. Therefore

\[
\boxed{r²\le |T|\le2\bigl((r-1)²+1\bigr)-1.}
\]

For the lower bound, every vertex has at least
`ceil((q²+1)/q)=q+1=r` top neighbors; a central row's `r`
tops have top-successor counts summing to `h`.

At minimum four with ten central elements this gives `16≤h≤19`,
at every order, under the no-size-four-block hypothesis. The
[separate central-partition argument](1485_order_forty_ten_central_small_blocks.md#3-nineteen-tops-contradict-central-partitions-alone)
also excludes `h=19` without using the total order. At order forty,
the fiber-counting argument on that page further excludes `h=16`.

# Top returns detect irregularity in full-core four-degree models

Research note, 18 September 2026. Assume the finite full-central-core
theorems and exactly four degrees

\[
r,\quad2r,\quad b,\quad2b,
\qquad n=2rb,\quad b>2r.
\]

**Subsequent simplification:** the [general full-core argument](1485_full_core_sharp_regularity.md)
now proves sharp regularity without a four-degree or minimum-degree
restriction. The irregular cases analyzed here are therefore impossible.
The identities and reductions below remain valid, but are no longer
needed to establish regularity under full core.

Write `A,H` for degrees `2r,b`, with sizes `m,h`. Let `k_a` be the
common sharp in-degree and out-degree of `a∈H`. This note proves:

* Top products of two high vertices can occur only at endpoint pairs
  satisfying `k_a+k_d≤r`.
* Exact good-return identities give `PG=r(RQ)^T` and
  `GQ=r(PR)^T`, and detect irregularity vertex by vertex.
* If any high vertex is irregular and `c=min k_a`, then
  `2≤c≤⌊r/2⌋`, `m≤2r(r-c)`, and `b≤r+r²/c-c`.
* Consequently every full-core four-degree model with `r≤5` is
  sharp-regular and has order `8r²`.
* Even with variable sharp degrees, `tr(DK²)=tr(DFK)=0`.
* Regular and irregular high vertices cannot coexist.

These are conditional finite structure statements, not a full spectrum
proof or Lean declarations. In particular, the full-core hypothesis
is known unconditionally when `r=2`, not for arbitrary `r`. They use the
[canonical relation](1485_full_central_core.md), the
[degree gaps](1485_min_two_neighbor_gap.md), and the bad-extension
support count in the [minimum-two four-degree note](1485_four_degree_min_two.md).

The subsequent [component argument](1485_four_degree_component_constraints.md)
extends the minimum-degree bound to `r≤6`, and settles the three
minimum-six necessary candidates left at the end of this note.
The [top-return cycle identities](1485_four_degree_top_cycles.md)
give further exact counts without assuming sharp regularity.

## Notation and exact path counts

The central and top classes each have size `r²`, so

\[
m+h=2r(b-r). \tag{1}
\]

Degree-`2r` vertices have `r` sharp neighbors in each direction.
At a high vertex, reciprocal neighbor balance equates the sharp
in-degree and out-degree, since its non-top neighbors have only degrees
`2r,b`. Thus `1≤k_a≤r` and

\[
\sum_a k_a=mr. \tag{2}
\]

Let `P,Q,D` be adjacency on `A→H`, `H→A`, and `H→H`. Then

\[
P\mathbf1=r\mathbf1,\quad P^T\mathbf1=k,\quad
Q\mathbf1=k,\quad Q^T\mathbf1=r\mathbf1,\quad
D\mathbf1=D^T\mathbf1=(b-r)\mathbf1-k.
\]

Write `C` for the canonical `r`-regular relation and `R` for its
internal part on `H`. Put `ℓ_a=r-k_a`, so both degrees of `R` at
`a` are `ℓ_a`.

Let `K=QP`, and let `E,G` indicate high endpoint pairs whose good
middle is high or top, respectively. These are zero-one matrices with
disjoint supports and

\[
K+E+G=J_h. \tag{3}
\]

The matrices `PD,DQ,PQ,RQ,PR` are also zero-one: every path they
count contains a sharp edge, so is good and has its unique middle.
The nonnegative matrix `F=D²-E` counts bad high two-edge paths.
It is supported on `K`, since a bad high middle must have a
strictly lower-degree replacement, necessarily in `A`.

For an internal edge, the number of bad high extensions is `b-3r`
outside `R`, and `b-2r` on `R`. Indeed its good-extension count is
`2r`, its good top contribution is respectively zero or `r`, and
all sharp extensions into `A` are good. With `F=D²-E`, it follows
that

\[
F\mathbf1=(b-3r)D\mathbf1+r\ell.
\]

Substitution into (3) gives, on writing `g=G1` and `g'=G^T1`,

\[
\boxed{g=(r^2-m)\mathbf1+Dk,\qquad
g'=(r^2-m)\mathbf1+D^Tk.} \tag{4}
\]

## The good-return fiber matching

For any good return `d*a=e`, put

\[
X=L_e^{-1}(a),\qquad Y=R_e^{-1}(d).
\]

For `x∈X`, the weak central law yields
`(x*d)*(d*(e*x))=d`. Since `e*x=a` and `d*a=e`, this means
`(x*d)*e=d`, putting `x*d∈Y`. The dual law gives

\[
((d*a)*x)*(x*d)=x,
\quad\text{hence}\quad a*(x*d)=x.
\]

Therefore `x↦x*d` is an injection from `X` to `Y`, with left inverse
`y↦a*y`. Both fibers have size `n/d(e)`, so it is a bijection. Its matched
edges parametrize precisely the good-good three-edge paths from `a`
to `d`. For the converse, close such a path through `e`; the five-cycle
law makes the whole cycle good, giving the required fiber memberships
and the equation `y=x*d`.

Now suppose `e=t` is top. The canonical-fiber identities give

\[
X=C(a),\qquad Y=C^-(d),\qquad |X|=|Y|=r.
\]

If both endpoints are high, `X,Y` contain respectively `k_a,k_d`
members of `A`. There is no ordinary edge `A→A`, because
`(2r)²<n=2rb`. Matching the low elements in each set therefore uses
disjoint sets of edges, and exactly `r-k_a-k_d` matched edges have
both ends high. In particular

\[
\boxed{G_{da}=1\quad\Longrightarrow\quad k_a+k_d\le r.} \tag{5}
\]

If instead `a∈A` and `d∈H`, all of `X=C(a)` lies in `H`, while
`Y` has exactly `ℓ_d` high members. Thus for such an endpoint pair
whose reverse product `d*a` is top, the number of good-good paths
with both middle vertices high is exactly `ℓ_d`.

## Exact closure identities

The matrix `DQ` is zero-one because its paths contain a sharp edge.
For a pair `(a,d)∈A×H`, its reverse product `d*a` is high exactly
when `(DQ)_{da}=1`; otherwise that product is top. Write
`M=(DQ)^T`, an `m×h` matrix. The preceding top-return matching says
that on the latter pairs

\[
(PE)_{ad}=\ell_d,\qquad (PK)_{ad}=k_d. \tag{6}
\]

Indeed these count respectively the matched `H→H` and `H→A`
edges; the first edge from `a∈A` is automatically sharp.

Next suppose the return `e=d*a` is high. Then `e⇒a` is sharp,
so `X=L_e^{-1}(a)=Row(a)` consists of `r` top and `r` high
vertices. The fiber `Y=R_e^{-1}(d)` contains all `k_d` sharp
`A` predecessors of `d`. It contains `r` top vertices if `d R e`,
and none otherwise, by the uniform top fibers of the canonical
relation. No central vertex can belong to either fiber.

The `r` top members of `X` map injectively into `C^-(d)` under
`x↦x*d`. As the latter set also has size `r`, they exhaust it,
including every `A` member of `Y`. Thus no high member of `X`
can match an `A` member of `Y`, proving `(PK)_{ad}=0`. If
`d R e`, the remaining `r` members of `Y` are top, so
`(PE)_{ad}=0`. Otherwise the remaining `r` members are high,
so `(PE)_{ad}=r`.

Combining the cases, with all all-one matrices of the required size,

\[
\boxed{
\begin{aligned}
PK&=(J-M)\operatorname{diag}(k),\\
PE&=r\bigl((D-R)Q\bigr)^T+(J-M)\operatorname{diag}(\ell)\\
  &=M\operatorname{diag}(k)-r(RQ)^T+J\operatorname{diag}(\ell).
\end{aligned}} \tag{7}
\]

Since `P(K+E+G)=PJ=rJ`, adding the two identities gives

\[
\boxed{PG=r(RQ)^T,\qquad GQ=r(PR)^T.} \tag{8}
\]

The second identity is the column-dual of the first. Summing (8)
over the `A` index gives the vector identities

\[
\boxed{G^Tk=rRk,\qquad Gk=rR^Tk.} \tag{9}
\]

Put `V=Σ_a k_aℓ_a`. Since `R` has row and column sums `ℓ`,
equation (9) yields the exact weighted counts

\[
\boxed{k^Tg=k^Tg'=rV.} \tag{10}
\]

These replace the weaker elementary bounds obtained by using only
`PE≤rJ` at high-return pairs. Combining (10) with (5) gives

\[
2rV=k^Tg+k^Tg'
=\sum_{G_{da}=1}(k_a+k_d)\le r|G|,
\]

and therefore

\[
\boxed{|G|\ge2\sum_a k_a(r-k_a).} \tag{11}
\]

In particular `G=0` if and only if every `k_a=r`; the reverse
implication also follows immediately from (9) and positivity of `k`.

## A size bound on the lower middle class

Put `x=h-m≥0`. Equation (2) gives `Σℓ_a=rx`. Summing (4) and
using (1) yields

\[
\boxed{|G|=\frac{4r^2-m}{2}\,x-\sum_a\ell_a^2.} \tag{12}
\]

For explicit algebra, the summed row formula is
`|G|=(r²-m)h+(b-r)mr-Σk²`; substitute
`r(b-r)=(m+h)/2` and
`Σk²=r²h-2r²x+Σℓ²` to obtain (12).

Also `V=rΣℓ_a-Σℓ_a²=r²x-Σℓ_a²`. Subtracting twice this
quantity from (12), inequality (11) becomes

\[
0\le |G|-2V=\sum_a\ell_a^2-\frac{m}{2}x. \tag{13}
\]

If any high vertex is irregular, then `Σℓ>0`, so `x>0`. Therefore
on putting `c=min_a k_a`, the bound
`Σℓ²≤(r-c)Σℓ=r(r-c)x` gives

\[
\boxed{m\le2r(r-c).} \tag{14}
\]

On the other hand `mr=Σk≥ch`, and `m+h=2r(b-r)`, so

\[
m\ge\frac{2rc(b-r)}{r+c}.
\]

Combining with (14) and dividing by positive factors gives

\[
\boxed{\text{irregularity}\quad\Longrightarrow\quad
b\le r+\frac{r^2}{c}-c.} \tag{15}
\]

The degree-gap theorem gives `b≥3r`, and degree-`3r` vertices are
sharp-regular. Hence irregularity requires `b>3r`. An irregular
vertex `a` has an outgoing `R` edge, whose `b-2r` bad high
extensions all have endpoints in the `rk_a`-element set of good
`A` replacements from `a`. Thus `b-2r≤rk_a`. In particular
`k_a=1` would imply `b≤3r`, a contradiction. Regular vertices
have `k_a=r`, so `c≥2`. Finally `G≠0` and (5) give

\[
\boxed{2\le c\le\lfloor r/2\rfloor.} \tag{16}
\]

For `r≤3`, (16) is impossible. For `r=4`, only `c=2` remains,
and (15) gives `b≤10<12`. For `r=5`, again `c=2`, and (15)
gives `b≤15.5`, hence `b≤15` because degrees are integers.
Both contradict `b>3r`. Therefore

\[
\boxed{\text{full central core, exactly four degrees, }r\le5
\quad\Longrightarrow\quad k_a=r\text{ for all }a\in H.}
\tag{17}
\]

The [sharp-regular four-degree theorem](1485_four_degree_regular_gap.md)
then gives `b=4r` and `n=8r²`. This is not an unconditional
classification for arbitrary minimum degree: full central core remains
an explicit assumption.

## An unconditional trace cancellation within the four-degree setup

Multiplying the first identity in (7) on the left by `Q` gives

\[
\boxed{K^2=kk^T-QQ^TD^T\operatorname{diag}(k).} \tag{18}
\]

After multiplication by `D`, the two traces cancel. Indeed
`DQ` is zero-one, so

\[
\begin{aligned}
\operatorname{tr}(Dkk^T)&=k^TDk,\\
\operatorname{tr}(DQQ^TD^T\operatorname{diag}(k))
 &=\sum_a k_a\sum_{z\in A}(DQ)_{az}^2
 =\sum_a k_a(Dk)_a=k^TDk.
\end{aligned}
\]

Therefore

\[
\boxed{\operatorname{tr}(DK^2)=0.} \tag{19}
\]

For comparison, the second identity in (7) produces the apparently
longer expression

\[
K^2=kk^T-QQ^TD^T\operatorname{diag}(k)
       +rQQ^TR^T-KG.
\]

The last two matrices cancel already before taking traces, because
`KG=Q(PG)=rQQ^TR^T` by (8). One may also check their traces
directly: `RQ≤DQ` is zero-one, so
`tr(DQQ^TR^T)=⟨DQ,RQ⟩=|RQ|=V`. If `G_{da}=1`, the
top-return matching gives `(DK)_{ad}=k_d`: these paths match the
`k_d` members of `Y∩A` to high members of `X`, since there are
no `A→A` edges. Thus

\[
\operatorname{tr}(DKG)=\sum_{G_{da}=1}k_d=k^Tg=rV. \tag{20}
\]

No constancy of `k` was used. Since `F` is nonnegative and supported
on the zero-one matrix `K`, there is a finite constant `L` with
`F≤LK`. Nonnegativity then gives

\[
\boxed{0\le\operatorname{tr}(DFK)
\le L\operatorname{tr}(DK^2)=0.} \tag{21}
\]

The cyclic interpretation of the last trace is that no bad-bad
three-edge high path has a good `A` return. In fact, when its last
two-edge path is bad and its return middle lies in `A`, the two
sharp closure edges force its first two-edge path to have the same
status.

One useful consequence, stated without needing a cycle count, is

\[
\boxed{PDQ=r\bigl(J_m-(PQ)^T\bigr).} \tag{22}
\]

To verify it, cyclically rewrite (19) as
`tr((PDQ)(PQ))=0`. Thus the nonnegative matrix `PDQ` is supported
off `(PQ)^T`; each entry is at most `r`, because `PD` is zero-one
and `Q` has column sum `r`. From (4) and (10),

\[
|PDQ|=k^TDk=r\left(m^2-\sum_a k_a^2\right).
\]

The zero-one matrix `PQ` has exactly `Σk_a²` entries equal to
one. The total of `PDQ` therefore saturates the entrywise bound,
which proves (22).

## Sharp regularity is constant on the sharp bipartite blocks

Because `k` is strictly positive and `R` has row and column sums
`ℓ`, (9) shows pointwise that

\[
g_a=0\quad\Longleftrightarrow\quad g'_a=0
\quad\Longleftrightarrow\quad \ell_a=0. \tag{23}
\]

For a fixed `a∈A`, (8) says that summing the `r` rows of `G`
selected by `P_{a*}` yields only the values zero and `r`.
Consequently those rows of `G` are identical. Dually the `r`
columns selected by `Q_{*a}` are identical. By (23), each sharp
successor set of an `A` vertex consists either entirely of regular
high vertices or entirely of irregular high vertices; the same holds
for each sharp predecessor set.

The two choices agree. If all sharp predecessors of `a` are regular,
then the `a` column of `RQ` is zero, since `R` has no edge incident
with a regular high vertex. Equation (8) gives `(PG)_{a*}=0`,
forcing all sharp successors of `a` to be regular. The converse is
dual. Hence, after partitioning `A` by this common type and `H` by
sharp regularity, both `P` and `Q`, and therefore `K`, are block
diagonal. This does not assert that `D` is block diagonal, or that
all irregular sharp degrees are equal.

The same zero-one saturation in (8) gives useful entrywise forms:

\[
\boxed{RK=G^T\operatorname{diag}(k),\qquad
KR=\operatorname{diag}(k)G^T.} \tag{24}
\]

For example, `(RQ)_{da}=1` precisely when every high sharp
successor `u` of `a` has `G_{ud}=1`. For fixed `u,d`, therefore,
either all `k_u` sharp predecessors of `u` contribute to
`(RQP)_{du}`, or none do; these cases correspond to `G_{ud}=1`
or zero. This proves the first identity; the second is dual.

## Regular and irregular high vertices cannot coexist

Suppose both types occur. Split `A=A₀⊔A₁`, `H=H₀⊔H₁`
according to the preceding section, where the zero block is regular.
Write `m_i=|A_i|`, `h_i=|H_i|`, and `D_{ij}` for the corresponding
blocks of `D`. The matrices `P,Q` have matching diagonal blocks
`P_i,Q_i`. All rows and columns of `P₀,Q₀` sum to `r`, so
`h₀=m₀>0`.

The off-diagonal block of (22) is

\[
P_0D_{01}Q_1=rJ_{m_0,m_1}. \tag{25}
\]

The matrices `P₀D₀₁` and `D₀₁Q₁` are zero-one, as submatrices
of `PD,DQ`. Each column of `Q₁` and each row of `P₀` has `r`
ones. Every row of `Q₁` and every column of `P₀` has a positive
sum. Thus equality in (25) forces

\[
P_0D_{01}=J_{m_0,h_1},\qquad
D_{01}Q_1=J_{h_0,m_1}. \tag{26}
\]

For the first assertion, each `Q₁` column selects `r` entries of
a row of `P₀D₀₁`, all of which must be one; every index occurs in
some such column. The second assertion is the same argument with
rows of `P₀`.

Consequently `D₀₁k₁=m₁1`. On `H₀`, equation (4) and `g=0`
give

\[
rD_{00}\mathbf1+m_1\mathbf1
=(m_0+m_1-r^2)\mathbf1,
\]

so every row of `D₀₀` has sum `m₀/r-r`. The total internal high
degree at a regular high vertex is `b-2r`. Therefore every row of
`D₀₁` has sum `b-r-m₀/r`, and

\[
|D_{01}|=m_0\left(b-r-\frac{m_0}{r}\right).
\]

Summing `P₀D₀₁=J` over entries and using the column sums `r`
of `P₀` also gives `r|D₀₁|=m₀h₁`. Since `m₀>0`, these imply
`h₁=r(b-r)-m₀`. But (1) says
`m₁+h₁=2r(b-r)-2m₀`, whence `m₁=h₁`. This contradicts
`rm₁=Σ_{H₁}k_a<rh₁`.

Thus either every high vertex is regular or every high vertex is
irregular. In the latter case every row and column of `G` is
nonzero. By (5), with `c=min k_a`, each high vertex then satisfies

\[
\boxed{c\le k_a\le r-c.} \tag{27}
\]

These statements do not yet exclude an all-irregular block with
nonconstant sharp degrees when `r≥6`.

## An irregular high class cannot have constant sharp degree

Suppose every `k_a=c<r`. Then `D` has constant degree
`b-r-c`, and (4) makes `g` constant. Equation (10), with
`V=hc(r-c)`, gives `g_a=r(r-c)`. Meanwhile (1)--(2) give

\[
h=\frac{2r^2(b-r)}{r+c},\qquad
m=\frac{2rc(b-r)}{r+c}.
\]

Substituting these into (4) yields

\[
g_a=r^2-m+c(b-r-c)
=(r-c)\left(r+c-\frac{c(b-r)}{r+c}\right).
\]

Equating the two expressions and dividing by `r-c>0` forces
`b=2r+c<3r`, contrary to the degree gap. Hence

\[
\boxed{\text{constant high sharp degree}\quad\Longrightarrow\quad
k_a=r\text{ for every }a\in H.} \tag{28}
\]

For instance, if `r=6`, an irregular case has `c=2`: `c=3`
would give `b≤15` from (15), contradicting `b>18`. Thus (15)
leaves `19≤b≤22`. At `b=22`, the lower and upper bounds on
`m` both equal `48`; then `h=144` and `Σk=288=2h`, so every
`k_a=2`, contradicting (28). The still-unexcluded irregular
values at minimum degree six are therefore `b∈{19,20,21}`;
this list is a necessary-condition reduction, not an existence claim.

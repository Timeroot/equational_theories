# Nine central elements and sixteen tops: sharper degree counts

Research note, 20 September 2026. These are independently audited
analytic necessary conditions, not Lean theorems. The final reduction in §12 is
`(a,b,a3)=(7,8,2)`, with six triple blocks on each side, four
degree-eight vertices having three top neighbors, and four having five.
Here `a3` counts degree-five vertices having a three-element profile.
Section 13 locates the exceptional sharp degree. The subsequent
[sixteen-top exclusion](1485_nine_central_sixteen_exclusion.md) finishes
the branch using two explicit, independently audited finite graph lemmas.
Assume an order-forty E1485 magma has minimum degree four, nine
central elements, and sixteen tops. Write `A,B` for its degree-five
and degree-eight classes, with `a=|A|`, `b=|B|`, so `a+b=15`.

The [variable-top-count bound](1485_order_forty_variable_top_counts.md#2-three-top-neighbors-suffice-for-a-useful-bound)
forces at least one member of `A` to have a three-element top
profile. Apply the
[three-profile complement tilings](1485_nine_central_three_profile.md)
and use their notation `N_ij`, `p=#P-triples`, `q=#C-triples`.
All blocks have size at most three and `p,q≤6`.

## 1. Every vertex has three through five top neighbors

Let `n_i` count global `P`-blocks of size `i`. Since
`n1+n2+n3=16` and `n1+2n2+3n3=36`,

\[
n_1=p-4\le2.
\]

The top predecessors of any vertex have `P`-blocks partitioning
nine central labels. If there are `I` such blocks, at most two
are singletons and all others have size at least two. Hence
`9≥2I−2`, so `I≤5`. Block size at most three gives `I≥3`.
The dual argument proves the same bounds for the top-successor count.

At every `x∈B`, reciprocal-neighbor balance gives
`O_x−I_x=3(j_x^+−j_x^-)`, where `j_x^±` count sharp neighbors
in `A`. Since `I_x,O_x∈{3,4,5}`, both sides must vanish:

\[
\boxed{I_x=O_x=:t_x,\quad j_x^+=j_x^-=:j_x,\quad
3\le t_x\le5.}
\tag{1}
\]

Thus its internal `B` degree is balanced as well, equal to `8−t_x−j_x`.
Also the sum of top-successor counts over the tops themselves is
at most 68: if this sum is `S`, the central row equations give

\[
3S-144=\sum_{u\in T}(3-|P_u|)O_u
\le5\sum_{u\in T}(3-|P_u|)=60.
\tag{2}
\]

## 2. Exact sharp-neighbor top counts at every three-profile vertex

Let `a0∈A` have a three-element top profile. It has exactly two
sharp predecessors in `B`, say `b1,b2`. In the complement tilings,
the disjoint sets `X_i={t∈T:t*a0=u_i}` consist of tops whose
`P`-blocks have size one or two and total weight eighteen. Thus

\[
|X|=9+\tfrac12\#\{t\in X:|P_t|=1\}.
\]

If `p=4` or `5`, there are at most one global singleton, and the
displayed singleton count is even; it is therefore zero and `|X|=9`.
If `p=6`, saturation in the complement-tiling theorem says that `X`
contains all small-`P` tops. Both global singletons belong to `X`,
so `|X|=10`.

The sixteen top inputs of `R_(a0)` split between its three top
outputs, counted by `X`, and its two sharp `B` outputs. At a
sharp output `b_i`, the full fiber is `Col(b_i)`, so its number
of top inputs is `t_(b_i)`. Consequently

\[
\boxed{\{t_{b_1},t_{b_2}\}=
\begin{cases}
\{3,4\},&p=4\text{ or }5,\\
\{3,3\},&p=6.
\end{cases}}
\tag{3}
\]

The dual sharp-successor statement uses `q` instead of `p`.
In particular a `B` vertex adjacent sharply to any three-profile
member of `A` cannot have five top neighbors.

Let `a3` count the three-profile members of `A`, and let `e_x^+`
and `e_x^-` count the sharp three-profile successors and predecessors
of `x∈B`. Summing (3) gives the exact identities

\[
\sum_B e_x^+t_x=(7-\mathbf1_{p=6})a_3,
\qquad
\sum_B e_x^-t_x=(7-\mathbf1_{q=6})a_3.
\tag{4}
\]

## 3. Top-input packing improves the auxiliary capacity bound

For a top `u`, let `Aout(u)` count its ordinary successors in `A`,
and `A3out(u)` those with a three-element profile. Count top inputs
of `L_u`. Each central output contributes four; each four-profile
`A` output contributes three; each three-profile output contributes
two. Therefore

\[
\boxed{4|C_u|+3Aout(u)-A3out(u)\le16.}
\tag{5}
\]

Every top predecessor of a three-profile `A` vertex has a triple
`P`-block. In particular `A3out(u)=0` if `|P_u|<3`.

An ordinary top-to-`A` edge has auxiliary support equal to all
central labels except the `C`-block of its unique excluded top
input. Its support has size at least six. Four-regularity of the
auxiliary relation gives

\[
Aout(u)\le\left\lfloor\frac{9(4-|C_u|)}6\right\rfloor
=\begin{cases}4,&|C_u|=1,\\3,&|C_u|=2,\\1,&|C_u|=3.
\end{cases}
\]

Equation (5) sharpens the middle case:

\[
\boxed{|C_u|=2,\ |P_u|<3\quad\Longrightarrow\quad Aout(u)\le2.}
\tag{6}
\]

The dual statements hold for predecessors. These are local statements;
no assumption of uniform auxiliary relations is used.

## 4. There are at most eight degree-five elements

Set

\[
D=N_{11}+N_{12}+2N_{21}+2N_{22}+3N_{31},
\quad
D'=N_{11}+N_{21}+2N_{12}+2N_{22}+3N_{13}.
\]

The central rows count every element of `A` once. Weighting the
capacity bounds above by `|P_u|`, the two central moments give

\[
9a=\sum_T |P_u|Aout(u)\le90-D,
\qquad 9a\le90-D'.
\tag{7}
\]

For example, if `X,Y,Z` are the total `P` weights of the tops
whose `C` sizes are respectively one, two, three, then
`X+Y+Z=36`, `X+2Y+3Z=81`. The unsharpened bound is
`4X+3Y+Z=90−X`; subtracting `N12+2N22` from (6) gives (7).

The [singleton-coverage inequalities](1485_nine_central_three_profile.md#6-singleton-coverage-excludes-another-seventeen-top-table)
imply `D,D'≥9`. To see the algebra explicitly, write
`x=N11`, `y=N12`, `z=N21`. The defect moments give

\[
N_{22}=9-4x-2y-2z,\quad
N_{23}=3+2x+z-2N_{13},\quad
N_{32}=3+2x+y-2N_{31}.
\]

Substitution in singleton coverage gives exactly `D≥9,D'≥9`.
Thus `a≤9`. If `a=9`, both are equalities, which force

\[
3N_{31}=7x+3y+2z-9,\qquad
3N_{13}=7x+2y+3z-9.
\tag{8}
\]

In particular `x≡y≡z (mod 3)` and `4x+2y+2z≤9`.
If `x=0`, the only possibilities for `(y,z)` are `(0,0),(3,0),(0,3)`,
and (8) makes a count negative in each. If `x=2`, the congruences
force `y,z≥2`, contradicting the inequality. Values `x≥3` are
already impossible. Thus `x=y=z=1`.
The central moments then reconstruct the unique table

\[
\begin{pmatrix}1&1&1\\1&1&4\\1&4&2\end{pmatrix},
\]

which has seven triples on either side, contrary to `p,q≤6`.
Therefore

\[
\boxed{a\le8.}
\]

## 5. At most three three-profile vertices, and at least seven elements of `A`

Split `A=A3⊔A4` according to top-profile size, and write their
cardinalities as `a3,a4`. Each `A3` element has six good ordered
top pairs, all in the `p` by `q` rectangle with `P`-triple first
inputs and `C`-triple second inputs.

Every central column has a `P`-triple among its four blocks, and
every central row has a `C`-triple, since their block sizes are
`3321` or `3222`. For a central label `z`, let `k_z` count
`P`-triple tops whose `C`-blocks contain it, and let `l_z` count
`C`-triple tops whose `P`-blocks contain it. Both are positive.
Central-middle uniqueness shows that the number of centrally valued
pairs in the rectangle is exactly `Σ_z k_z l_z`, hence at least

\[
\sum_z(k_z+l_z-1)=9+W_P+W_C,
\]

where `W_P=Σ_(|P|=1)|C|` and `W_C=Σ_(|C|=1)|P|`.
Here we used the pointwise identity that the number of triples
in a four-block central partition is one plus its singleton count.
This is the central-coverage capacity argument of the
[class-capacity note](1485_nine_central_class_capacities.md).

There are `p−4` singleton `P`-blocks and `q−4` singleton `C`-blocks.
If `u=N11`, then

\[
W_P\ge2(p-4)-u,\quad W_C\ge2(q-4)-u,
\quad u\le\min(p-4,q-4).
\]

Consequently the number of central pairs is at least
`1+2 max(p,q)`. Disjointness of the product fibers proves

\[
\boxed{6a_3\le pq-2\max(p,q)-1.}
\tag{9}
\]

Its largest right side for `4≤p,q≤6` is 23. Therefore `a3≤3`.
Moreover, `a3=3` requires `p=q=6`: if one count is at most five,
the right side is at most seventeen.

Sharp-neighbor existence covers `B` by the `2a3+a4=a+a3`
sharp successors of the elements of `A`. Thus
`15=a+b≤2a+a3≤2a+3`, giving `a≥6`.
Suppose `a=6`. Then `b=9`, `a3=3`, and each `B` vertex has
sharp count one, because `Σ_B j_x=a+a3=9`.

Put `U=Σ_B(t_x−3)`. Counting all 160 edges ending in the top
class, and writing `S=Σ_(u∈T)O_u`, gives the exact identity

\[
S=160-36-(4a-a_3)-(3b+U)
 =79-a+a_3-U.
\tag{10}
\]

Thus `a=6,a3=3` and (2) imply `76−U≤68`, or `U≥8`.
But (9) forces `p=q=6`. The six sharp predecessor incidences
from `B` to the three members of `A3` hit six distinct `B` vertices,
since each has sharp count one. By (3), all six have three top
neighbors. The other three have at most five, so `U≤6`, a
contradiction.

Combining with §4, the analytic reduction is therefore

\[
\boxed{(a,b)\in\{(7,8),(8,7)\},\qquad 1\le a_3\le3.}
\]

## 6. There cannot be just one three-profile vertex

Suppose `a3=1`. Write `u_x=t_x−3∈{0,1,2}`, `U=Σu_x`,
and `d_x=j_x−1≥0` for `x∈B`. The unique `A3` element has
two distinct sharp predecessors in `B`; call this two-element set
`M` and put `v=Σ_(x∈M)u_x`. Its indicator is exactly `e_x^+`.

The globally summed bad-path bound of the
[class-capacity note, §3](1485_nine_central_class_capacities.md#3-a-global-bad-path-count-without-edgewise-balance)
can be written

\[
\sum_B g_x\ge10b-5\sum_B j_x
+\sum_B\bigl[u_x^2+u_xd_x+d_x(d_x-1)\bigr]
-\sum_{x\in M}(4-u_x-d_x).
\tag{11}
\]

This is only a global bound: no individual summand has been
clipped at zero and no edgewise bad-path balance is assumed.

If `a=7,b=8`, then `Σj=a+a3=8`, so all `j=1`.
Equation (11) gives `Σg_x≥32+Σu_x²+v`.
The central and degree-five outputs leave only
`256−144−6−6·12=34` top pairs for `B` and `T`, so
`Σu_x²+v≤2`. But (10) gives `S=73−U≤68`, or `U≥5`,
contradicting `Σu_x²≥U`.

If `a=8,b=7`, then `Σd=2`. The top-pair budget now leaves
`256−144−6−7·12=22` pairs. Thus (11) implies

\[
F:=\sum_B\bigl[u_x^2+u_xd_x+d_x(d_x-1)\bigr]
+v+\sum_{x\in M}d_x\le5.
\tag{12}
\]

Equation (10) gives `S=72−U≤68`, hence `U≥4`.
If `U≥5`, all terms in (12) are nonnegative and `Σu²≥U`,
so equality forces `U=5`, five of the seven `u` values equal
to one, and two equal to zero. The other terms must all vanish.
Since `Σd=2` and `Σd(d−1)=0`, exactly two vertices have `d=1`.
They have `u=0` by `Σud=0`, and lie outside `M` by
`Σ_Md=0`. Both members of `M` also have `u=0` because `v=0`.
This requires four distinct zero values, not two. Consequently
`U=4` and `S=68`.

Equality in (2) now forces `O_u=5` whenever `|P_u|<3`.
Dually `I_u=5` whenever `|C_u|<3`.
We claim that every top with `|C_u|=2` has `Aout(u)≤2`.
For `|P_u|<3` this is (6). Otherwise `|P_u|=3`, `I_u=5`,
and reciprocal balance gives

\[
O_u-5=-5+3(Aout(u)-Ain(u)).
\]

Since `3≤O_u≤5`, its only possible value is `O_u=3`, and
`Aout−Ain=1`. The dual auxiliary capacity gives `Ain≤1`
when `|P_u|=3`, proving the claim.

Let `q` be the global number of `C`-triples. The numbers of
singletons and pairs are `q−4` and `20−2q`. The total ordinary
top-to-`A` edge count is therefore at most

\[
4(q-4)+2(20-2q)+q=24+q\le30.
\]

But that count is exactly `4a−a3=31`, a contradiction.
Thus `a3=1` is excluded in both class splits. The strengthened
analytic reduction is

\[
\boxed{(a,b)\in\{(7,8),(8,7)\},\qquad a_3\in\{2,3\}.}
\]

## 7. Three-profile count three cannot accompany eight elements of `A`

Suppose `a3=3`. By (9), `p=q=6`. Every sharp `B` predecessor
or successor of an `A3` vertex then has three top neighbors.
Let `B0` be the set of all such degree-eight vertices with `t_x=3`.
Each `A3` vertex has two sharp predecessors and two sharp successors,
giving four ordered pairs with that product in `B0×B0`. These
twelve pairs are distinct, so `|B0|≥4`.

As before put `U=Σ_B(t_x−3)`. Equation (10) and (2) imply
`U≥14−a`, while the four members of `B0` give
`U≤2(b−4)`. Thus `a=8,b=7` would force `U=6` and `S=68`.
We show that `p=q=6,S=68` is impossible independently of `a`.

Equality in (2) forces `O=5` at tops with `P` size below three,
and dually `I=5` at tops with `C` size below three. Harmonic
balance modulo three therefore forbids types `(1,2),(2,1)`.
The singleton marginals are both two. Setting `x=N11`, the
remaining central moments give

\[
N_{13}=N_{31}=2-x,\quad N_{22}=9-4x,\quad
N_{23}=N_{32}=4x-1,\quad N_{33}=5-3x.
\]

Nonnegativity forces `x=1`, and the unique table is

\[
\begin{pmatrix}1&0&1\\0&5&3\\1&3&2\end{pmatrix}.
\]

The successor count `O` is five at the `(1,1),(1,3),(2,2),(2,3)`
tops. At the `(3,1)` top it is four, and at each `(3,2)` top
it is three, by harmonic balance modulo three and `3≤O≤5`.
The two `(3,3)` tops each have at least three successors in `T`.
Consequently

\[
S\ge5+5+5\cdot5+3\cdot5+4+3\cdot3+2\cdot3=69,
\]

contrary to `S=68`. This excludes `a=8,a3=3`.

If `a=7,a3=3`, the bounds instead give `7≤U≤8`.
The case `U=7` would again give `S=68`, so `U=8,S=67`.
Exactly four members of `B` have three top neighbors and four
have five. The latter four have no sharp `A3` neighbors and use
all four sharp incidences from `A4`, so their sharp counts are one.
The former four have only sharp `A3` neighbors. Their sharp counts
sum to six and each is at most two, because their `2j_x` distinct
sharp two-step successors lie among only four vertices.
Their sharp-count multiset is therefore `(2,2,1,1)`.

In particular the remaining class/profile possibilities are

\[
\boxed{(a,b,a_3)\in\{(7,8,2),(7,8,3),(8,7,2)\}.}
\]

These arguments do not eliminate all the remaining central tables.
Exploratory integer optimizations are deliberately not used as
infeasibility certificates in this note.

## 8. A local capacity inequality excludes three smaller profiles

Suppose `a3=3`. The preceding section forces `a=7,b=8`,
`p=q=6`, and `S=67`. We now exclude this last three-profile case
by an explicit inequality, checked below in nine central block types.
The inequality was discovered using linear optimization; the following
proof does not use an optimizer's status or numerical output as a premise.

At a top write `i=|P|`, `j=|C|`, `α=Aout`, `β=Ain`, and
`d=5−O`, `e=5−I`. Thus `d,e∈{0,1,2}`, and reciprocal balance is

\[
e-d=5(j-i)+3(\alpha-\beta).
\tag{13}
\]

The established auxiliary-capacity bounds give `α≤4,3,1` for
`j=1,2,3`, and the dual bounds hold for `β` using `i`.
There is also a lower bound `α≥2` when `j=1`: a central row
containing this top has pattern `3321`, whose other three tops
have total capacity at most `1+1+3=5`, whereas the required sum
is `a=7`. Dually `β≥2` when `i=1`.

Define constants

\[
(R_1,R_2,R_3)=(-6,46,134),\qquad
(C_1,C_2,C_3)=(0,26,58).
\]

Here the letters `C_j` are numerical coefficients, not central blocks.
We claim the pointwise inequality

\[
\boxed{18(i-2)\alpha\le
R_i+C_j-18ij+(28-12i)d+(11-3j)e.}
\tag{14}
\]

Let `H` be the right side minus the left side. Its nine expressions
are as follows; the last uses `d=e`, forced by (13) when `i=j=3`.

| `(i,j)` | `H` |
| --- | --- |
| `(1,1)` | `18α+16d+8e−24` |
| `(1,2)` | `18α+16d+5e−16` |
| `(1,3)` | `18α+16d+2e−2` |
| `(2,1)` | `10+4d+8e` |
| `(2,2)` | `4d+5e` |
| `(2,3)` | `−4+4d+2e` |
| `(3,1)` | `80−8d+8e−18α` |
| `(3,2)` | `52−8d+5e−18α` |
| `(3,3)` | `30−6d−18α` |

For `(1,1)`, use `α≥2`; the two cases `(2,1),(2,2)` are
immediate. In `(1,2)`, (13) permits `(d,e)=(1,0),(2,1),(0,2)`.
The first two make `H≥0` directly; the last gives `β=α+1`,
so `β≥2` implies `α≥1` and again `H≥0`.
For `(1,3)`, the possible pairs are `(0,1),(1,2),(2,0)`;
already `16d+2e−2≥0`. For `(2,3)`, they are
`(0,2),(1,0),(2,1)`, and `−4+4d+2e≥0` in each.

For `(3,1)`, use `α≤4` and `e−d∈{−1,2}` to get
`H≥8(1+e−d)≥0`. For `(3,2)`, (13) permits `(d,e)=(2,0)`
with `α=β+1≤2`, or `(0,1),(1,2)` with `α=β+2≤3`.
Substitution gives lower bounds zero, three, zero, respectively.
Finally `(3,3)` follows from `d≤2` and `α≤1`.
This proves (14) in every case by integer arithmetic alone.

Sum (14) over the sixteen tops. There are two singleton, eight
double, and six triple blocks in each direction. Consequently

\[
\sum R_i=1160,\quad \sum C_j=556,\quad \sum ij=81.
\]

Since `S=67`, `Σd=Σe=13`. The weighted central row/column
equations give `Σ iO=Σ jI=144`; hence
`Σ id=Σ je=5·36−144=36`. The summed right side is therefore

\[
1160+556-18\cdot81+28\cdot13-12\cdot36
       +11\cdot13-3\cdot36=225.
\]

On the other hand, `Σα=4a−a3=25`, and central-row counting gives
`Σ iα=9a=63`. The summed left side is

\[
18(63-2\cdot25)=234>225,
\]

a contradiction. Thus `a3=3` is impossible. The resulting analytic
frontier is

\[
\boxed{(a,b,a_3)=(7,8,2)\quad\text{or}\quad(8,7,2).}
\]

## 9. Five triples on both sides are impossible

Continue with `a3=2`. Write `γ_u=A3out(u)`. These counts vanish
unless `|P_u|=3`, and their sum is six. Among the `q` tops `v`
with `|C_v|=3`, at least `|C_u|` give a central product `u*v`:
their `P_v` blocks cover `Z`, and each meets `C_u` at most once.
Each of the `γ_u` distinct degree-five outputs uses two further,
distinct targets from this same family. Therefore

\[
                   2\gamma_u\le q-|C_u|.                \tag{15}
\]

Suppose `p=q=5`. Equation (15) bounds `γ≤1` at every top with
`|C|≥2`. Since five `P`-triple tops must carry total `γ=6`, some
top has `γ≥2` and hence type `(3,1)`. There is only one singleton
block on each side, so `N31=1`. Dually `N13=1`. These two tops
use both singleton margins, forcing `N11=N12=N21=0`. The central
moments now determine the table

\[
                    \begin{pmatrix}
                    0&0&1\\0&9&1\\1&1&3
                    \end{pmatrix}.
\]

In the notation of the
[central-coverage bound](1485_nine_central_class_capacities.md#1-a-sharper-total-bound-on-three-neighbor-vertices),
this table has `L=R=12`. It gives the contradiction
`12=6a3≤pq−L−R+9=10`. Consequently

\[
                    \boxed{(p,q)\in\{(5,6),(6,5),(6,6)\}.}
\tag{16}
\]

This is an analytic exclusion; no enumeration of central incidence
structures is used.

## 10. Two symmetric local inequalities bound the remaining top counts

Keep `i,j,α,β,d,e` from §8. In addition to the bounds already
used there, `(i,j)=(2,2)` has `α,β≤2`, by (6). For `a=7`,
the singleton lower bounds are `α≥2` when `j=1`, and `β≥2`
when `i=1`. Let `(r1,r2,r3)=(33,−118,−319)`. Then

\[
\begin{split}
H_7={}&(55-22i)d+(55-22j)e\\
 &+(63-32i)\alpha+(63-32j)\beta-r_i-r_j-58ij\ \ge0.
\end{split}                                               \tag{17}
\]

The expression and hypotheses are symmetric under
`(i,α,d)↔(j,β,e)`, so six types suffice. Their expressions are

| Type | `H7` |
| --- | --- |
| `11` | `33(d+e)+31(α+β)−124` |
| `12` | `33d+11e+31α−β−31` |
| `13` | `33d−11e+31α−33β+112` |
| `22` | `11(d+e)−α−β+4` |
| `23` | `11(d−e)−α−33β+89` |
| `33` | `116−11(d+e)−33(α+β)` |

Types `11,22,33` follow directly from the bounds above. For `12`,
reciprocal balance (13) gives either `e=d−1, β=α+2`, when the
expression is `44e+30α`, or `e=d+2, β=α+1`. The latter forces
`d=0,e=2,α≥1`, giving `30α−10≥0`.
For `13`, either `e=d+1, β=α+3`, giving `22d+2−2α≥0`, or
`d=2,e=0,β=α+4`, giving `46−2α≥0`.
For `23`, the alternatives are `e=d+2,β=α+1` and
`e=d−1,β=α+2`; both expressions equal `34−34α≥0`.
This proves (17) by elementary integer arithmetic.

Summing (17), use `Σd=Σe=80−S`, `Σid=Σje=36`,
`Σα=Σβ=4a−2`, and `Σiα=Σjβ=9a`. The `P` margins give
`Σr_i=−2492−50p`, and the dual margins give
`Σr_j=−2492−50q`. Thus

\[
       110(80-S)\ge1550+72a-50(p+q).                     \tag{18}
\]

At `a=7`, since `p+q≤12`, this implies `110(80−S)≥1454`.
In particular **`S≤66`**, and the exact global count
`S=74−U` gives **`U≥8`**.

For `a=8`, the singleton lower bounds improve to three. Put
`(s1,s2,s3)=(20,−52,−134)`. A stronger pointwise inequality is

\[
\begin{split}
H_8={}&(15-6i)d+(15-6j)e\\
 &+(22-11i)\alpha+(22-11j)\beta-s_i-s_j-26ij\ \ge0.
\end{split}                                               \tag{19}
\]

Again there are six unordered types:

| Type | `H8` |
| --- | --- |
| `11` | `9(d+e)+11(α+β)−66` |
| `12` | `9d+3e+11α−20` |
| `13` | `9d−3e+11(α−β)+36` |
| `22` | `3(d+e)` |
| `23` | `3(d−e)−11β+30` |
| `33` | `34−3(d+e)−11(α+β)` |

Types `11,22,33` are immediate. In type `12`, the alternatives
above give `12e+11α−11≥0`, because `β=α+2≥3`, or
`11α−14≥0`, because `β=α+1≥3`. In type `13`, they give
`6d≥0` or ten. In type `23`, they give `24−11β≥2` with
`β≤2`, or `33−11β≥0` with `β≤3`.

Now `Σs_i=−1120−10p` and dually for `q`. Summing (19) proves

\[
          30(80-S)\ge386+22a-10(p+q).                   \tag{20}
\]

At `a=8`, it follows that **`S≤65` if `p=q=6`**, and
**`S≤64` if `{p,q}={5,6}`**. Since `S=73−U`, respectively
**`U≥8` and `U≥9`**.

The two inequalities were found through local-state optimization,
but the displayed six-case proofs and exact sums replace it entirely.
They are additional necessary conditions, not an exclusion of the two
remaining degree-class configurations.

## 11. Sharp degree-five rectangles exclude eight elements of `A`

Each of the two members of `A3` has two sharp predecessors and
two sharp successors in `B`. The corresponding two-by-two rectangles
of ordered `B×B` pairs are disjoint, because a pair has only one
product. In particular, if their predecessor pairs intersect, their
successor pairs must be disjoint, and conversely.

Let `b_i` count the vertices of `B` with `t_x=i`, for `i=3,4,5`.
Then `U=b4+2b5`. The exact sharp-profile theorem (3) says that
when `p=6` each `A3` predecessor pair lies in the `b3` vertices;
when `p=5` it has one member of each of the `b3,b4` classes.
The successor statement uses `q`.

Suppose first `a=8,b=7` and `p=q=6`. Both sharp rectangles have
their row and column pairs in the same `b3`-element set. If `b3≤3`,
their two row pairs and their two column pairs would both intersect,
contradicting disjointness. Thus `b3≥4`, and
`U≤2(7−4)=6`, contrary to `U≥8` in §10.

If `p=5,q=6`, §10 gives `U≥9`, so `b3≤2`. Each sharp successor
pair requires two members of this class, so `b3=2` and both
successor pairs are identical. Their predecessor pairs must therefore
be disjoint. Each has one member with `t=3` and one with `t=4`,
giving two distinct vertices of each kind. The other three vertices
contribute at most six to `U`, so `U≤2+6=8`, a contradiction.
The case `p=6,q=5` is dual. Therefore `a=8` is impossible and

\[
\boxed{(a,b,a_3)=(7,8,2).}
\tag{21}
\]

There is now only one unit of sharp-degree excess:
`Σ_B(j_x−1)=a+a3−b=1`. Thus exactly one vertex of `B` has
sharp degree two and the other seven have sharp degree one.
The top-count classes are also forced.

If `p=q=6`, the disjoint-rectangle argument gives `b3≥4`.
With eight vertices in `B`, this yields `U≤8`. Since §10 gives
`U≥8`, equality forces

\[
(b_3,b_4,b_5)=(4,0,4),\qquad U=8,\qquad S=66.
\tag{22}
\]

This does **not** determine which top-count class contains the
unique sharp-degree-two vertex.

If `p=5,q=6`, the two sharp successor pairs cannot lie in just
two vertices: both vertices would have two distinct `A3` sharp
predecessors, but only one vertex of `B` has sharp degree two.
Thus `b3≥3`. If `b3≥4`, the bound `U≥8` would force `b3=4`
and all other vertices to have five top neighbors. This leaves no
vertex with four, contrary to the `p=5` predecessor-pair theorem.
Hence `b3=3`.

The two successor pairs intersect in exactly one vertex, necessarily
the unique sharp-degree-two vertex. Their predecessor pairs are
disjoint, giving two distinct vertices with four top neighbors.
Now `U≥8` and the remaining five vertices give

\[
(b_3,b_4,b_5)=(3,2,3),\qquad U=8,\qquad S=66.
\tag{23}
\]

The unique sharp-degree-two vertex lies in the `t=3` class.
Again the case `p=6,q=5` is dual. Equations (22)–(23) are necessary
profiles, not constructions or exclusions of the remaining cases.

## 12. Equality and central rows exclude unequal triple counts

Suppose `p=5,q=6`; the other unequal case is dual. Section 11
gives `a=7,a3=2,S=66`. Set
`(R1,R2,R3)=(9,−35,−97)` and `(C1,C2,C3)=(0,−1,−11)`.
The following local inequality is sharp in this case:

\[
H=(8-6i)d+(10-3j)e-6i\alpha+(18-3j)\beta
       -R_i-C_j-9ij\ \ge0.                              \tag{24}
\]

Here the `Cj` are coefficients, not central blocks. The generic
capacities, singleton lower bounds, and harmonic relation (13) suffice.
The complete check, including equality cases, is as follows. Each tuple
in the last column is `(d,e,α,β)`.

| Type | Nonnegative expression after harmonic balance | All zero cases |
| --- | --- | --- |
| `11` | `9d+9α−18`, with `α≥2` | `(0,0,2,2)` |
| `12` | `6(e+α)` or `6(α−1)` | `(1,0,0,2)`, `(0,2,1,2)` |
| `13` | `3(d+α+1)` or `15+3α` | none |
| `21` | `3(d+β)` or `3(β−1)` | `(0,1,2,0)`, `(2,0,2,1)` |
| `22` | zero | `d=e`, `α=β≤2` |
| `23` | `3−3α` or `3(3−d−α)` | `(0,2,1,2)`, `(2,1,1,3)` |
| `31` | `3(3−d−β)` or twelve | `(2,1,4,1)` |
| `32` | `6−6β` or `6(2−d−β)` | `(2,0,2,1)`, `(1,2,3,1)` |
| `33` | `9(3−d−α)` | `(2,2,1,1)` |

For example, type `12` has either `e=d−1,β=α+2`, or
`d=0,e=2,β=α+1≥2`. Type `21` is the corresponding reversed
harmonic split. Types `23,32` use `α≤1,β≤1`, respectively;
type `31` uses `d≤2,β≤1`. Thus each nonnegativity and each
equality condition in the table is an elementary consequence of the
stated integer bounds, not a solver assertion.

Summing (24), the marginals give `ΣR_i=−826`, `ΣC_j=−74`.
The other sums are `Σd=Σe=14`, `Σid=Σje=36`,
`Σα=Σβ=26`, and `Σiα=Σjβ=63`. Consequently

\[
\sum H=18\cdot14-9\cdot36-9\cdot63+18\cdot26
                       +826+74-9\cdot81=0.
\]

Every top must therefore have one of the zero states in the table.
There is exactly one top with `P`-block size one. It cannot have
type `13`. We exclude its remaining three possible states using the
exact central row/column sums. For each fixed central label `z`,

\[
\sum_{u:\,z\in P_u}\alpha_u=7,\qquad
\sum_{u:\,z\in P_u}O_u=16.
\]

Each sum has four tops. The dual column sums are `Σβ=7,ΣI=16`.

- If the singleton top has type `11`, it has `α=2,O=5`.
  Its central row has `C` sizes `3321`. Both size-three tops have
  `α=1`, so the size-two top must have `α=3`, hence type `32`
  and `O=4`. The size-three tops have odd `O` (three or five).
  The row's total `O` is therefore odd, not sixteen.
- In the type-`12` state `(1,0,0,2)`, it has `α=0,O=4`.
  A row of pattern `3321` has total `α≤0+1+1+4=6`.
  A row of pattern `3222` can reach seven only if both other
  size-two tops have `α=3,O=4`. Its size-three top has odd `O`,
  so again the total is odd, not sixteen.
- In the other type-`12` state `(0,2,1,2)`, it has `β=2,I=3`.
  Consider any central **column** containing this top.
  The `P` sizes are `3321`. Every `P`-triple top has `β=1`,
  so the remaining `P`-double top must have `β=3`, hence type
  `23` with `I=4`. Because `q=6`, the six `C`-triple blocks
  cover every central label exactly twice. This column must contain
  two tops with `C` size three. The original top has `C` size two,
  and the `23` top supplies only one; consequently one of the two
  `P`-triple tops has type `33`, with `I=3`. The final top has
  `I≤5`, giving total `I≤3+4+3+5=15`, a contradiction.

There is no possible singleton top. This excludes `p=5,q=6`
and, by duality, `p=6,q=5`. Thus the sixteen-top branch has the
single remaining numerical configuration

\[
\boxed{
a=7,\quad b=8,\quad a_3=2,\quad p=q=6,\quad S=66,
\qquad \#B_{t=3}=\#B_{t=5}=4.
}
\]

This is the intermediate analytic frontier, not a construction.
Section 13 and the subsequent finite graph lemmas now exclude it.

## 13. Central pair capacity locates the exceptional sharp degree

Continue in the final configuration of §12. Write `L=B_{t=3}`
and `H=B_{t=5}`; each has four vertices. There is exactly one
vertex of sharp degree two, all others having sharp degree one.
We prove that this exceptional vertex belongs to `L`.

First improve the central contribution inside the six-by-six rectangle
of `P`-triple sources and `C`-triple targets. Let `K_Z` count
the centrally valued pairs in this rectangle. Put
`x=N11,y=N12,z=N21`. The central moments give

\[
\begin{split}
 N_{13}&=2-x-y,\qquad N_{31}=2-x-z,\\
 N_{22}&=9-4x-2y-2z,\qquad N_{33}=5-3x-y-z.
\end{split}
\]

The weighted singleton sum is
`W_P1+W_C1=12−4x−y−z`; thus the central coverage argument of
§6 gives `K_Z≥21−4x−y−z`.
The singleton margins imply `x≤2`. If `x=2`, they force
`y=z=0`, giving `N33=−1`, impossible. If `x=1`,
the [singleton-coverage inequality](1485_nine_central_three_profile.md#6-singleton-coverage-excludes-another-seventeen-top-table)
`N11≤3N33` forces `N33≥1`, hence `y+z≤1` and `K_Z≥16`.
If `x=0`, the two singleton margins give `y,z≤2`, hence
`K_Z≥17`. In all cases,

\[
                         K_Z\ge16.                    \tag{25}
\]

Every vertex of `L` has three top predecessors and three top
successors. Their blocks partition nine into three triples. Hence
**every** top pair with product in `L` belongs to this same
six-by-six rectangle. The rectangle already contains twelve pairs
with product in `A3`, in addition to its centrally valued pairs.
Writing `g_b` for the number of top pairs with product `b`,
disjointness of products proves

\[
                         \sum_{b\in L}g_b\le8.          \tag{26}
\]

For clarity, introduce two incidence relations only on `B`:
`D_xy=1` means ordinary internal adjacency `x→y`, and
`Q_xz=1` means a sharp path `x⇒a⇒z` through `a∈A`.
Sharp-path uniqueness makes `Q` binary. An internal two-edge
path is bad exactly when its endpoint pair belongs to `Q`;
in particular `(D²)_xz≥2` implies `Q_xz=1`.
For an edge `xDy`, put

\[
 \eta(x,y)=\#\{z:zDx,\ Q_{zy}=1\},\qquad
 \beta(x,y)=\#\{z:yDz,\ Q_{xz}=1\}.
\]

Thus `η` counts bad predecessors and `β` bad extensions.
Let `τ_x=Σ_{y:xDy}η(x,y)` count bad paths with middle `x`.
The [exact good-pair identity](1485_nine_central_class_capacities.md#3-a-global-bad-path-count-without-edgewise-balance)
gives, for `x∈L`,

\[
                         g_x=3(4-j_x)-\tau_x.          \tag{27}
\]

We will also use the
[weighted auxiliary-fiber identity](1485_general_return_matching.md#6-a-weighted-version-beyond-the-smallest-central-class).
On an internal edge `xDy`, the top members of `R_y^{-1}(x)`
number `t_x−3+η(x,y)`, and their `P`-block sizes sum to the
edge's central auxiliary support. The top members of
`L_x^{-1}(y)` number `t_y−3+β(x,y)`, with the same sum of
their `C`-block sizes.

If `x,y∈L`, all these blocks are triples, so `η=β` on this
edge. If `x∈L,y∈H`, the first sum is `3η`, while the second
selects `2+β` parts of a five-part partition of nine.
Such a partition is either `32211` or `22221`. Selecting two,
three, four, or five parts and requiring their sum to be a multiple
of three gives exactly the following necessary alternatives:

\[
 (\beta,\eta)\in\{(0,1),(1,2),(2,2),(3,3)\}.             \tag{28}
\]

The `(2,2)` alternative requires pattern `32211` and omission of
its triple. The dual alternatives, with `β,η` interchanged,
hold for `H→L` edges. In particular, if `y∈H` has `j_y=1`,
its sole sharp predecessor lies in `A4` by (3), and the column
of `Q` at `y` has only one entry. Thus `η≤1`, and every
`L→y` edge has `(β,η)=(0,1)`.

Suppose now the exceptional sharp-degree-two vertex lies in `H`.
Every member of `L` then has `j=1` and precisely one sharp
predecessor and successor in `A3`. The restriction `Q_L` is the
union of the two disjoint two-by-two sharp rectangles. In particular
each of its rows and columns has exactly two entries, and there
are no sharp endpoint pairs between `L` and `H`.

Let `F` be the four-by-four restriction of `D` to `L`.
We claim it has at most ten entries. If it had at least eleven
and a full row, every column of `F` of degree at least two
would force an entry in the corresponding row of `Q_L`.
There could be at most two such columns, giving at most
`4+4+1+1=10` entries, a contradiction. The dual argument
excludes a full column. Thus all row and column degrees are at
most three. At least eleven entries would then require at least
three degree-three rows and three degree-three columns.
A degree-three row and a degree-three column intersect in at
least two places. These nine endpoint pairs would all belong to
`Q_L`, contrary to its row degree two. This proves the claim.

Every vertex of `L` has internal degree four, so the number
`ℓ` of `L→H` edges is `16−|F|≥6`. On an `L→L` edge,
`η≤2`, because the relevant column of `Q` has two entries.
On an `L→H` edge, `η=1` unless its target is the exceptional
vertex. That vertex has internal indegree `8−5−2=1`, so at
most one edge is exceptional; even there `η≤2`. Consequently

\[
 \sum_{x\in L}\tau_x
 \le2(16-\ell)+\ell+1
 =33-\ell\le27.
\]

But (26) and (27), with `j_x=1` on all four vertices of `L`,
give `36−Σ_Lτ_x≤8`, or `Σ_Lτ_x≥28`. This contradiction
proves

\[
\boxed{\text{The unique sharp-degree-two vertex belongs to }B_{t=3}.}
\tag{29}
\]

All steps above are analytic. A small incidence check suggested the
four-by-four matrix bound, but the row/column argument proves it
without enumeration. The residual case with the exceptional vertex
in `L` is excluded by the two small graph lemmas in the
[complete sixteen-top proof](1485_nine_central_sixteen_exclusion.md).

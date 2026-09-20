# Order forty with nine central elements: a single remaining degree split

Research theorem, 20 September 2026. These are necessary conditions used
in the now-completed [nine-central exclusion](1485_order_forty_nine_central_exclusion.md),
not Lean declarations.
The proof combines the already audited three-profile exclusions with
the new analytic capacity arguments below.

**Theorem.** An order-forty E1485 magma with minimum degree four and
nine central elements must have seventeen tops, seven degree-five
vertices, and seven degree-eight vertices. Every degree-five vertex has
four top neighbors in each direction. Every degree-eight vertex has
one sharp neighbor in each direction, and its top-neighbor counts agree.
Those seven balanced counts cannot all be four.

No model realizing these data is asserted to exist.

## 1. The remaining profiles have size four

Write `Z,A,B,T` for the degree classes `4,5,8,10`, with
`|Z|=9`, `a=|A|`, `b=|B|`, `h=|T|`. The
[full-block exclusion](1485_order_forty_ten_central_full_blocks.md)
gives `1≤|P_u|,|C_u|≤3` for every top. Every degree-five vertex
has common top-profile size three or four.

If a size-three profile exists, the
[complement-tiling and eighteen-top proofs](1485_nine_central_three_profile.md)
force `h=16` or `17`. Both have now been excluded:

- [Sixteen tops](1485_nine_central_sixteen_exclusion.md): analytic
  reduction and two explicitly checked sixteen-bit graph lemmas.
- [Seventeen tops](1485_nine_central_seventeen_degree_counts.md):
  an entirely analytic proof, ending with four- and five-vertex matrix
  inequalities.

Consequently every member of `A` has four top neighbors and exactly
one sharp neighbor in each direction. Sharp-neighbor existence gives
`a≥b`, while `a+b=31−h`.

The [variable-top-count inequality](1485_order_forty_variable_top_counts.md#2-three-top-neighbors-suffice-for-a-useful-bound)
gives `h²+8h≥392`, hence `h≥17`. The central moments give
`h≤21`; their exclusions of twenty and twenty-one in the
[central-partition calculation](1485_nine_central_three_profile.md#3-excluding-the-four-boundary-values)
use only block sizes at most three and the row patterns `3321,3222`,
not the existence of a size-three profile. Thus

\[
                            17\le h\le19.
\tag{1}
\]

## 2. Weighted degree-five capacities exclude nineteen tops

Let `p,q` count the `P`- and `C`-triple tops, respectively; do
**not** assume the three-profile bounds `p,q≤6` here. With `N_ij`
denoting paired block sizes, the singleton margins are
`2h−36+p,2h−36+q`, and the double margins `36−h−2p,36−h−2q`.

Every central column contains a `P`-double top, and every row a
`C`-double top. Their opposite block weights cover all nine central
labels, so each family has at least three tops. In particular

\[
                       p,q\le\left\lfloor(33-h)/2\right\rfloor.
\tag{2}
\]

For a top, write `α` for its number of successors in `A`. The
complement-block auxiliary support bound gives
`α≤f(C)`, where `f(1)=4,f(2)=3,f(3)=1`.
Set `X=Σ_(C=1)P`, and define the nonnegative slack `w=f(C)−α`.
The central moments and the exact degree-five profile counts give

\[
\begin{split}
 \sum f(C)&=5h-36-q, &\sum P f(C)&=90-X,\\
 \sum\alpha&=4a, &\sum P\alpha&=9a.
\end{split}
\]

Since `P≥1`,

\[
 5a=\sum(P-1)\alpha
 \le126-5h+q-X\le162-7h,                               \tag{3}
\]

where `X≥2h−36+q`. At `h=19`, sharp coverage gives `a≥6`,
whereas (3) gives `a≤5`, a contradiction. At `h=18`, (3)
and sharp coverage force `a=7`. At `h=17`, they leave `a=7,8`.

## 3. Joint singleton slack excludes eighteen tops

Suppose `a≥7`, and write `x=N11,y=N12,z=N21`.
A `C`-singleton top lies in a central row of pattern `3321`.
The other tops have total `A` capacity at most five, so this top
has `α≥2`. The slack bounds at `P`-singleton types `11,12,13`
are consequently `2,3,1`.

The exact total and weighted slack are

\[
 \sum w=5h-36-q-4a,\qquad
 \sum(P-1)w=126-5h+q-X-5a.                              \tag{4}
\]

The latter bounds the slack on `P>1`. Add the singleton slack
bound `2x+3y+N13` and substitute
`N13=2h−36+p−x−y`, `X=6h−108+3q−2x−z`.
After rearrangement, and then dualizing,

\[
\begin{split}
 3x+2y+z&\ge14h-234-p+q+a,\\
 3x+y+2z&\ge14h-234+p-q+a.
\end{split}
\tag{5}
\]

At `h=18,a=7`, their sum is
`3(2x+y+z)≥50`. But the singleton margins give
`2x+y+z≤p+q`, and (2) gives `p,q≤7`, so the left side is
at most forty-two. This excludes eighteen tops.

## 4. Eight degree-five vertices are impossible at seventeen tops

It remains that `h=17` and `a=7` or `8`. Suppose `a=8`.
The singleton lower bound improves to `α≥3` when `C=1`,
and dually `β≥3` when `P=1`, where `β` counts predecessors in `A`.
On a top of type `12`, we also have `α≥1`. Indeed, if `α=0`,
reciprocal balance gives

\[
                O-I=5+3(\alpha-\beta)\le-4.
\]

Since `O≥3`, this forces `I≥7`, contradicting the ordinary
degree bound `I+1+β≤10`. Therefore the singleton-type slack
bounds improve to `1,2,1`.

Now `Σw=17−q`, `Σ(P−1)w=1+q−X`, and the singleton slack
is at most `p−2+y`. The two directional slack bounds become

\[
           2x+y+z\ge12+q-p,\qquad
           2x+y+z\ge12+p-q.
\]

The singleton margins also give `2x+y+z≤p+q−4`. Hence
`min(p,q)≥8`, while (2) bounds both by eight. Thus `p=q=8`.
There are exactly three `P`-double tops and three `C`-double tops.
Each of these families must cover nine opposite central labels,
so all the opposite blocks are triples. This forces
`N12=N21=N22=0`. But the defect moment is

\[
                     4N11+2N12+2N21+N22=18,
\]

which would say `4N11=18`. This excludes `a=8`.

We have proved `h=17,a=b=7`, with all profiles in `A` of size
four. The seven sharp incidences in each direction cover all seven
members of `B`, so their sharp degrees are all one. Reciprocal
balance then equates their two top-neighbor counts.

## 5. Some further necessary counts, not a final exclusion

At the surviving split, (5) and the defect moment imply

\[
                   8\le2N11+N12+N21\le9,
                   \qquad N22\in\{0,2\}.
\]

The sharp two-step endpoint relation on `B` is a permutation matrix.
Writing `t_x` for its balanced top count and `d_x=7−t_x` for its
ordinary internal degree, we have `0≤d_x≤4`. Put `K=Σ_Bd_x`
and let `τ` count bad internal paths. Each edge has at most one bad
predecessor, so `τ≤K`. Exact top-pair counting gives

\[
 N= -86+7K-\sum_Bd_x²+\tau\ge0,
\]

where `N` is the number of top-valued top pairs. Hence
`Σ_B(8d_x−d_x²)≥86`. If `K≤14`, the concavity bound
`Σd_x²≥K²/7` makes this sum at most 84. Thus `K≥15`.
The number `S` of ordinary top-to-top edges is `57+K`, so `S≥72`.

Equivalently, the pointwise bound `τ_x≤d_x` gives
`g_x≥(t_x−3)²+5`. There are at most 61 top pairs left after
the central and degree-five outputs, so

\[
                         \sum_{x\in B}(t_x-3)^2\le26.
\]

For example, at most one degree-eight vertex can have seven top
neighbors, and at most two can have six.

These counts alone do not contradict each other. The subsequent
[central-gap and orbit arguments](1485_order_forty_nine_central_exclusion.md)
now exclude the last split and complete the nine-central case.

## 6. Uniform degree-eight top counts are now excluded

There is a useful structural reduction if every member of `B` has
top count four. Its internal adjacency matrix `D` is then three-regular
on seven vertices. Let `Q` be its sharp endpoint permutation matrix.
Each row of `D²` sums to nine. Its six positions outside `Q` have
value at most one, and its one `Q` position has value at most three.
All these bounds must be equalities:

\[
                           D²=J+2Q.
\]

Write `Q_(x,σ(x))=1`. The three paths from `x` to `σ(x)`
use all three ordinary successors of `x`. Thus `xDy` implies
`yDσ(x)`. This is a bijective transformation of ordered pairs, so
`D=QDᵀ`. Also `DQ=QD`, by commuting `D` with its displayed
square and using `DJ=JD=3J`. It follows that

\[
                    DDᵀ=Q^{-1}D²=J+2I.
\]

Therefore the rows form the seven-point projective-plane incidence
design: each has three points and any two distinct rows meet once.
Such incidence matrices exist, so this alone is **not a contradiction**.
Furthermore `tr(D)` is odd, since `tr(D²)=7+2tr(Q)` is odd
and `tr(D²)≡tr(D) (mod 2)` for an integral zero-one matrix.

The [new analytic exclusion](1485_order_forty_nine_central_uniform_exclusion.md)
uses the additional one-degree-five five-cycle identity. It forbids
every edge `x→σ⁻²(x)`, so `M=DQ²` has zero diagonal and
`tr(M²)` is even. But `M²=J+2Q⁵` makes this trace odd.
Thus the uniform case is excluded without enumeration or a
classification of the seven-point design. The same argument applies
to the analogous incidence equations at every odd internal degree.

This does not prove uniformity. The nonuniform case is excluded by
the later central-gap and orbit arguments, not by this uniform lemma.

## 7. The remaining internal graph has fifteen through twenty edges

The [nonuniform bounds](1485_order_forty_nine_central_nonuniform_B.md)
give `15≤K≤20` and `1≤d_x≤4`, hence `3≤t_x≤6`.
Indeed `Σd_x²≤42+K` and Cauchy's inequality give `K≤21`;
equality forces the now-excluded uniform case. An isolated internal
vertex would improve the bounds to `K²/6≤Σd_x²≤30+K`,
forcing `K≤16` and a negative number of top-valued top products.

At `K=15` the degrees must be `(3,2,2,2,2,2,2)`, and there
are no top-valued products of two tops. The
[ninety-case orbit check](1485_order_forty_nine_central_fifteen_edges.md)
now excludes this boundary, leaving `16≤K≤20`. Its final surviving
graph has an explicit forbidden five-walk; no SAT solver is used.

The [missing degree-five neighborhood theorem](1485_nine_central_missing_degree_five_neighbor.md)
also forces some top to have no `A` neighbors in one direction.
Its proof is a six-row pointwise inequality whose sum would otherwise
be `−2`. At `K=16` this rules out all internal degree patterns with
minimum degree two, including the theta-graph local fixtures. Only
the three patterns containing degree-one vertices listed in that note
remain at sixteen edges.

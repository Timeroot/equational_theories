# Order forty: ten central elements cannot have seventeen tops

Research proof, 20 September 2026, independently audited. This is an
analytic E1485 exclusion, not a Lean theorem. The arithmetic checker is an independent
regression check, not a SAT premise or a dependency of the argument.

**Theorem.** A finite E1485 magma of order forty with minimum degree four
and ten central elements cannot have seventeen top elements.

Write `Z,T,A,B` for the degree classes `4,10,5,8`, respectively, and
`a=|A|`, `b=|B|`. Suppose for contradiction that `|Z|=10`, `|T|=17`.
Then `a+b=13`. The
[central-block theorem](1485_order_forty_ten_central_small_blocks.md)
gives `1≤|P_u|,|C_u|≤3` for all tops `u`, and every vertex has at
least four top predecessors and successors. Every degree-five vertex
has exactly four in each direction and one sharp neighbor in `B`.

## 1. The tops contribute at most six units of excess

A central row contains four tops whose top-successor counts sum to
seventeen. Thus every top has four or five top successors; the dual
statement holds for predecessors. Write these counts as `4+δ_u^+`
and `4+δ_u^-`, with both bits in `{0,1}`. The `P`-blocks with
`δ^+=1` partition `Z`, as do the `C`-blocks with `δ^-=1`.

For a top with block sizes `(p,c)`, reciprocal-neighbor balance gives

\[
δ^+-δ^-=5(c-p)+3(A^+-A^-),
\tag{1}
\]

where `A^+,A^-` count its neighbors in `A`. Reducing modulo three
determines the bits whenever `p≠c`: the types `(2,1),(3,2),(1,3)`
have `(δ^+,δ^-)=(1,0)`, and their transposes have `(0,1)`.
Diagonal types have equal bits.

Let `n_pc` count tops of type `(p,c)`. The off-diagonal multiplicities
are symmetric. Indeed, put

`x=n21−n12`, `y=n32−n23`, `z=n13−n31`.

Equality of the total top-top in/out edge counts gives `x+y+z=0`.
The central degree sums give `−x−y+2z=0`. Finally the two selected
block partitions have size ten, giving `2x+3y+z=0`. These equations
force `x=y=z=0`. Set

\[
u=n_{12}=n_{21},\quad v=n_{13}=n_{31},\quad
w=n_{23}=n_{32},\quad q=n_{11}+u.
\]

The three central incidence moments are
`Σ1=17`, `Σ|P|=Σ|C|=40`, `Σ|P||C|=100`.
Equivalently, their defect sums give

\[
n_{22}=13-4q,\qquad u+2v+w=2q-2.
\tag{2}
\]

In particular `1≤q≤3` and `v≤q−1`.
Let `L=Σδ^+=Σδ^-`. In the selected `P`-partition let `S_i`
count blocks of size `i`. Then

\[
2L=10+S_1-S_3
\le10+n_{11}+v-w=12-q+3v.
\tag{3}
\]

If `q≤2`, or if `q=3,v≤1`, this gives `L≤6`.
The only other possibility is `q=3,v=2`; (2) then forces
`u=w=0` and `n22=1`. There would be exactly one top with a
double `C`-block. A central row containing this top would have
exactly one double block. But a partition of ten into four positive
parts at most three is `3331` or `3322`, never one double block.
Therefore

\[
\boxed{L\le6.}
\tag{4}
\]

## 2. The degree-eight counts leave only six tiny profiles

The [variable-top-count bound](1485_order_forty_variable_top_counts.md)
shows that each `x∈B` has balanced top count `4+e_x` and sharp
count `j_x`, where

\[
j_x\ge1,\quad e_x\ge0,\quad j_x+e_x\le4,
\qquad \sum j_x=a.
\]

Its internal `B` in/out degree is `k_x=4−j_x−e_x`.
Put `E=Σe_x`. Counting edges ending in `T` gives `E+L=10`,
so (4) implies `E≥4`.

Let `N` count ordered pairs of tops whose product is top. Central
outputs account for 160 pairs, and `A` outputs account for `12a`.
Define the nonnegative integer

\[
R_x=(j_x-1)(j_x-2)+e_x(j_x+e_x-2),\qquad R=\sum R_x.
\]

Nonnegativity follows directly for positive integer `j_x` and
nonnegative integer `e_x`. The global good-pair bound becomes

\[
\boxed{N\le2a-1-3E-R.}
\tag{5}
\]

Also `a≥b`, `a≤10` from `160+12a≤289`, and
`a=Σj_x≤4b−E`, hence `5a≤52−E`. Thus `a≤9` and
`4≤E≤5`.

If `E=5`, (5) leaves `a=8` or `9`.
For `a=8,b=5`, it forces `R=0`. The only zero-remainder types
`(j,e)` are `(1,0),(1,1),(2,0)`. Five units of excess on five
vertices would force all five to be `(1,1)`, contrary to `Σj=8`.
For `a=9,b=4`, it gives `R≤2`. Since `Σe=5`, some vertex has
`e≥2`; the only such type with remainder at most two is `(1,2)`,
already using the entire remainder budget. The other three have
`j≤2`, giving `Σj≤7`, again impossible. Hence `E=4` and `L=6`.

Now `a∈{7,8,9}`. For every allowed type one has

\[
R_x\ge2(j_x+e_x)-5.
\]

For completeness, for `j+e=1,2,3,4`, the minimum possible remainder
is respectively `0,0,1,4`, proving this inequality immediately.
If `a=9,b=4`, its sum gives `R≥2(9+4)−5·4=6`, whereas
(5) requires `R≤5`. Thus `a=7` or `8`.

For `a=7,b=6`, (5) gives `R≤1` and `N≤1`. The sharp counts
are five ones and one two. Remainder at most one forces `e∈{0,1}`,
with exactly four ones. Up to relabeling there are two possibilities:

| Profile | Multiset of `(j,e)` on `B` |
| --- | --- |
| I | `(1,0)` twice, `(1,1)` three times, `(2,1)` once |
| II | `(1,0)` once, `(1,1)` four times, `(2,0)` once |

For `a=8,b=5`, (5) gives `R≤3`. In fact `R≥2`: if `R≤1`,
then `j≤2` and `e≤1`. There would be three vertices with `j=2`
and four with `e=1`; at least two would have both, contributing
at least two to `R`. Therefore (5) again gives `N≤1`.
The [one-top-product gap](1485_top_product_count_gap.md) now implies

\[
\boxed{N=0.}
\tag{6}
\]

The four possible `(8,5)` multisets may be listed by the arithmetic
checker, but the following proof does not require that list.

## 3. Count the central parameters supporting an internal edge

For a central parameter `h`, the auxiliary relation `B_h` is
four-regular. Equation (6) means that it has no edge from `T` to `T`:
such an edge has the form `t→t*s` with both `t,s` top.
Every central element has four top neighbors, and every `A` element
has three auxiliary top neighbors (the fourth is its sharp `B` neighbor).
Consequently the number of internal `B_h` edges is

\[
4b-a-(4\cdot17-4\cdot10-3a)=4b+2a-28.
\tag{7}
\]

For an ordinary internal edge `x→y`, let
`H_xy={h∈Z:x B_h y}`. The top inputs of the five-element fiber
`R_y^{-1}(x)` have `P`-blocks which partition `H_xy`. They form
a subset of the `t_x=4+e_x` blocks partitioning `Z` at `x`.
If there are `s` such inputs, then

\[
|H_{xy}|\le\min(3s,10-t_x+s),
\qquad
s\le\min(5-j_x,\ 1+e_x+j_y).
\tag{8}
\]

The second upper bound follows from the exact fiber count
`s=1+e_x+η(x,y)`: a bad internal predecessor path ending at `y`
must have its start in one of the `j_y` sharp two-step predecessors
of `y`, so `η(x,y)≤j_y`. The first upper bound just reserves the
`j_x` sharp inputs. Both expressions on the right in the first
inequality increase with `s`, so any upper bound for `s` can be
substituted there. The dual bound, interchanging `x,y`, also holds.
No equality of bad predecessor and extension counts is assumed.
The two-sided top-fiber partition used here is also recorded in the
[general return-matching note, §6](1485_general_return_matching.md#6-a-weighted-version-beyond-the-smallest-central-class).

## 4. Five degree-eight elements are impossible

If `(a,b)=(8,5)`, equation (7) gives eight internal auxiliary edges
for every central parameter. The ordinary internal edge count is
`Σk_x=4b−a−E=8`. Thus every ordinary internal edge belongs to
every `B_h` and has `|H_xy|=10`.

Equation (8) then requires at least four top fiber inputs; the
five-element fiber also contains `j_x` sharp inputs. Thus every
vertex with positive internal outdegree has `j_x=1`.
But `Σj=8>5` gives a vertex with `j≥2`. Such a vertex cannot
have zero internal degree: that would mean `j+e=4`, and the
three possible types `(2,2),(3,1),(4,0)` have remainders `4,4,6`,
all larger than the entire budget `R≤3`. This is a contradiction.

## 5. Six degree-eight elements are impossible

It remains that `(a,b)=(7,6)`, with profile I or II.
There are thirteen ordinary internal edges, and (7) gives ten
internal auxiliary edges for each of ten parameters. Therefore

\[
\sum_{x\to y\text{ in }B}|H_{xy}|=100.
\tag{9}
\]

For profile I, call the two `(1,0)` vertices low, the three `(1,1)`
vertices medium, and the remaining `(2,1)` vertex `v`.
The dual bounds (8) give support at most eight on every edge,
and at most six on an edge from a low vertex to a vertex other
than `v`. The two low vertices have three outgoing internal edges
each; `v` has indegree one. Hence at least five distinct edges have
support at most six. The sum in (9) is at most

\[
13\cdot8-5\cdot2=94<100.
\]

For profile II, let `u` have type `(1,0)`, let `v` have type `(2,0)`,
and call the four `(1,1)` vertices medium. The bounds (8) give
support at most eight between medium vertices, at most six on
every edge incident with `u` or joining `v` to a different vertex,
and at most nine on the possible loop `v→v`.
The internal indegree and outdegree of `u` are three, so at least
five distinct edges touch it. Thus (9) is at most

\[
13\cdot8+1-5\cdot2=95<100.
\]

Both remaining profiles contradict (9), completing the proof.

## Arithmetic regression

Run `python3 scripts/1485_order_forty_seventeen_top_counts.py` to
check all the allowed degree-eight type multisets and the support
capacities used above. The script uses only short integer loops.
The proof itself provides the case reductions explicitly; it does
not rely on the program to certify an absent magma or incidence system.

# A restriction at order forty-eight and minimum degree four

Research note, 19 September 2026. These are analytic necessary
conditions, not Lean declarations and not an exclusion of order 48.

Assume a finite E1485 magma has minimum translation degree four,
exactly four central vertices, and exactly the four degrees

\[
4,\quad6,\quad8,\quad12.
\]

Its order is 48. Write `Z,A,B,T` for these degree classes and
`f=|A|`, `g=|B|`. The
[minimal-central-count theorem](1485_minimal_central_count.md)
gives `|T|=16` and exactly four top neighbors in each direction
at every vertex. Every member of `A` has exactly two sharp
neighbors in each direction, both in `B`.

**Results.**

1. A degree-12 output of two top inputs has at most one top input
   in each participating top translation fiber. Its good top pairs
   consequently form a matching.
2. For every central parameter `z`, if `R_z` counts auxiliary
   edges inside `B`, then
   \[
   \boxed{5f+R_z\le88.}
   \]
   A second count of those internal auxiliary edges, followed by
   good-return matching arguments and a small internal-graph
   obstruction improve this to **`f≤14`**. The elementary class
   counts previously allowed `f=15,16,17,18`, which are excluded.

## Shortest proof of the cardinality bound

The subsequent
[general four-degree return argument](1485_four_degree_minimal_core_returns.md#4-a-short-route-through-the-order-forty-eight-class-bounds)
now proves `f≤15` directly. Briefly, it excludes sharp count four
in `B`, giving `f≤16`; at `f=16` a sharp-count-three vertex
would require at least three sharp-count-one top-return partners,
although the total sharp-degree deficit permits at most two.
The internal-graph argument in §7 below excludes `f=15`.

This is the shortest current route to `f≤14`. The longer packing
proof is retained because it independently proves the matching,
auxiliary-edge and bad-path restrictions used elsewhere in this note.

## 1. A central-parameter set containing a top output

Label the tops by their central predecessor and successor:
`t_ij=z_i*z_j`, with `i,j∈{0,1,2,3}`. Write `H(t)=i` and
`C(t)=j`. A top pair has a central product exactly when the
successor label of its first input equals the predecessor label
of its second input.

Fix `u∈T` and a central vertex `z_l`. Put

\[
S=u*Col(z_l)=B_{z_l}(u),\qquad j=C(u).
\]

The four outputs in `S` are distinct, one of them is `z_j`, and
the other three are noncentral. With `v=z_l*u`, the
fixed-parameter set is

\[
F_v(u)=L_u^{-1}(S),\qquad |F_v(u)|=16.
\]

It contains `Row(b)` for every `b∈S`, as well as `Col(z_l)`.
In particular it contains the seven top points in the cross

\[
X=Row(z_j)\cup Col(z_l)
 =\{H=j\}\cup\{C=l\}.
\]

Suppose `S` contains a top output `t`, of degree 12. Its ordinary
row has four top and eight non-top elements. Thus `F_v(u)`
contains at most eight top elements.

There is at least one degree-six output in `S`. Indeed its least
noncentral output has degree at most seven by the
[row-local bound](1485_first_top_output_fibers.md#5-a-row-local-degree-bound),
and six is the only occurring degree in `(4,7]`.

Consider such an output `a∈A`. Its equality-matrix profile has
two central labels, each repeated twice, on both sides. Since
`u∈TopPred(a)` and `C(u)=j`, the two labels are `j` and some
`k≠j`. Its two good top inputs under `L_u` are exactly its
two top successors with `H=k`; those with `H=j` give central
products. One of its good inputs lies in `Col(z_l)`. The other
does not, because `TopSucc(a)` meets each central column once.
That second input therefore lies outside `X`.

Distinct degree-six outputs in `S` have distinct such outside
points, since they belong to different fibers of `L_u`. Two
degree-six outputs would force at least nine top points into
`F_v(u)`, contradicting its upper bound of eight. Hence there
is exactly one degree-six output in `S`.

Nor can there be two degree-12 outputs. The
[ordered-degree bound](1485_auxiliary_ordered_degree_bound.md)
requires a degree-12 member of this four-element set to have
at least three strictly lower-degree members: if there were `j'`
such members, it would give `12≤4+3j'`. Thus each top output
is the sole maximal member. We have proved

\[
\boxed{S\text{ containing a top output has degrees }4,6,8,12.}
                                                               \tag{1}
\]

## 2. The high fibers each have just one top input

The four fibers of `L_u` over the members of the set (1) are
disjoint, have size four, and partition `F_v(u)`. The central
fiber has four top inputs. The degree-six fiber has exactly two:
its other two inputs are the two sharp `B` successors of that
output. The degree-eight and degree-12 fibers each have at least
one top input, because their outputs belong to `S`.

These lower bounds already total eight top points, which is the
upper bound from §1. Therefore the degree-eight and degree-12
fibers each have exactly one top input.

Every top representation `t=u*w` can be treated this way by
choosing the central successor `z_l` of `w`. Thus a fixed top
left input has at most one top right input producing `t`.
The dual argument gives the other direction, proving the matching
assertion. This conclusion is special to the displayed degree
pattern and central count; it is not a general replacement for
the earlier degree-`r²` matching theorem.

## 3. Count the auxiliary edges by degree class

Fix `z∈Z`. The relation `B_z` is four-regular in both directions
and contains every sharp edge. It has exactly `2f` edges in
each of the blocks `A→B` and `B→A`. Its other edges incident
to `A` lead to `T`, so the counts of `A→T` and `T→A`
are both `4f−2f=2f`.

Let `R_z≥0` be the number of edges of `B_z` inside `B`.
Degree balance at the entire class `B` gives

\[
\#(B\mathrel{B_z}T)=\#(T\mathrel{B_z}B)
=4g-2f-R_z.
\]

This uses only equality of the two *total* sharp edge counts,
not equality of sharp in/out counts at individual members of `B`.
The `Z↔T` blocks each have 16 edges. Counting the 64 auxiliary
edges out of the 16 tops therefore gives

\[
\#(T\mathrel{B_z}T)
=64-16-2f-(4g-2f-R_z)=48-4g+R_z.
\]

Since `f+g=48−4−16=28`, these become

\[
\#(T\mathrel{B_z}T)=4f-64+R_z,
\qquad
\#(T\mathrel{B_z}B)=112-6f-R_z.                         \tag{2}
\]

For each top vertex `u`, its auxiliary row is the set `S` in
§1. By (1), if it contains a top member then it contains exactly
one such member and exactly one member of `B`. Thus, row by row,
the number of top members is at most the number of `B` members.
Summing and applying (2) yields

\[
4f-64+R_z\le112-6f-R_z,
\qquad\boxed{5f+R_z\le88.}
\]

As `R_z≥0`, this proves `f≤17`.

For comparison, the elementary bounds give `10≤f≤18` before
this argument. Indeed every member of `B` has between one and
four sharp neighbors in each direction, and their total is `2f`;
hence `g≤2f≤4g`. Substituting `g=28−f` gives the stated
integer interval. The argument so far narrows it to

\[
\boxed{10\le|A|\le17.}
\]

The next section removes seventeen as well.

## 4. Every internal edge occurs for at least two central parameters

Let `E` count ordinary edges inside `B`. A member of `B` has
degree eight, four top neighbors and otherwise only sharp `A`
neighbors or internal `B` neighbors. Summing the sharp count gives

\[
E=4g-2f=112-6f.
\]

For an ordinary edge `b→b'` inside `B`, the
[top-fiber slot bound](1485_three_central_minimum_top_output.md#a-general-top-fiber-slot-bound)
places `b'` in at least

\[
\max(0,n/d(b')-d(b)+4)=6-8+4=2
\]

of the four top fibers `L_t^{-1}(b)`, for `t∈TopPred(b)`.
Because there are four central vertices and every top vertex has
one central predecessor, `z↦z*b` bijects `Z` onto `TopPred(b)`.
The fiber identity `B_z(b)=L_{z*b}^{-1}(b)` therefore says that
the edge belongs to at least two of the four auxiliary relations.
Consequently

\[
\sum_{z\in Z}R_z\ge2E=224-12f.
\]

Summing `5f+R_z≤88` over the four parameters gives the upper
bound `Σ_z R_z≤352−20f`. Comparison proves `8f≤128`, hence

\[
\boxed{10\le|A|\le16.}
\]

## 5. Equality forces all reciprocal-class sharp counts above one

If `f=16`, then `g=12`, and every inequality in §4 is an
equality. In particular:

* Every `R_z=8`.
* Every ordinary internal `B` edge belongs to exactly two of
  the four auxiliary relations.
* For each central parameter, the auxiliary counts `T→T` and
  `T→B` are both eight. Their pointwise inequality from §3
  is therefore an equality in every top row.

Thus each top auxiliary row has exactly one of the degree patterns

\[
\boxed{\{4,6,6,6\}\quad\text{or}\quad\{4,6,8,12\}.}
\]

For each parameter, eight top rows have each pattern. In particular
every degree-eight top output occurs in the second pattern, so §2
shows that its participating top fibers also have exactly one top
input. Its good top pairs form a matching as well.

There is a useful consequence for individual members of `B`.
Their sharp in- and out-degrees agree: they each have four top
neighbors, and ordinary degree balance together with reciprocal
neighbor balance then equates the sharp counts. Denote that count
by `j`. The remaining `4−j` non-top neighbors are internal `B`
neighbors. Each lies in exactly two top fibers by the equality
case above, while each sharp neighbor lies in all four. Counting
the sixteen slots in the four top fibers gives

\[
g_B=16-4j-2(4-j)=8-2j
\]

good ordered top pairs with this member as middle. The matching
property bounds `g_B≤4`, so `j≥2`. Therefore the possible sharp
counts and numbers of good top pairs are precisely restricted to

\[
\boxed{(j,g_B)\in\{(2,4),(3,2),(4,0)\}.}
\]

## 6. Good returns exclude equality

Continue to suppose `f=16`, so `|B|=12`, every sharp count
`j_b` in `B` is at least two, and `Σ_b j_b=2f=32`.

First fix `b∈B` and count its two-step ordinary paths whose
middle and endpoint both lie in `H=A∪B`, with the endpoint
in `B`. It has `j_b` sharp successors in `A`, each with two
successors in `B`. Its other non-top successors are the `4−j_b`
members of `B`, each of which has at most two successors inside
`B`, since its own sharp count is at least two. Consequently
there are at most

\[
2j_b+2(4-j_b)=8
\]

such paths. There are twelve possible endpoints in `B`. At least
four therefore have no ordinary middle in `H`. Their good middle
cannot be central either, so their product with `b` is top. In
particular every `b∈B` has some `d∈B` with `b*d∈T`.

Here is the general good-return constraint at such a pair. Put
`e=b*d∈T` and

\[
X=L_e^{-1}(d),\qquad Y=R_e^{-1}(b).
\]

Both fibers have size four. For `x∈X`, E1485 and its dual give

\[
(x*b)*(b*(e*x))=b,
\qquad ((b*d)*x)*(x*b)=x.
\]

Since `e*x=d` and `b*d=e`, these become
`(x*b)*e=b` and `d*(x*b)=x`. Thus `x↦x*b` is a bijection
from `X` to `Y`, and each matched pair is an ordinary edge.

The set `X` contains all `j_d` sharp successors of `d` in
`A`, and `Y` contains all `j_b` sharp predecessors of `b`
in `A`. There are no ordinary `A→A` edges, because
`6²<48`. The bijection must therefore send those `j_d` members
of `X∩A` outside `Y∩A`, proving

\[
j_d+j_b\le4.
\]

Both counts are at least two. Every `b` has such a top-return
partner `d`, so every `j_b=2`. This contradicts
`Σ_b j_b=32`, since `|B|=12` would instead give 24.
The case `f=16` is impossible, and we conclude

\[
\boxed{10\le|A|\le15.}
\]

## 7. Fifteen degree-six vertices are impossible as well

Suppose `f=15`, so `g=13` and the sum of the balanced sharp
counts `j_b` over `B` is 30. Each count lies in `{1,2,3,4}`;
the internal in- and out-degree of `b` is `4−j_b`.

For an arbitrary `b∈B`, the number of ordinary two-step paths
to a `B` endpoint through `A∪B` is at most

\[
2j_b+3(4-j_b)=12-j_b<13.
\]

Thus every `b` has some top-return partner in `B`. The general
fiber matching from §6 gives `j_b+j_d≤4` at every such pair,
so `j_b=4` is impossible.

Let `n_i` count members of `B` with sharp count `i`. Then

\[
n_1+n_2+n_3=13,\qquad n_3-n_1=30-2\cdot13=4.
\]

In particular some member has sharp count three. Such a member
has one internal successor and at most `6+3=9` two-step paths
through `A∪B` to `B` endpoints. It therefore has at least four
top-return partners, all of sharp count one by the matching bound.
Hence `n_1≥4`. But `n_2=9−2n_1≥0` gives `n_1≤4`, so

\[
\boxed{(n_1,n_2,n_3)=(4,1,8).}
\]

Write `L,M,H` for these three subsets of `B`; their sizes are
four, one and eight, and their internal in/out degrees are three,
two and one, respectively.

Every member of `H` has top-return products with all four members
of `L`, and no other top-return partners. To leave at most four
such partners its unique internal successor must have internal
out-degree three, so it belongs to `L`. The column-dual argument
gives all the reversed assertions. Thus

\[
H*L\subseteq T,\qquad L*H\subseteq T,
\]

and every internal predecessor and successor of a member of `H`
lies in `L`.

For `x∈L`, let `a_x` count its predecessors in `H` and `b_x`
its successors in `H`. Their sums are both eight and every value
is at most three. If `a_x>0`, then `x` has no successor in `L`:
such an edge would give a path `H→x→L` with a degree-eight
middle, although the product of those endpoints is top of degree
twelve. This contradicts the minimum-degree-middle theorem.
There is only one vertex in `M`, so `x` must then have at least
two successors in `H`: `b_x≥2`. Dually `b_x>0` implies
`a_x≥2`.

Call `x` active when these equivalent positivity conditions hold.
At least three of the four members of `L` are active, since the
sum of their `a_x` is eight and each is at most three. If exactly
three were active, the remaining vertex would have no successor
in `H` and could not point to any active member of `L`: active
members have no predecessors in `L`. Only itself and the single
member of `M` would remain, at most two possible successors,
contrary to its internal out-degree three. Loops are allowed in
this count; they still contribute at most one successor.

Hence all four members are active. Each `a_x,b_x≥2`, and their
sums are eight, so all are exactly two. Each member of `L`
therefore has its third internal outgoing edge to the single
member of `M`. That vertex would have internal in-degree at least
four, contradicting its prescribed in-degree two. This excludes
`f=15` and proves

\[
\boxed{10\le|A|\le14.}
\]

## 8. Necessary conditions at the next endpoint

If `f=14`, then `g=14` and `Σ_b j_b=28`. The same
`12−j_b<14` path bound gives every member of `B` a top-return
partner, again excluding sharp count four. Thus `n_3=n_1`.
If a sharp-count-three vertex exists, it has at least `14−9=5`
top-return partners, all of sharp count one. The only possible
sharp-count profiles are consequently

\[
\boxed{(n_1,n_2,n_3)\in
\{(0,14,0),(5,4,5),(6,2,6),(7,0,7)\}.}
\]

There is also a small bound on failures of goodness inside `B`.
For an ordinary internal edge `b→x`, let `c(b,x)` count the
central parameters for which it belongs to the auxiliary relation.
Since the four central columns partition `T`, and multiplication
is injective on each such column, `c(b,x)` is exactly the number
of top inputs in `L_b^{-1}(x)`. That fiber has size six and
contains all `j_x` sharp `A` successors of `x`. Therefore it
contains `6−c(b,x)−j_x` internal `B` successors, out of the
`4−j_x` available. The number of bad internal two-edge paths
extending this edge is exactly `c(b,x)−2`.

Summing over ordinary internal edges proves

\[
\#\{\text{bad }B\to B\to B\text{ paths}\}
=\sum_{z\in Z}R_z-2E.
\]

At `f=14`, we have `E=28` and `R_z≤88−5f=18`, hence at
most sixteen bad internal two-edge paths. This is an additional
constraint, not an exclusion of any of the four displayed profiles.

The [seven-plus-seven note](1485_order_forty_eight_seven_three.md)
further restricts the last profile. Its sharp-count-three vertices
split into those attached to sharp-count-one vertices and isolated
directed cycles. The isolated part is empty, a two-cycle, or a
three-cycle; the attachment possibilities in the three-cycle case
are restricted further. No whole profile is excluded by that note.

## 9. Matrix restrictions in the all-sharp-count-two endpoint

Consider the remaining profile `(n_1,n_2,n_3)=(0,14,0)` at
`f=14`. The adjacency matrices

\[
P:A\to B,\qquad Q:B\to A,\qquad D:B\to B
\]

are all fourteen-by-fourteen zero-one matrices, two-regular in
both directions. The matrices `PD,DQ` are zero-one because all
their paths contain a sharp edge. Put `K=QP`, also zero-one
and four-regular. Let `E` indicate `B×B` endpoint pairs with
a good middle in `B`, and `G` those with a top good middle.
Then

\[
K+E+G=J,
\qquad F=D^2-E\ge0,
\qquad \operatorname{supp}(F)\subseteq\operatorname{supp}(K),
\qquad \sum F\le16.
\]

The support assertion follows from strict descent: a bad middle
in `B` has a lower-degree replacement in `A`. In particular an
entry of `D²` equal to two contributes two bad paths, not one;
two different ordinary middles of the same degree cannot include
a good one.

The good-return matching gives a further restriction. If the
reverse product of two `B` endpoints is top, there is **no**
three-edge path between them entirely inside `B` with both
adjacent two-edge paths good. Indeed the associated size-four
fiber matching contains two sharp `A` members on each side.
Since there are no `A→A` edges, every matched edge has exactly
one endpoint in `A`, ruling out the middle `B→B` edge of
such a path.

More quantitatively, let `R_{db}` count good-good three-edge paths
from `d` to `b` wholly inside `B`. The
[general return matching](1485_general_return_matching.md)
has exactly four edges incident to `A`, for any product `b*d`.
Its remaining capacity therefore gives the entrywise bound

\[
\boxed{R\le4K^{\mathsf T}+2E^{\mathsf T}.}
\]

Indeed the return fibers have size eight, six, or four when the
product belongs respectively to `A`, `B`, or `T`. This
strengthens the preceding zero bound on the support of `Gᵀ`.

The [three-partition-label description](1485_min_four_six_profiles.md)
also restricts the top profiles of these fourteen `A` vertices:
at most four in each row and column can fail its unique-intersection
criterion. The profile criterion and this return bound remain
necessary conditions, not exclusions.

Finally every ordinary five-cycle entirely inside `B` has zero,
two consecutive, or five bad positions. The five-cycle law
already excludes isolated bad positions. If a mixed adjacent
pair in such a cycle had a bad opposite return path, its good
return middle could not be top, since the cycle supplies an
ordinary middle of degree eight. It could not lie in `A`
either: the three paths meeting that sharp middle are good, so
the other two statuses would have to agree. Hence it lies in
`B`, where equality of degrees forces it to be the original
return middle, contradicting badness. This eliminates blocks of
three or four bad positions.

These matrix and cycle restrictions have not yielded an exclusion
of the all-sharp-count-two profile. The surviving cases are not
asserted to exist. This note does not exclude them, other central
cardinalities at minimum four, or other possible degree patterns
at order 48.

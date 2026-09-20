# Four remaining top-valued top pairs in the order-forty boundary case

Research note, 19 September 2026. Assume the fourteen/six split
and one of the three aligned internal incidence types in the
[near-saturation analysis](1485_order_forty_near_saturation.md).
The degree classes `Z,A,B,T` have degrees `4,5,8,10` and sizes
`4,14,6,16`. These are analytic necessary conditions, not an
existence claim or by themselves an exclusion of that split.

**Results.** There are exactly four ordered pairs `(u,v)∈T²`
whose product is top. A high-sharp `B` vertex has two good top
pairs, and a low-sharp one has six. Whenever a central-parameter
set `u*Col(z)` contains a top element, its four distinct members
have degrees exactly `4,5,8,10`.

## Every internal B edge has two top inputs in its translation fiber

Write `l,l'` for the two low-sharp vertices, and `H_l,H_l'`
for their attached high-sharp pairs. The internal successor sets
are `Row(l)∩B={l'}∪H_l` and `Row(b)∩B={l}` for `b∈H_l`.
The sharp-path matrix has the two low loops and a high block
`J₄` minus a permutation preserving these pairs.

For every internal edge `b→c`, the fiber `L_b⁻¹(c)` has size
five, and exactly three of its inputs are non-top:

* For `b∈H_l,c=l`, they are the sharp-loop `A` vertex at `l`,
  the other low vertex `l'`, and the high vertex omitted from
  the sharp-path row at `b`.
* For `b=l,c∈H_l`, they are the three sharp `A` successors
  of `c`. The only other non-top candidate is `l`, but
  `l*l` is its sharp-loop `A` vertex.
* For `b=l,c=l'`, they are the sharp-loop `A` vertex at `l'`
  and the two high vertices in `H_l'`. Again `l*l` excludes
  the remaining non-top candidate.

These lists follow from the explicit internal and sharp-path
matrices: a sharp path is good; an internal two-step path without
a sharp replacement has its indicated `B` middle. A central input
always gives a top product. Thus in every case

\[
\boxed{|L_b^{-1}(c)\cap T|=2\qquad(b\to c\text{ inside }B).}
                                                               \tag{1}
\]

## Count all top-endpoint products

Fix `b∈B`, with balanced sharp count `j_b`. Its four right
top-translation fibers have size four each. Every sharp `A`
predecessor occupies all four fibers, accounting for `4j_b`
slots. Each of the `4−j_b` internal predecessors occupies
exactly two, by (1). There are no central predecessors of `b`.
The remaining slots are precisely its good top pairs. Hence

\[
g_b=16-4j_b-2(4-j_b)=8-2j_b.
\]

There are four vertices with `j_b=3` and two with `j_b=1`,
so `Σ_b g_b=4·2+2·6=20`. Each degree-five vertex contributes
`4·3=12` top pairs, and the four central vertices contribute
sixteen each. The entire top square has `16²=256` pairs,
leaving

\[
\boxed{|\{(u,v)\in T^2:u*v\in T\}|
=256-14\cdot12-20-4\cdot16=4.}                  \tag{2}
\]

## A central-parameter set containing a top output

Fix `u∈T`, a central `z`, and put `S=u*Col(z)`. The
[first-output fiber identities](1485_first_top_output_fibers.md)
say that `S` has four distinct members, one central, and is a
fiber of a top translation. Its full inverse image under `L_u`
has size sixteen and contains the row of every member of `S`.

Suppose `t∈S` is top. Its row contains six non-top elements,
so this sixteen-element inverse image contains at most ten tops.
It contains the seven top points in the central row/column cross
`Row(c)∪Col(z)`, where `c` is the central member of `S`.

The row-local bound supplies at least one degree-five member of
`S`: its least noncentral degree is at most seven. Each degree-five
member has three top inputs under `L_u`. One lies in `Col(z)`;
the other two lie outside the seven-point cross. Different members
have disjoint fibers. Two degree-five members would therefore
force at least eleven tops into the inverse image, which is
impossible. There is exactly one such member.

The only other alternative to the claimed pattern is therefore
`4,5,10,10`. For either degree-ten member `t`, descent and
absorption put `Row(t)` in the union of its own fiber and the
fibers of the two lower-degree members. This union has size twelve.
The two inputs in `Col(z)` giving those lower members do not
belong to `Row(t)`, so at most ten elements remain. Since
`|Row(t)|=10`, this is an equality.

But these three fibers contain at least `4+3+1=8` top inputs.
Removing two points leaves at least six tops in `Row(t)`, whereas
every vertex has exactly four top successors. This contradiction
excludes the alternative and proves

\[
\boxed{t\in S\cap T\quad\Longrightarrow\quad
\{d(a):a\in S\}=\{4,5,8,10\}.}                  \tag{3}
\]

In this situation the degree-eight and degree-ten fibers have
positive top-input counts with sum at most three: the central
and degree-five fibers already account for seven of the at most
ten tops. In particular either high fiber has at most two top
inputs. These restrictions use only the four degrees `4,5,8,10`
and the minimum and central count four, not the sizes of `A,B`
or their internal incidence type. In particular the degree-pattern
and high-fiber conclusions also apply to the now-excluded
[thirteen/seven branch](1485_order_forty_thirteen_directions.md)
and the still-open smaller degree-five classes. The exact four-top-product
count earlier in this note is specific to the fourteen/six incidence
types, now excluded by a shorter analytic argument.

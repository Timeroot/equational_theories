# Degree-five profiles leave at most six degree-four vertices

Research note, 19 September 2026. The arguments below are analytic,
not yet Lean declarations. We work in the remaining hypothetical
case with minimum degree three and exactly three central vertices.

**Theorem.** There are at most six degree-four vertices. If there
are exactly six, their missing predecessor/successor profile cells
form a perfect matching. Every degree-five vertex then has two
sharp predecessors and two sharp successors; its top predecessors
form a central column, and its top successors form a central row,
with different central labels.

The [degree-five necessity theorem](1485_three_central_requires_five.md)
ensures that degree five occurs. In particular `60|n`, so all the
degree classes distinguished below are disjoint.

## Notation and elementary capacity

Write `A` for the degree-four class and `B` for the degree-`n/4`
class. There are nine top vertices, and every vertex has three top
predecessors and three top successors. The sharp maps `F,G:A→B`
are surjective, have fibers of size at most three, and satisfy

\[
|G^{-1}(b)\cap F^{-1}(b')|\le1.
\]

Suppose `|A|≥6`. Then `|B|≥3`, so the
[opposite-parity profile argument](1485_three_central_saturated_four.md#the-saturated-profile-grid)
applies. The three possible top predecessor profiles `P_p` of `A`
and three possible top successor profiles `Q_q` each partition the
top set, with `t_pq=P_p∩Q_q`. There is at most one member of `A`
per cell `(p,q)`. Each `F`-fiber meets each `P`-row at most once;
each `G`-fiber meets each `Q`-column at most once.

For a top vertex `t`, write `H(t)` for its central predecessor and
`C(t)` for its central successor. A central row has fixed `H`; a
central column has fixed `C`. Every top predecessor set meets each
central row once, and every top successor set meets each central
column once.

Fix a degree-five vertex `c`, and write `U,V` for its top
predecessors and successors. Its two non-top neighbors, in either
direction, have complementary degree four or five. Those of
complementary degree five are sharp, and there is at least one.
Thus there is at most one `B` neighbor in each direction; any
other non-top neighbor has degree `n/5`.

Every vertex of `U` participates in a good top pair with middle
`c`: its three-element fiber at `c` cannot fit inside the two
non-top successors. Dually every vertex of `V` participates.
The [top-fiber slot bound](1485_three_central_minimum_top_output.md#a-general-top-fiber-slot-bound)
gives

\[
3\le g(c)\le4,                                      \tag{1}
\]

where `g(c)` is the number of good ordered top pairs. More precisely,
the upper bound is four with one sharp successor and three with two.

## Neither profile can be a degree-four profile line

The set `U` cannot equal a `P`-line. Suppose `U=P_p`. If a top
successor `v∈V` lies in `Q_q` and `(p,q)` is occupied by a member
of `A`, no endpoint pair in `P_p×{v}` has good middle `c`: its
product is central or degree four. This contradicts activity of `v`.

Thus every such `(p,q)` is missing. Exactly one of the three pairs
in `P_p×{v}` is central. For the other two, the path through `c`
cannot descend to degree three or four, so is good. Each of the
three successors supplies two good pairs, contrary to (1).

Dually `V` cannot equal a `Q`-line. This argument does not assume
that all three possible `P`- or `Q`-profiles occur among members
of `A`.

## Exceptional profiles fit inside a single sharp fiber

Put `m_q=|U∩Q_q|`. If there is a non-top `B` predecessor of
`c`, denote it by `b_-`. For any `a∈A` with `F(a)≠b_-`, the
ordinary paths from `a` to `c` have only top middles: the only
non-top successor of `a` is `F(a)`, and the other possible non-top
predecessors of `c` lie in the distinct degree-`n/5` class.
Such a path has a unique middle, since a bad top middle would
require a non-top replacement. Consequently

\[
|Q(a)\cap U|=1.                                    \tag{2}
\]

If `c` has no `B` predecessor, (2) holds for all `a`.

Every column `q` with `m_q≠1` therefore has all its occupied
cells inside the one fiber `F^{-1}(b_-)`. If not all `m_q` equal
one, at least two differ from one, because their sum is three.
Their occupied cells number at most three, and the remaining
column has at most three. Hence

\[
U\text{ not transversal to the }Q_q\quad\Longrightarrow\quad
|A|\le6.                                           \tag{3}
\]

Moreover, in the equality case `|A|=6`, exactly two columns are
exceptional, their occupied cells form a three-element `F`-fiber,
and the third column is full. The exceptional cells meet each
`P`-row exactly once, so every `P`-row contains exactly two cells
of `A`. The argument includes the possibility of an empty column;
no nonemptiness assumption on individual profiles is needed.

The dual statements apply to `V`, the `P`-rows, and a possible
`B` successor `b_+` using the map `G`.

## Both profiles must be central lines

A three-element top set transversal to both the `Q`-columns and
the central `H`-rows is either a `P`-line or a central `C`-column.
Dually a transversal to the `P`-rows and the central `C`-columns
is either a `Q`-line or a central `H`-row. Here is an explicit
verification. Choose coordinates over `F_3` with

\[
C(t_{pq})=p+q,\qquad
H(t_{pq})=\varepsilon(p-q)+\delta.
\]

For the first assertion, write the set as `(p(q),q)`. Transversality
to `H` says that `p(q)-q` is a permutation. Every permutation of
`F_3` is affine with slope `±1`, so `p(q)` is either constant or
`-q+constant`. These are exactly the two claimed line types. The
dual assertion follows in the same way.

If `|A|≥7`, (3) and its dual give the required transversality
of both `U,V`; the prohibited `P,Q` alternatives leave a central
column for `U` and a central row for `V`.

Now suppose `|A|=6` and `U` is not transversal to the `Q`
profiles. The equality analysis after (3) gives two occupied cells
in every `P`-row and a full `Q`-column. The dual exceptional-row
argument forces `V` to be transversal to the `P`-rows: otherwise
at least four occupied cells would have to lie in one three-element
`G`-fiber. Thus `V` is a central row, since the `Q`-line alternative
is prohibited. It meets the full `Q`-column once, at a top successor
having no good extension from any top predecessor. This contradicts
activity. Hence `U` is transversal. The dual argument gives
transversality of `V`, proving that both are central lines also
when `|A|=6`.

These central lines meet every `P`-row and every `Q`-column.
A full occupied profile row would leave its top predecessor in
`U` inactive; a full column would leave its top successor in `V`
inactive. Every profile row and column therefore has at most two
occupied cells. In particular `|A|≤6`. At equality, each has
exactly two, so the missing cells form a perfect matching.

## At equality, both non-top neighbors are sharp

Continue with `|A|=6`. Write `C=k` for the central column `U`
and `H=l` for the central row `V`. If `k=l`, all nine endpoint
pairs have a central middle, contrary to activity. Thus `k≠l`.
All nine pairs are noncentral, and precisely the three missing
profile cells have good middle `c`. The other six have their
degree-four middles. Hence `g(c)=3`, one good pair per member of
`U` and of `V`.

Suppose `c` had only one sharp successor, leaving a nonsharp
successor `b∈B`. For every `t∈U`, the three-element fiber
`L_t^{-1}(c)` contains its one good top input and the sharp
successor. Its third element must be `b`. Thus

\[
t*b=c\qquad(t\in U).                              \tag{4}
\]

Choose a sharp predecessor `a∈A` of `b`, possible by surjectivity
of `F`. The `P`-line `TopPred(a)` meets the central column `U`
once. For their common top vertex `t`, sharpness gives `t*b=a`,
contradicting (4). Therefore both non-top successors of `c` are
sharp. The dual argument proves the same for its predecessors.

The subsequent [six-vertex exclusion](1485_three_central_six_four_exclusion.md)
rules out this last equality case analytically. This note supplies
its profile restrictions; the contradiction is in that later proof.

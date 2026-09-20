# Six degree-four vertices are impossible

Research note, 19 September 2026. This is an analytic proof, not yet
formalized in Lean.

**Theorem.** A finite E1485 magma with minimum degree three and
exactly three central vertices has at most five degree-four vertices.

The [degree-five profile theorem](1485_three_central_five_profiles.md)
already bounds their number by six. Assume equality. Write `A,B,C,D`
for the degree classes `4,n/4,5,n/5`, respectively. The
[degree-five necessity theorem](1485_three_central_requires_five.md)
gives `C≠∅` and `60|n`, so these classes are distinct.

We use the nine top vertices `t_pq=P_p∩Q_q`, with the three
unoccupied `A`-profile cells forming a perfect matching. Every
`c∈C` has top predecessors a central column `C(t)=k`, top
successors a central row `H(t)=l`, with `k≠l`, and two sharp
neighbors in each direction. Its three good top pairs form a
matching: precisely the three unoccupied profile cells in this
central-column/central-row rectangle.

## 1. At most three degree-five vertices

Fix `c∈C` with central labels `(k,l)`, and let `c'∈C` have
labels `(k',l')`. For `a_pq∈A`, the mixed products have unique
top middles, because `B` and `D` are distinct:

\[
a_{pq}*c=u_q\in Q_q\cap\{C=k\},\qquad
c'*a_{pq}=v_p\in P_p\cap\{H=l'\}.
                                                        \tag{1}
\]

E1485 gives

\[
u_q*(c*v_p)=c.                                          \tag{2}
\]

For fixed `p`, two values of `q` occur among the occupied cells.
If `c*v_p` were top, (2) would pair the same top successor of `c`
with two distinct top predecessors, contrary to its matching of
good pairs. Thus `c*v_p` is one of the two sharp successors of
`c` in `D`. As `p` ranges over three values, the entire central
row `H=l'` maps into those two values under `L_c`.

A sharp successor's fiber is its ordinary row and contains exactly
three top vertices. These two fibers are disjoint. They therefore
accommodate only six top inputs. Consequently at most two central
row labels `l'` occur among all members of `C`. The dual argument
bounds the number of central column labels `k'` by two.

A fixed label pair `(k',l')` determines at most one member of `C`,
because it determines its nonempty good-pair matching. Only pairs
with different labels occur. Two subsets of a three-element label
set, each of size at most two, admit at most three such off-diagonal
pairs: if both have size two they intersect, and otherwise their
Cartesian product has size at most two. Hence

\[
|C|\le3.                                               \tag{3}
\]

## 2. Every unoccupied profile cell has only degree-five or six outputs

Fix an unoccupied profile cell and label it `(0,0)`. Choose
coordinates over `F_3` with

\[
C(t_{pq})=p+q,\qquad
H(t_{pq})=\varepsilon(p-q)+\delta,
\quad\varepsilon\in\{1,-1\}.
\]

Write

\[
u_x=t_{0x},\qquad \beta_y=\varepsilon(y-\delta),\qquad
w_y=t_{\beta_y,0}.
\]

Then `C(u_x)=x` and `H(w_y)=y`. Its six noncentral pairs are
`(u_x,w_y)` with `x≠y`. Put `e=ε(y−x)`. The central-column
triple containing `w_y` has a second noncentral output `a_0e∈A`:
row zero has no other unoccupied profile cell.

The [nine-element fixed-parameter argument](1485_three_central_requires_five.md#3-six-point-packing-around-one-missing-cell)
applies without assuming degree five absent. That set contains the
ordinary row of `b=u_x*w_y` and the six top points

\[
S(x,y)=\{H=x\}\cup\{C=\beta_y\}\cup Q_e.                 \tag{4}
\]

Since `b` has three top successors, `d(b)−3≤3`. The cell is
noncentral and has no degree-four output, so `d(b)` is five or six.

If `d(b)=6`, its three non-top successors exhaust the remaining
positions in the fixed-parameter set. In particular

\[
TopSucc(b)\subseteq S(x,y),\qquad
F(a_{0e})\in Row(b).                                    \tag{5}
\]

The dual set gives

\[
TopPred(b)\subseteq
\{C=y\}\cup\{H=\delta-\varepsilon x\}\cup P_{y-x},
\qquad G(a_{y-x,0})\in Col(b).                          \tag{6}
\]

## 3. A degree-six output has only one good pair globally

First it has at most one good pair in this unoccupied profile cell.
Indeed (5) and (6) imply

\[
TopSucc(b)\cap Q_0\subseteq\{w_x,w_y\},\qquad
TopPred(b)\cap P_0\subseteq\{u_x,u_y\}.
\]

The pairs `(u_x,w_x)` and `(u_y,w_y)` are central. Thus the only
possible second good pair would be `(u_y,w_x)`. Let `z` be the
third central label. On the column `C=β_z`, the set `S(x,y)`
contains just the point with `q=e`, whereas `S(y,x)` contains
just the point with `q=−e`. These are distinct. But `b` must
have a top successor on that column, a contradiction.

This argument needs no assumption about the degrees of other
products in the cell, and applies to each of the three unoccupied
profile cells.

There is no additional top predecessor of `b` in `P_0`. If one
existed, it would have no good top extension: the only unoccupied
cell in its profile row is `(0,0)`, whose one good pair has already
been accounted for. Its three-element fiber at `b` would consist
of all three non-top successors of `b`, including `F(a_0e)`.
Yet sharpness gives `u*F(a_0e)=a_0e` for every `u∈P_0`, not `b`.
The dual argument gives

\[
TopPred(b)\cap P_0=\{u_x\},\qquad
TopSucc(b)\cap Q_0=\{w_y\}.                             \tag{7}
\]

The other two top successors of `b` both lie in `Q_e`. This follows
directly from (4): on column `C=β_x`, the `H=x` alternative is
the forbidden point `w_x`, leaving `q=e`; on column `C=β_z`,
there is already just one possible point, also with `q=e`.

Both these successors are inactive: if one belonged to a good top
pair with middle `b`, its profile cell would be the unique unoccupied
cell in column `e`. Applying (7) to that cell would say that `b`
has exactly one successor in `Q_e`, whereas it has two. Therefore
the displayed pair is the only good top pair with middle `b`,
globally.

## 4. Each directed three-cycle needs two degree-five outputs

Fix a nonzero `e`. Consider the three endpoint pairs

\[
(u_x,w_{x+\varepsilon e}),\qquad x\in F_3.               \tag{8}
\]

Suppose two of their products had degree six. By §3 they are
distinct, each with two inactive top successors in `Q_e`. By (6)
they have the common non-top predecessor

\[
b'=G(a_{\varepsilon e,0}).
\]

For an inactive successor `v` of either output `b`, the fiber
`R_v^{-1}(b)` has size three and no top input, so contains all
three non-top predecessors, including `b'`. Thus `b'*v=b`.
The two two-element successor sets overlap in the three-element
set `Q_e`; a common input would be mapped to both distinct outputs.
This is impossible.

At most one pair in (8) therefore has degree-six product. The other
two have degree-five products. Applying this to both nonzero values
of `e` gives at least four degree-five outputs among the six pairs
of this one unoccupied profile cell. Their central label pairs
`(x,y)` are distinct, so they are four distinct vertices of `C`.
This contradicts (3) and excludes `|A|=6`.

Together with the preceding bound of six, this proves `|A|≤5`.
Smaller degree-four classes are not excluded by this note.

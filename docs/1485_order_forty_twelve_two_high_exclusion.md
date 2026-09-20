# Order forty: twelve degree-five vertices cannot have two high-sharp partners

Research note, 20 September 2026. This is an analytic exclusion, with
no finite search, affine-profile assumption, or Lean theorem involved.
In the order-forty branch with degree-class sizes

\[
(|Z|,|A|,|B|,|T|)=(4,12,8,16),
\]

the sharp-degree distribution `(1,1,1,1,1,1,3,3)` on `B`
is impossible. It is excluded in both the single-coset and mixed-coset
profile cases.

The proof uses only the binary incidence data from the
[twelve-vertex profile note](1485_order_forty_twelve_high_profiles.md).
Let `D` be ordinary adjacency within `B`, and let `C_bd=1`
mean that `b⇒a⇒d` is a sharp path through a degree-five vertex.
If `j_b` is the sharp degree, then the row and column sums of
`D,C` are respectively `4−j_b,j_b`. Two necessary conditions are

\[
(D^2)_{bd}\ge2\ \Longrightarrow\ C_{bd}=1,
\qquad
j_b=j_d=3\ \Longrightarrow\ C_{bd}=1.                 \tag{1}
\]

The first follows because two internal two-step paths cannot both
be good; their only possible lower replacement has degree five.
The second is the [return-matching bound](1485_general_return_matching.md):
the two sharp degrees sum to six, exceeding the return-fiber sizes
five and four for products in `B,T`, so the product is in `A`.
All path counts below count distinct choices of the middle vertex;
loops are allowed throughout.

## 1. The two high vertices have prescribed low neighbors

Let `H` be the two vertices with sharp degree three and let
`L=B\H`, so `|L|=6`. Every high vertex has `D` in/out
degree one, and every low vertex has `D` in/out degree three.
The submatrix `C[H,H]` is all ones by (1).

Each high column of `C` therefore has precisely one additional
entry, in a low row. These two rows are distinct because each low
row of `C` has sum one. Call their set `P⊆L`, with `|P|=2`.
Dually, let `Q⊆L` be the two distinct low columns receiving the
additional `C` entries from the high rows. Thus

\[
C(p)\subseteq H\quad(p\in P),\qquad
C(b)\subseteq L\quad(b\in L\setminus P).             \tag{2}
\]

For `p∈P`, all entries of row `(D²)_p` are at most one.
Indeed, (1) permits a repeated endpoint only at the unique member
of `C(p)`, which is high; but a high endpoint has only one
internal predecessor and therefore cannot have two distinct middles.

If `p` had no high successor under `D`, its three successors
would all be low, giving `3·3=9` two-step paths. Their endpoints
would be distinct, impossible in the eight-element set `B`.
Hence each member of `P` has a high `D` successor. The total
`D` indegree of `H` is two, so these edges exhaust it, one from
each member of `P`, and they match `P` bijectively with `H`.

Applying the same argument to the transposed matrices gives

\[
\boxed{D\text{ matches }P\text{ to }H\text{ and }H\text{ to }Q;
\text{ these are all internal edges incident to }H.}     \tag{3}
\]

In particular, there are no internal high-to-high edges. A low
vertex has a high successor if and only if it belongs to `P`.

## 2. Every low vertex has exactly one successor in P

First consider `p∈P`. Its successors comprise one high vertex
and two low vertices, giving `1+3+3=7` two-step paths. Their
endpoints are distinct, as proved above. If neither of the two
low successors belonged to `P`, (3) would make all seven paths
end in the six-element set `L`: the high successor points into
`Q⊆L`, and the two low successors would have no high successors.
This is impossible. Thus `p` has a successor in `P`.

Now consider `b∈L\P`. Its three successors are low. Suppose
none belongs to `P`. By (3), all nine two-step paths from `b`
then end in `L`. By (1), only the single endpoint in `C(b)`
can be repeated, and its multiplicity is at most three because
there are only three possible middles. Thus the six low endpoints
can accommodate at most

\[
3+5\cdot1=8
\]

paths, contradicting nine. Consequently every low vertex has at
least one successor in `P`.

The six low vertices already contribute at least six edges into
`P`, whose total `D` indegree is exactly `2·3=6`. Therefore

\[
\boxed{|D(b)\cap P|=1\quad\text{for every }b\in L.}    \tag{4}
\]

No high vertex points into `P`; in particular (3) also gives
`P∩Q=∅`, though this disjointness is not needed below.

## 3. Four distinct sharp targets cannot fit in P

For each `b∈L\P`, its three `D` successors are low, and by
(4) each has exactly one successor in `P`. Thus there are exactly
three two-step paths from `b` with endpoint in the two-element
set `P`. Some endpoint is repeated. By (1), the unique member
of `C(b)` must consequently lie in `P`.

There are four vertices `b∈L\P`. Their `C` targets are
distinct: each target in `P` is a low vertex and therefore has
`C` column sum one. Four distinct targets cannot lie in the
two-element set `P`. This is the desired contradiction.

Hence the twelve/eight branch has at most one sharp-degree-three
vertex. Its only remaining sharp-degree distributions are

\[
\boxed{(1^5,2^2,3)\quad\text{or}\quad(1^4,2^4).}
\]

These two distributions, and therefore the complete order-forty
exclusion, are not settled by this note.

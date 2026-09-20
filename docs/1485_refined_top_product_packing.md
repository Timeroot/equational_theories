# Central-block packing inside a top translation fiber

Research note, 19 September 2026. These are unconditional finite
E1485 inequalities, not Lean declarations. They refine the
[single-column packing bound](1485_top_product_packing_bound.md).
Write `n=rs`, let `Z,T` be the central and top classes, and put
`P_t=Col(t)∩Z`, `C_t=Row(t)∩Z` for `t∈T`.

## 1. Pack an entire central predecessor block

Let `t→u` be an ordinary edge with both vertices top. Define

\[
V_t=\bigcup_{z\in P_t}Col(z),\qquad
F_t(u)=\{h:t*(u*h)=u\}.
\]

The fixed-parameter formula gives `|F_t(u)|=r²`. The columns
in `V_t` are pairwise disjoint: a common member `v` of columns
at distinct `z,z'∈P_t` would give two central middles from `v`
to `t`. Each column has size `r`, so

\[
|V_t|=r|P_t|.
\]

Central goodness in `z→t→u` gives `z*u=t` for every `z∈P_t`.
For `v∈Col(z)`, write `v=y*z`. E1485 gives

\[
t*(u*v)=(z*u)*(u*(y*z))=u.
\]

Absorption now gives `Row(u*v)⊆F_t(u)`. Since `v∈Row(u*v)`,
we conclude `V_t⊆F_t(u)`.

More generally, whenever `t*b=u`, absorption gives
`Row(b)⊆F_t(u)`. Every row meets each central column in exactly
one point, by unique goodness at a central endpoint. Consequently

\[
|Row(b)\cap V_t|=|P_t|.
\]

Counting the union inside `F_t(u)` proves

\[
\boxed{t*b=u,\quad t,u\in T
\quad\Longrightarrow\quad
d(b)\le r^2-(r-1)|P_t|.}                       \tag{1}
\]

In particular (1) applies to `b=u*w` whenever `w∈T` and
`C_w∩P_t≠∅`: the displayed E1485 identity gives `t*b=u`.
The corresponding statement with rows and columns interchanged
holds in the dual magma.

## 2. Every central label supplies a noncentral input

Fix an ordinary top edge `t→u` with `|C_u|<r`, and choose
`z∈P_t`. Exactly `|C_u|` members `w` of the `r`-element
column `Col(z)` have central product `u*w`.

Indeed each `c∈C_u` supplies the unique top middle `w=c*z`
of the central endpoint pair `(c,z)`. These are distinct, and
they exhaust the centrally valued inputs in that column. Thus
at least one input has noncentral product, and (1) gives

\[
\boxed{\exists w\in T,\qquad
r<d(u*w)\le r^2-(r-1)|P_t|.}                  \tag{2}
\]

This is local in the ordinary edge `t→u`. If no degree in this
interval occurs as a top product, that ordinary edge is impossible.
At minimum degree three, a top predecessor with two central
predecessors therefore forces a noncentral product of degree at
most five in the corresponding top row, provided the row element
has fewer than three central successors.

## 3. A complementary bound using the central successors of the output

For the same ordinary top edge, put

\[
W_u=\bigcup_{c\in C_u}Row(c).
\]

These central rows are pairwise disjoint, by uniqueness of central
middles from `u`. Since `t*c=u` for every `c∈C_u`, absorption
puts all of them inside `F_t(u)`. Hence `|W_u|=r|C_u|`.
Whenever `t*b=u`, union counting gives

\[
\boxed{d(b)\le r^2-r|C_u|+|Row(b)\cap W_u|.}  \tag{3}
\]

The last intersection consists of precisely those top successors
`x` of `b` for which `u*x` is central. In particular, if `b=u*w`
is noncentral, its top successor `w` is not in this intersection.
Choosing `z∈C_w` and `t=z*u` supplies the required top edge
and equation `t*b=u`. Thus

\[
d(u*w)\le r^2-r|C_u|+|TopSucc(u*w)|-1.        \tag{4}
\]

For minimum degree three and four central vertices, a top product
whose first factor has two central successors has degree at most
six: its top successor profile has at most four members. Dually,
the same bound holds when its second factor has two central
predecessors.

These inequalities do not by themselves force full core. Their
first complete branch consequence is the analytic
[four-central/ten-top exclusion](1485_four_central_ten_top_exclusion.md).

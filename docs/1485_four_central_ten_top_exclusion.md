# Four central vertices and ten top vertices are impossible

Research note, 19 September 2026. This is an analytic finite E1485
proof, not a Lean declaration. It excludes the entire ten-top branch
at minimum translation degree three, without an order restriction,
solver search, or finite incidence enumeration.

Suppose for contradiction that the minimum degree is three, the
central class `Z` has four vertices, and the top class `T` has ten.
The [central-incidence reduction](1485_four_central_residual.md)
gives two tops of profile `(2,2)`, called mids, and eight of profile
`(1,1)`, called lows. Write `P_t,C_t` for the central predecessor
and successor sets of a top vertex. Every such set has size one or
two, and

\[
|C_v\cap P_t|\le1\qquad(v,t\in T).
\]

The same analytic reduction proves that the least noncentral degree
is five or six. If it is five, degree-five vertices have one of two
forms: they are sharp-regular and never top-top products, or the
entire degree-five class is a singleton `{a}` with four-low top
predecessor profile

\[
U_\varepsilon
=\{L_{ij,i\oplus\varepsilon}:i,j\in\{0,1\}\}.
                                                        \tag{1}
\]

We show that neither alternative is possible.

## 1. A mid predecessor forces small top products

Fix a mid `t`, so `|P_t|=2`, and let `u∈TopSucc(t)`.
Put

\[
V=\bigcup_{z\in P_t}Col(z).
\]

Both columns in this union have three top vertices. They are
disjoint: if a top `v` belonged to both, then `C_v∩P_t` would
contain two central points, contrary to uniqueness. Thus `|V|=6`.

For any `z∈P_t`, central goodness of `z→t→u` gives `z*u=t`.
For any `v∈Col(z)`, choose `y` with `y*z=v`. E1485 gives

\[
t*(u*v)=(z*u)*(u*(y*z))=u.
\]

The fixed-parameter set

\[
F_t(u)=\{h:t*(u*h)=u\}
\]

has size nine, because `t,u` are both top. The absorption identity
puts `Row(u*v)⊆F_t(u)` for every `v∈V`. In particular
`V⊆F_t(u)`, since `v∈Row(u*v)`.

Fix any `w∈V` and write `b=u*w`. Its row is contained in
`F_t(u)` and meets each of the two columns `Col(z)`, `z∈P_t`,
in exactly one point: every path ending at a central vertex is
good and has a unique middle. The columns are disjoint, so
`|Row(b)∩V|=2`. Counting the union gives

\[
d(b)+6-2\le|F_t(u)|=9,
\qquad\boxed{d(u*w)\le5\quad(w\in V).}          \tag{2}
\]

## 2. Every top successor of a mid precedes a degree-five top product

Fix `z∈P_t`. Exactly `|C_u|` of the three inputs `w∈Col(z)`
give central-valued products `u*w`. Indeed, for each `c∈C_u`,
the central endpoint pair `(c,z)` has a unique top middle `w`;
these are precisely the central-valued inputs in that column.
Since `|C_u|≤2`, at least one such input is noncentral.

Its product has degree at most five by (2). The least noncentral
degree is at least five, so this product has degree exactly five.
This also excludes least noncentral degree six immediately.

Degree-five sharp-regular vertices cannot be top-top products: a
top translation fiber would contain their three sharp inputs and
also its top input. Therefore the regular degree-five alternative
is impossible.

In the remaining alternative every noncentral degree-five product
equals the single vertex `a` of (1). Applying the preceding argument
to every `u∈TopSucc(t)` gives

\[
TopSucc(t)\subseteq TopPred(a)=U_\varepsilon.     \tag{3}
\]

## 3. Two central labels cannot cover four

The canonical low labels have central successor sets

\[
C_{L_{ijk}}=\{(k,1-i)\}.
\]

For the four lows in `U_ε`, these sets cover only the two points

\[
\{(\varepsilon,1),(1\mathbin\oplus\varepsilon,0)\}.
\]

On the other hand, the central successor sets of the tops in
`TopSucc(t)` partition all four central vertices, by uniqueness
of paths from `t` to central endpoints. Inclusion (3) is therefore
impossible. This final contradiction excludes the ten-top branch.

The only remaining four-central configuration at minimum degree
three has nine tops; this proof makes no assertion that the
nine-top branch is impossible.

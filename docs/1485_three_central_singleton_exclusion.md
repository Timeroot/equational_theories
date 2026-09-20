# Three central vertices cannot have a singleton degree-four class

Research note, 19 September 2026. This is an analytic finite E1485
proof, without a solver or finite profile enumeration. It is not yet
formalized in Lean.

**Theorem.** If the minimum translation degree is three and there are
exactly three central vertices, then the degree-four class has at
least two vertices. In particular, its reciprocal class cannot be
a singleton.

The [three-central reduction](1485_three_central_minimum_top_output.md)
gives a nonempty degree-four class `A`, nine tops `t_ij=z_i*z_j`,
and exactly three top predecessors and successors at every vertex.
Every degree-four vertex has sharp degree one, permutation top
profiles, and six good ordered top endpoint pairs.

Suppose for contradiction that `A={a}`. Denote its top predecessor
and successor transversals by `U_a,V_a`. Both are permutation
transversals of the three-by-three top grid: each meets every grid
row and every grid column exactly once. Let

\[
K=\{(t_{ij},t_{kl}):j=k\},\qquad
G_a=(U_a\times V_a)\setminus K.
\]

The six pairs in `G_a` are exactly the top representations of `a`.

## 1. Each central-column triple contains a degree-four or degree-five output

Fix a top `u=t_ij` and a central label `z_l`. Put `t=z_l*u`.
E1485 gives

\[
u*Col(z_l)\subseteq L_t^{-1}(u).
\]

Both sides have size three. For the left side, multiplication by
`u` is injective on `Col(z_l)`: if two inputs gave the same output
`x`, they would give two middles in `x→Col(z_l)→z_l`, contrary
to central endpoint uniqueness. Thus

\[
S:=u*Col(z_l)=L_t^{-1}(u).                         \tag{1}
\]

The three outputs are the central vertex `z_j` and two distinct
noncentral vertices `x,y`.

Choose the smaller-degree one, say `d(x)≤d(y)`. For any
`v∈Row(x)`, absorption gives `Row(x)⊆F_t(u)`, so `u*v∈S`.
If `v` is non-top, `u*v` cannot be central, because every input
giving a central product is top. It also cannot equal `y`: the
path `u→x→v` would be bad, making `d(y)<d(x)`. Therefore all
non-top successors of `x` belong to `L_u⁻¹(x)`.

If `d(x)≥6`, there would be at least three such non-top
successors. Together with the original top input representing `x`,
they would overfill this three-element fiber. Hence

\[
\boxed{\min(d(x),d(y))\le5.}                      \tag{2}
\]

There are 27 triples (1), one for every `(u,z_l)`. If degree five
were absent, each triple would contain a degree-four output. But
`a` has only six top representations and thus belongs to only six
of these triples. This is impossible. Consequently degree five
must occur.

More generally, the same count proves that absence of degree five
would require `6|A|≥27`, and hence `|A|≥5`.

## 2. A degree-five profile has one or two good entries in every row and column

Fix a degree-five vertex `x`. Write `U=TopPred(x)` and
`V=TopSucc(x)`. The set `U` has exactly one top in each grid row;
the set `V` has exactly one in each grid column. A bad top path
through `x` has product of smaller degree, hence either a central
vertex or the single vertex `a`. Its good-pair matrix is therefore

\[
G=(U\times V)\setminus(K\cup G_a).                \tag{3}
\]

Each top fiber at `x` has size three. Its inputs lie in `Row(x)`,
which has only two non-top elements, so it must contain at least
one top input. Conversely it contains a sharp non-top input, so
it contains at most two top inputs. Dually the same applies to
columns. Thus every row and column of `G` has one or two entries.

## 3. A two-entry good row forces degree-four companion outputs

Suppose a row at `u=t_ij∈U` has two good inputs `w_1,w_2`.
For either input `w_s=t_kl`, the triple (1) consists of a central
output, `x`, and one other noncentral output `y_s`.

The fiber `L_u⁻¹(x)` already contains the two good top inputs.
But `x` has two non-top successors, so at least one of them is
not in that fiber. As in §1, its product under `L_u` belongs to
the same triple, cannot be central, and now cannot equal `x`.
It is consequently `y_s`, which has degree strictly less than five.
Thus `y_s=a`.

In grid coordinates the companion input is the other noncentral
input of the triple:

\[
w_s'=t_{hl},\qquad \{h\}=\{0,1,2\}\setminus\{j,k\}.
\]

We have proved

\[
\boxed{u\in U_a,\qquad w_1',w_2'\in V_a.}         \tag{4}
\]

The two inputs have distinct grid-column labels. Since `V_a` is
a permutation transversal, their companion inputs also have
distinct grid-row labels. Hence `w_1,w_2` have the two distinct
row labels other than `j`.

Consider the third member `w_3` of `V`. Its product under `u`
is bad. If its row label differed from `j`, that product would be
`a`, putting `w_3∈V_a`. But the two companion inputs in (4)
already occupy the two row labels other than `j` in `V_a`; its
remaining column must have row label `j`. This is a contradiction.
Therefore `w_3` has row label `j`, and it is precisely the third
member of `V_a`. In particular,

\[
V\text{ is a permutation transversal},\qquad
V\cap V_a=\{w_3\}.                               \tag{5}
\]

A second two-entry good row would satisfy the same conclusion,
and its left endpoint would belong to `U_a` with the same central
successor label `j`. The permutation property of `U_a` makes that
endpoint equal to `u`. Thus the other two good rows have one entry.
Because `V` is a permutation transversal, each of those rows has
two noncentral positions before removing `G_a`; losing a position
forces its left endpoint into `U_a`. Consequently `U=U_a`.

But the column at `w_3∈V_a` then has no good positions: each is
either central or a representation of `a`. This contradicts §2.
We conclude that **no good row has two entries**.

## 4. A matching good matrix is impossible as well

All three rows now have exactly one entry. Each column has at least
one, so the three columns also have exactly one.

If `U=U_a`, then every column has two noncentral positions before
removing `G_a`. To leave exactly one good position, every member
of `V` must belong to `V_a`. This gives `V=V_a`, making `G`
empty, a contradiction.

Otherwise choose `u∈U\setminus U_a`, and write `j` for its grid
column label. No position in its row belongs to `G_a`. Since
its good row has one entry, two members of `V` have grid-row
label `j`, and the third, called `w`, has a different row label.
At least one of those first two members, say `v`, lies outside
`V_a`, because `V_a` has distinct row labels.

No position in the column at `v` belongs to `G_a`. Its unique good
entry therefore forces exactly two members of `U` to have grid
column label `j`: these are `u` and some distinct `u'`. Both
`(u,w)` and `(u',w)` are noncentral. The former is good, so the
matching condition forces the latter into `G_a`.

The row at `u'` now has no good position: its two positions at
row-label `j` are central, while its position at `w` belongs to
`G_a`. This final contradiction excludes a degree-five vertex.

Section 1 forced degree five to occur. Hence the singleton assumption
was false, proving `|A|≥2`.

Finally, if the reciprocal degree class were a singleton, both sharp
maps from `A` to that class would be constant. Uniqueness of a good
middle on sharp two-edge paths makes the joint sharp-map pair
injective, forcing `|A|=1`. The reciprocal class therefore also has
at least two vertices.

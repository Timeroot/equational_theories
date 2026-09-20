# Four central vertices, nine tops, and least degree four are impossible

Research note, 19 September 2026. This is a finite E1485 proof with
an explicit small incidence enumeration. It is not a Lean theorem
and does not use SAT, an ATP, or enumeration of magma tables.

**Theorem.** A finite E1485 magma cannot have minimum translation
degree three, four central vertices, nine top vertices, and least
noncentral degree four. There is no restriction on the order or on
the number of degree classes.

The [degree-four reduction](1485_four_central_degree_four.md) shows
that the degree-four class and its reciprocal class are singletons
`A={a}`, `B={b}`, with `d(b)=n/4`. It also eliminates all central
incidence diagrams with equal central rows or columns. Exactly 24
of the 285 normalized labeled diagrams remain, forming six orbits
under central relabeling and duality.

Write `P_t,C_t⊆Z` for the central predecessor and successor sets of
a top `t`. These have size one or two. Let

\[
K=\{(u,v)\in T^2:C_u\cap P_v\ne\varnothing\}
\]

be the set of central-valued top products. It has 36 elements.
The singleton `a` has three top predecessors `U_a` and three top
successors `V_a`. Its six top representations are precisely

\[
G_a=(U_a\times V_a)\setminus K.
\]

We first constrain every possible degree-five top output, without
assuming such an output exists. The union of all possibilities
already proves too small for the ordinary top adjacency.

## 1. Exact degree-five neighbor balance

Suppose `x` has degree five. An ordinary neighbor `y` has
complementary degree `n/d(y)≤5`, and complementary degrees are
translation degrees. The only possibilities are three, four, and
five. They correspond, respectively, to top neighbors, the unique
vertex `b`, and sharp neighbors.

Let `I,O` be the top predecessor/successor counts, `k⁻,k⁺` the
sharp counts, and `ε⁻,ε⁺∈{0,1}` indicate whether `b` is an
ordinary predecessor/successor. Counting ordinary neighbors gives

\[
I+k^-+\varepsilon^-=O+k^++\varepsilon^+=5.
\]

Reciprocal neighbor balance, multiplied by `n`, says

\[
3I+5k^-+4\varepsilon^-
=3O+5k^++4\varepsilon^+.
\]

Eliminating the sharp counts yields
`2I+ε⁻=2O+ε⁺`. Since each `ε` is zero or one,

\[
\boxed{I=O=t,\quad k^-=k^+=k,\quad
\varepsilon^- =\varepsilon^+=\varepsilon=5-t-k\in\{0,1\}.}
                                                        \tag{1}
\]

The top profiles `U=TopPred(x)`, `V=TopSucc(x)` partition the
central labels via their `P` and `C` sets. Thus `2≤t≤4`, and
`1≤k≤3`.

## 2. Exact good-pair and fiber restrictions

Every path `u→x→v` with `u,v` top is either good, central-valued,
or has product `a`. Indeed a bad middle has strictly larger degree
than its endpoint product, and the only translation degrees below
five are three and four. Consequently the good pairs of `x` are
exactly

\[
\boxed{G_x=(U\times V)\setminus(K\cup G_a).}             \tag{2}
\]

For each `u∈U`, the fiber `L_u⁻¹(x)` has three elements. It
contains all `k` sharp successors of `x`. Its only possible
non-top, non-sharp element is `b`, and that is possible only if
`ε=1`. All its remaining elements are precisely the top inputs
counted by the row of `G_x`. The dual statement applies to columns.
Every row and column count of `G_x` therefore lies in

\[
\boxed{[3-k-\varepsilon,\ 3-k].}                        \tag{3}
\]

When `ε=1`, the
[variable-neighborhood slot bound](1485_three_central_minimum_top_output.md#a-general-top-fiber-slot-bound)
applied to the successor `b` says that `b` belongs to at least
`n/d(b)-d(x)+I=4-5+t=t-1` of these top fibers. After reserving
the `tk` sharp slots, this gives

\[
\boxed{|G_x|\le t(3-k)-\varepsilon(t-1).}               \tag{4}
\]

Equations (1)–(4), the partition conditions on `U,V`, and
`G_x≠∅` form the complete filter used below. It is deliberately
an overapproximation: possible profiles are not required to
coexist, have disjoint good sets, or extend to a magma.

## 3. An ordinary top edge forces many small products

Suppose `t→u` is an ordinary top edge and `|P_t|=2`. Put

\[
W_t=\bigcup_{z\in P_t}Col(z).
\]

The two central columns have size three and are disjoint: an
intersection would give two central middles between a top vertex
and `t`. Thus `|W_t|=6`, and

\[
w\in W_t\quad\Longleftrightarrow\quad C_w\cap P_t\ne\varnothing.
\]

Central goodness gives `z*u=t` for every `z∈P_t`. For
`w=y*z∈Col(z)`, E1485 gives `t*(u*w)=u`. The absorption identity
then puts `Row(u*w)` inside the nine-element fixed-parameter set

\[
F_t(u)=\{v:t*(u*v)=u\}.
\]

Also `W_t⊆F_t(u)`. The row of `u*w` meets each of the two
central columns in exactly one point, by central endpoint
uniqueness. Counting the union inside `F_t(u)` gives

\[
d(u*w)+6-2\le9,
\qquad\boxed{d(u*w)\le5\quad(w\in W_t).}              \tag{5}
\]

This is the same refined packing argument used in the
[ten-top exclusion](1485_four_central_ten_top_exclusion.md#1-a-mid-predecessor-forces-small-top-products).
It requires neither a least-degree-five hypothesis nor any
classification of the other degree classes.

## 4. The finite incidence contradiction

For each of the 24 remaining diagrams, enumerate every candidate
`(U,V,k)` satisfying (1)–(4), and form the set

\[
L=K\cup G_a\cup\bigcup_{\text{candidates}}G_x.
\]

This contains **every** top pair whose actual product has degree
at most five. By (5), an ordinary top edge `t→u` must satisfy

\[
|P_t|=1\quad\text{or}\quad
\forall w\in T,\ (w,t)\in K\Longrightarrow(u,w)\in L.  \tag{6}
\]

Call the pairs satisfying (6) allowed edges. Actual top adjacency
is a subset of this allowed relation. But central endpoint
uniqueness requires both of the following coverage conditions:

- For every top `t` and central `z`, some successor `u` has
  `z∈C_u`.
- For every top `u` and central `z`, some predecessor `t` has
  `z∈P_t`.

The executable check finds a violation of at least one coverage
condition in **each** of the 24 diagrams. No search for a complete
ordinary adjacency matrix is needed. In terms of its conventional
blocks `B,C,D`, even the supports of `DC=J` and `BD=J` cannot
be satisfied.

The reproducible command is

```text
python3 scripts/1485_m4h9_degree_four_exclusion.py
```

The script imports the original exhaustive 285-diagram generator
and the earlier parameter-sharing test. Its final checks are run
on all 24 labeled survivors; canonicalization is used only for
this summary table. The degree-five pair cover counts exclude
the 36 central pairs and six degree-four pairs.

| Central rectangle table | Degree-five candidate profiles | Degree-five pair cover | Failed coverage |
| --- | ---: | ---: | --- |
| `01HH/CDHH/C2AA/BD3B` | 14 | 24 | Row |
| `01HH/CDAA/C2HH/BD3B` | 10 | 18 | Row |
| `AA01/CDHH/C2HH/BD3B` | 6 | 13 | Row |
| `AA01/HDHC/H2HC/3DBB` | 2 | 6 | Row |
| `AA01/HDHC/H2HC/BD3B` | 14 | 24 | Column |
| `AA01/HDCH/H2CH/3DBB` | 7 | 12 | Row |

Across the 24 labeled diagrams, the candidate-count histogram is
`{2:2, 6:2, 7:8, 10:2, 14:10}`. Their simultaneous incompatibility
with (6) proves the theorem.

The remaining mathematical assumption is not a conjectural spectrum
exclusion or an unavailable solver certificate: every analytic
reduction is given above or in the linked singleton note, and the
finite incidence lemma is directly executable. Kernel formalization
of these arguments and of the enumeration remains to be done.

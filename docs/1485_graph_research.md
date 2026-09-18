# E1485: counting good-path-reflecting Boolean quotients

Research note, 17 September 2026. This proves a conditional finite-spectrum
theorem and several unconditional finite-structure results: sharp neighbors
exist; translations have uniform nonempty fibers; every row and column at
the same element have equal size; and central vertices exist and are exactly
the minimum-degree vertices. In particular all odd prime orders are excluded.
**It does not prove that every finite E1485 magma admits the quotient required
below, or settle the complete square/twice-square conjecture.** The constant-row
classification used here is proved in
[the main research note](1485_spectrum_research.md).

## The quotient condition

Let `M` and `Q` be nonempty finite E1485 magmas, and let
`π : M → Q` be a surjective homomorphism. In the associated directed graphs,
write `x → y` when `y = x * z` for some `z`. A two-edge path
`x → y → z` is good when `y = x * z`.

Assume that `π` **reflects goodness**: whenever `x → y → z` and
`π(y) = π(x) * π(z)`, we have `y = x * z`. This is stronger than being a
homomorphism. Preservation of goodness is automatic; reflection is not.
No additional edge-lifting condition or assumption about adjacency between
fibers is used.

Assume also that `Q` has a constant row. The classification gives distinguished
elements `0,1`, a Boolean algebra structure, and a Boolean automorphism `σ`
of order dividing five such that

\[
  a*b=\neg(\sigma a\wedge\sigma^{-1}b),
  \qquad 0*a=a*0=1.
\]

Put `T(a)=a*1`. Thus

\[
 T(a)=\neg\sigma a,\qquad T^2(a)=\sigma^2a,
 \qquad 1*T(a)=a,\qquad a*T^2(a)=T(a). \tag{1}
\]

The identity `a*T²(a)=T(a)` does not actually require the classification:
the main note proves `T³(a)*a=1` and
`u*v=1 ⇒ v*(z*u)=T(v)`. Taking `u=T³(a)`, `v=a`, and `z=1`
gives it immediately, since `1*T³(a)=T²(a)`. Consequently the
uniform-square-fiber part of the following theorem uses only those short
constant-row identities; the classification is needed only to identify
the cardinality of `Q` as a power of two.

### Theorem

Every fiber of `π` has the same square cardinality `r²`, for a positive
integer `r`. In particular

\[
  |M|=r^2|Q|=r^2 2^m
\]

for some nonnegative integer `m`, so `|M|` is a square or twice a square.

## Proof

For each `a ∈ Q`, let `Fₐ=π⁻¹(a)` and `nₐ=|Fₐ|`. These sets are
nonempty. Let `Aₐᵦ` be the zero-one adjacency matrix from `Fₐ` to `Fᵦ`.
Whenever `b=a*c`, unique existence of good paths and reflection give

\[
 A_{ab}A_{bc}=J_{n_a,n_c}. \tag{2}
\]

Indeed, the matrix product counts all two-edge paths with middle vertex in
`Fᵦ`; every such path is good by reflection, and the unique good path is
always one of them by the homomorphism property.

First treat the distinguished fibers. Put

\[
 B=A_{10},\qquad C=A_{01},\qquad D=A_{11}.
\]

The four products of `0` and `1` are
`0*0=0*1=1*0=1` and `1*1=0`. Equation (2) therefore gives

\[
 BC=J_{n_1,n_1},\quad CB=J_{n_0,n_0},\quad
 DB=J_{n_1,n_0},\quad CD=J_{n_0,n_1}. \tag{3}
\]

The rectangular trace identity gives `n₀=n₁=k`. Now all three matrices
are square, and write `J=Jₖ,ₖ`. From `BC=CB=J` it follows that
`BJ=JB` and `CJ=JC`. Thus `B` and `C` each have constant row and
column sums, say `b` and `c`. Furthermore

\[
 BJ=B(CD)=(BC)D=JD,
 \qquad JC=(DB)C=D(BC)=DJ.
\]

Consequently all columns of `D` sum to `b`, and all rows sum to `c`.
Counting its entries by rows and columns gives `kb=kc`, hence `b=c=r`.
Taking row sums in `BC=J` gives

\[
  k=r^2. \tag{4}
\]

This argument remains valid when `0=1`: there is then only one fiber and
the repeated names refer to the same matrix. Nonemptiness and (4) give
`r≥1`.

For arbitrary `a ∈ Q`, the equations `0*a=1` and `a*0=1` give

\[
 C A_{1a}=J_{k,n_a},\qquad
 A_{a1}B=J_{n_a,k}. \tag{5}
\]

Since `C` has column sums `r`, summing any column of the first equality
shows that every column of `A₁ₐ` sums to `k/r=r`. Since `B` has row
sums `r`, the second equality shows that every row of `Aₐ₁` sums to
`r`.

Write `Pₐ=Aₐ,ₜ₍ₐ₎`. The equations `a*1=T(a)` and `1*T(a)=a`
give

\[
 P_a A_{T(a),1}=J_{n_a,k},\qquad
 A_{1a}P_a=J_{k,n_{T(a)}}. \tag{6}
\]

The row sums of `Aₜ₍ₐ₎,₁` are `r`, so the first equality makes every
row sum of `Pₐ` equal to `k/r=r`. The column sums of `A₁ₐ` are
`r`, so the second equality makes every column sum of `Pₐ` equal to
`r`. In particular, counting its entries gives `nₐ=nₜ₍ₐ₎`.

Finally, `a*T²(a)=T(a)` from (1) and (2) give

\[
 P_aP_{T(a)}=J_{n_a,n_{T^2(a)}}. \tag{7}
\]

Both matrices on the left have row sums `r`. Taking row sums of (7)
gives `nₜ²₍ₐ₎=r²`. Since `T` is a permutation, this proves the
assertion for every fiber. The finite Boolean algebra `Q` has `2ᵐ`
elements, completing the proof.

## Scope and remaining problem

This includes all constant-row models (take the identity quotient), all
central groupoids (take the one-element quotient), and the high/low family
in the main note (take the two-element NAND quotient). It also includes
any good-path-reflecting quotient onto a cyclically twisted Boolean model,
so the order-32 example is not an obstruction to this theorem.

The missing general step is structural: does every finite E1485 magma
admit a good-path-reflecting quotient with a constant row? This is a
proposed reduction, **not an established fact**. Nor is the theorem a
statement about arbitrary homomorphic quotients: the proof uses reflection
precisely in (2).

## Central vertices: unconditional local lemmas

Call `a` a **central vertex** if every two-edge path with middle vertex
`a` is good. Equivalently,

\[
 (x*a)*(a*y)=a\quad\text{for all }x,y. \tag{C}
\]

This is a property of one element, not the assertion that the whole magma
is a central groupoid. It is also equivalent to each of

\[
 a*((a*x)*y)=a*x, \tag{L}
\]
\[
 (x*(y*a))*a=y*a. \tag{R}
\]

Thus every path starting or ending at a central vertex is good as well.
These equivalences require no finiteness assumption:

- (L) implies (C): use (W) with its left-hand-side variable `a`, middle
  variable `x`, and final variable `a*y`. The resulting equality is
  `(x*a)*(a*((a*y)*x))=a`, and (L) simplifies the second factor.
- (C) implies (L): apply the dual identity to obtain
  `((y*a)*(a*x))*((a*x)*y)=a*x`, and simplify the first factor by (C).
- (C) implies (R): (W) gives
  `(x*(y*a))*((y*a)*(a*x))=y*a`, and (C) simplifies the second factor.
  Dualizing the first implication gives (R) implies (C).

Write `Row(a)={a*x}` and `Col(a)={x*a}`. If `a,b` are central, then

\[
 u\longmapsto u*b:\operatorname{Row}(a)\longrightarrow\operatorname{Col}(b),
 \qquad v\longmapsto a*v
\]

are inverse bijections, by (L) at `a` and (R) at `b`. In particular
all central vertices have the same row and column cardinality `r` in a
finite magma. Even if `y` is not central, the first map from
`Row(a)` to `Col(y)` is injective by (L); dually `Col(a)` injects
into every row. Therefore, **if a central vertex exists**, its row and
column sizes are the global minimum.

Fix such an `a`, and define

\[
 B_a=\{u*v:u\in\operatorname{Row}(a),\ v\in\operatorname{Col}(a)\}.
\]

For `c=u*v` in this set, (L) and (R) give

\[
 a*c=u,\qquad c*a=v. \tag{8}
\]

Hence `(u,v)↦u*v` is injective, and `|Bₐ|=r²` in the finite case.
Every central vertex `b` belongs to `Bₐ`, since (C) at `b` gives
`b=(a*b)*(b*a)`. Thus the number of central vertices is at most
`r²`. The map

\[
 p_a(x)=(a*x)*(x*a)
\]

is a retraction onto `Bₐ`: equation (8) gives `pₐ(c)=c` for
`c∈Bₐ`.

The existence of finite central vertices and the assertion that every
minimum-row vertex is central are **proved later in this note** using
sharp edges and uniform fibers. The following stronger assertion remains
**unproved**: in a finite model, every element of `Bₐ` is central.

This assertion holds in the examined finite examples but is false
without finiteness, as the next section shows. In particular the displayed
retraction is not claimed to be a homomorphism.

## Why rectangle closure cannot be proved purely equationally

The existing greedy-completion theorem supplies an infinite counterexample
to the unrestricted assertion that every element of `Bₐ` is central.
Use the five-vertex relaxed weak central groupoid from the
[blueprint chapter](../blueprint/src/chapter/weak_central_groupoids.tex),
with adjacency matrix

\[
 \begin{pmatrix}
 1&1&0&0&1\\
 1&1&0&1&0\\
 0&0&1&1&1\\
 1&0&1&0&0\\
 0&1&1&0&0
 \end{pmatrix}.
\]

The only bad two-edge paths are

```text
(0,0,0), (0,0,1), (0,1,1), (1,0,0), (1,1,0), (1,1,1).
```

This is the blueprint's actual six-bad-path version: `(2,2,2)` is good.
It has 13 edges and 29 good paths and satisfies existence of a good path
between every ordered pair, good extensions at both ends of every edge,
and the five-cycle rule. These are the relaxed-model hypotheses; they
were also independently checked by exhaustive enumeration here.

Start with five distinct lifts, denoted by their base labels, and retain
only these six edges:

```text
2 → 3,  3 → 0,  0 → 4,  4 → 2,  0 → 0,  0 → 1.
```

The good paths in this finite partial extension are exactly

```text
(0,0,4), (0,4,2), (2,3,0), (3,0,0),
(3,0,1), (3,0,4), (4,2,3).
```

Their ordered endpoint pairs are distinct, so uniqueness of good paths
holds. The two remaining paths `(0,0,0)` and `(0,0,1)` are bad.
The five-cycle rule is inherited from the base. Thus this is a valid
finite partial extension, and the greedy theorem completes it to a
countable E1485 magma, preserving and reflecting goodness over the base.

Let `a` be the retained lift of 2, let `u,v` be the lifts of 3 and 4,
and let `b` be the lift of 0. Every path whose image contains 2 is good
in the base. Consequently `a` is a central vertex of the completion.
The good four-cycle in the seed gives

\[
 a*b=u,\qquad b*a=v,\qquad u*v=b,\qquad v*u=a.
\]

Hence `b∈Bₐ`. But the retained bad path `0 → 0 → 1` starts at
`b`, so `b` is not central. This establishes the counterexample.

Accordingly any finite rectangle-closure proof must genuinely use
finiteness. Longer first-order equational searches with only (W) and a
central-element hypothesis cannot prove this unrestricted target.

## Experimental check of a possible canonical quotient

A concrete proposed reduction is: choose an element `a` whose row has
minimum size, and quotient by the congruence generated by identifying all
elements of `Row(a)`. The quotient automatically has a constant row, so
the only additional condition needed for the theorem is reflection of
goodness.

The archived model banks were checked directly, first verifying (W) for
each complete table. The outcome is:

| Order | Tables checked | Minimum row size | Quotient order | Minimum-row choices checked |
|---|---:|---:|---:|---:|
| 8 | 1 (Boolean NAND) | 1 | 8 | 1 |
| 8 | 9 | 2 | 2 | 36 |
| 16 | 180 | 2 | 4 | 720 |
| 18 | 200 | 3 | 2 | 1800 |

All 2,557 choices gave goodness-reflecting quotients. All also satisfied
(L), so their minimum-row vertices were central. Congruence closure took
at most two synchronous rounds of closure under left and right
translations, with equivalence closure after each round.

This is experimental support, **not a general proof or an exhaustive
search at orders 16 or 18**. The order-16 portable archive actually contains
180 entries, despite its historical filename saying “181”.

Do not assume that these quotients split: order-eight model number 9 in
Kevin M's bank has no two-element NAND subalgebra at all, despite having a
goodness-reflecting quotient onto NAND. Thus a proof by choosing an
internal copy of the proposed Boolean quotient would need additional
justification.

A second, choice-free candidate comes from **sharp edges**. Write
`a ⇒ u` when `a*(u*x)=u` for every `x`. By (W) this is
equivalent to `(x*a)*u=a` for every `x`; the converse follows from
the dual identity. Explicitly,

\[
 (x*a)*(a*(u*x))=a,
 \qquad ((x*a)*u)*(u*x)=u.
\]

Either condition implies the ordinary edge `a → u`. If
`a ⇒ u ⇒ v`, then `v=u*x` for some `x`, whence `a*v=u`.
Therefore every sharp two-edge path is good, and the square of the sharp
adjacency matrix is zero-one.

On all 390 examined tables, the equivalence relation generated by pairs
with a common sharp predecessor or a common sharp successor was already
a magma congruence, and its quotient was goodness-reflecting. No subsequent
closure under multiplication added identifications. It gave exactly the
quotient orders in the table above. Every sharp in-degree and out-degree
was the listed minimum row size.

Also experimentally, the relation `R` of being connected by two sharp
edges was compatible with multiplication and difunctional: any two of
its nonempty rows were equal or disjoint. These are **unproved structural
targets**, not assumptions in the cover theorem. If they can be established
in general, the relation `RRᵀ` becomes a promising canonical congruence.

## Finite sharp successors and predecessors: a proved theorem

Every element of a nonempty finite E1485 magma has at least one sharp
successor and at least one sharp predecessor. Here is a full equational
and finite-set proof; it does not assume central vertices exist.

We first record the absorption identity

\[
 x*((x*y)*(y*z))=x*y. \tag{9}
\]

It follows from two applications of the dual law (D):

\[
 \begin{aligned}
 x*((x*y)*(y*z))
 &=\bigl(((y*z)*x)*(x*y)\bigr)*((x*y)*(y*z))\\
 &=x*y.
 \end{aligned}
\]

Fix `a`, and for each `b` define the transformation
`P_b(t)=a*(t*b)`. Identity (W) says

\[
 (b*a)*P_b(t)=a. \tag{10}
\]

If `u=P_b(t)`, applying (D) with its distinguished variable `u`,
middle variable `b`, and final variable `a` gives

\[
 ((b*a)*u)*(u*b)=u.
\]

Together with (10) this yields `P_b(u)=u`. Thus

\[
 P_b^2=P_b. \tag{11}
\]

Now put `u=P_b(t)` and `v=P_c(u)=a*(u*c)`. Apply (9) with
`x=b*a`, `y=u`, and `z=c`. Using (10), it gives

\[
 (b*a)*v
 =(b*a)*\bigl(((b*a)*u)*(u*c)\bigr)
 =(b*a)*u=a.
\]

A further application of (D), now with distinguished variable `v`,
gives `a*(v*b)=v`. Equivalently,

\[
 \boxed{P_bP_cP_b=P_cP_b.} \tag{12}
\]

Composition is read right to left. Equations (11) and (12) are universal:
they hold in infinite models too. They are the fixed-left
right-regular-band identities. For completeness, they extend from the
generators to the semigroup they generate. In a word of generators, any
earlier occurrence of a repeated letter can be deleted: prove
`p U p=U p` inductively on the length of `U`, using
`p q p=q p` to insert `p` immediately before the last letter of
`U`, then shorten the intervening word. Consequently each word equals
the word retaining only the last occurrence of each generator, and the
whole semigroup satisfies `F²=F` and `FGF=GF`.

Only a simpler common-fixed-point argument is needed here. Start at any
element `t`, and apply `P_b` once for every `b∈M`, in any
order. Whenever `u` is already fixed by `P_b`, equation (12) says

\[
 P_b(P_c(u))=P_bP_cP_b(u)=P_cP_b(u)=P_c(u).
\]

Thus applying a new transformation preserves every previously obtained
fixed-point condition. Equation (11) gives the new fixed-point condition.
After this finite list of transformations, the result is fixed by all
`P_b`. It therefore belongs to

\[
 K(a)=\{u: a*(u*b)=u\text{ for every }b\}
      =\bigcap_b \operatorname{im}(P_b). \tag{13}
\]

This is exactly the set of sharp successors of `a`, and is nonempty.
The equality with the intersection of images follows because each
`P_b` is idempotent. The dual magma also satisfies E1485, so the same
argument gives a sharp predecessor of every vertex.

The composition of one copy of every `P_b` is, in fact, a retraction
onto the canonical set `K(a)`: it maps everything into `K(a)`,
and every generator fixes every point of `K(a)`. Consequently the
minimum rank of the fixed-left generated semigroup is exactly
`|K(a)|`. This does **not** identify that rank with the minimum row
size of the magma.

### Rigorous degree bounds; equality remains open

Let `k(a)` and `h(a)` denote the numbers of sharp successors and
predecessors of `a`. For any `b`, the map

\[
 K(a)\longrightarrow\operatorname{Col}(b),\qquad u\longmapsto u*b
\]

is injective, with left inverse `v↦a*v`, directly by sharpness.
Dually, the sharp predecessors of any vertex inject into every ordinary
row. Therefore, writing `r_L=min_x |Row(x)|` and
`r_R=min_x |Col(x)|`,

\[
 1\le k(a)\le r_R,\qquad 1\le h(a)\le r_L. \tag{14}
\]

Also, if `u,v∈K(a)` have a common ordinary successor `y`, then
`u=a*y=v`. Thus their ordinary row sets are disjoint. Dually, the
ordinary columns of distinct sharp predecessors of a fixed vertex are
disjoint. Hence

\[
 k(a)r_L\le |M|,\qquad h(a)r_R\le |M|. \tag{15}
\]

In matrix form, if `A` is ordinary adjacency and `B` is sharp
adjacency, both `AB` and `BA` are zero-one matrices, entrywise
bounded above by the all-ones matrix. Indeed a two-edge path is good as
soon as either one of its edges is sharp, so its middle vertex is unique.

These bounds do not yet establish equality of the sharp degrees with the
minimum ordinary degree. The equality `r_L=r_R` and centrality of
minimum-degree vertices are proved below by additional counting arguments;
they do not follow just from the common-fixed-point construction.

## Sharp edges give exact rectangular factorizations

There is a stronger counting theorem. For every sharp edge `e ⇒ a`,
the maps

\[
 \Phi:M\longrightarrow\operatorname{Row}(a)\times\operatorname{Col}(e),
 \qquad x\longmapsto(a*x,x*e),
\]
\[
 \Psi(u,v)=u*v
\]

are inverse bijections. This statement needs **no finiteness assumption**.

First, even an ordinary edge `e → a` makes `Φ` injective.
Write `a=e*t`. The dual identity gives

\[
 (a*x)*(x*e)=((e*t)*x)*(x*e)=x. \tag{16}
\]

For surjectivity, let `u=a*x` and `v=y*e`.
Sharpness and its dual form give `e*u=a` and `v*a=e`.
Applying (W) and (D), respectively, gives

\[
 \begin{aligned}
 a*(u*v)&=(e*u)*(u*(y*e))=u,\\
 (u*v)*e&=((a*x)*v)*(v*a)=v.
 \end{aligned} \tag{17}
\]

This proves the bijection.

### Uniform fibers of every finite translation

The sharp-successor/predecessor theorem supplies a sharp predecessor
`e` for every `a`. Under the displayed bijection, left
multiplication by `a` is first-coordinate projection. Hence
**every nonempty fiber of left multiplication by `a` has the same
cardinality** `|Col(e)|`. Similarly, every vertex `e` has
a sharp successor `a`; all nonempty fibers of right multiplication
by `e` have cardinality `|Row(a)|`.

Thus, for `n=|M|`, `r(a)=|Row(a)|`, and
`c(a)=|Col(a)|`,

\[
 \boxed{\text{every nonempty }L_a\text{-fiber has size }n/r(a),\quad
        \text{every nonempty }R_a\text{-fiber has size }n/c(a).} \tag{18}
\]

In particular **every row size and every column size divides `n`**.
At this stage these are uniformity theorems for each translation
separately. The next section proves `r(a)=c(a)`, and hence equality of
the left- and right-fiber sizes at the same element.

### Sharpness is exactly the tight cardinality case

For every ordinary edge `e → a`, injection (16) gives

\[
 n\le r(a)c(e). \tag{19}
\]

For finite models, equality holds **if and only if the edge is sharp**.
The forward direction from sharpness is the factorization above. Conversely,
if equality holds, the injection `Φ` is bijective, and (16)
shows its inverse is multiplication. Consequently

\[
 a*((a*x)*(y*e))=a*x \quad\text{for all }x,y. \tag{20}
\]

Use (W) with distinguished variable `a`, middle variable
`y*e`, and final variable `a*x`. Simplification by (20) gives

\[
 ((y*e)*a)*(a*x)=a. \tag{21}
\]

Write `a=e*t`. For any `w`, the dual identity gives

\[
 ((t*w)*e)*a=((t*w)*e)*(e*t)=e.
\]

Taking `y=t*w` in (21) therefore yields `e*(a*x)=a`,
which is precisely sharpness. We have proved

\[
 \boxed{e\Rightarrow a
 \quad\Longleftrightarrow\quad
 e\to a\ \text{ and }\ r(a)c(e)=n.} \tag{22}
\]

Thus in finite E1485 models the sharp graph can be recovered from the
ordinary adjacency graph and its row and column degrees alone.

Finally, the existence of sharp neighbors and (22) give exact extremal
relations:

\[
 \boxed{
 (\min_a r(a))(\max_a c(a))=n
 =(\max_a r(a))(\min_a c(a)).
 } \tag{23}
\]

For example, every sharp successor of `e` has row size
`n/c(e)`; conversely every row size arises at a sharp successor.
The analogous statement holds for columns. This proves (23), but does not
by itself identify the two minimum degrees.

## Row/column balance and finite central vertices

The preceding results prove the remaining equality of the left- and
right-fiber sizes. They also prove that **every nonempty finite E1485 magma
has a central vertex, and its central vertices are exactly the elements
of minimum row size**.

Let `e ⇒ a` be a sharp edge. Sharpness gives the exact fiber identity

\[
 L_e^{-1}(a)=\operatorname{Row}(a). \tag{24}
\]

Indeed, if `x=a*y`, then `e*x=a` by sharpness. Conversely,
`e*x=a` makes `e → a → x` the good path associated to
the product, so `x∈Row(a)`.

Uniformity (18) therefore gives `r(a)=n/r(e)`. On the other hand,
the sharp rectangular factorization gives `n=r(a)c(e)`. Cancelling
the positive factor `r(a)` proves `r(e)=c(e)`.
Every vertex has a sharp successor, so

\[
 \boxed{r(x)=c(x)\quad\text{for every }x\in M.} \tag{25}
\]

Write this common degree as `d(x)`, and put
`d_min=min_x d(x)`, `d_max=max_x d(x)`.
Equation (23) becomes

\[
 d_{\min}d_{\max}=n. \tag{26}
\]

Now choose any vertex `e` of minimum degree, and consider any
ordinary edge `e → a`. The inequality (19) and the maximum-degree
bound give

\[
 n\le d(a)d(e)=d(a)d_{\min}\le d_{\max}d_{\min}=n.
\]

Thus equality holds, so (22) makes this edge sharp. Every outgoing edge
of `e` is therefore sharp: every two-edge path beginning at `e`
is good. By (L) and its proved equivalence with (C), `e` is a central
vertex.

Conversely, the earlier injection argument already showed that every
central vertex attains the minimum row and column degree. We have proved

\[
 \boxed{
 x\text{ is central}\quad\Longleftrightarrow\quad d(x)=d_{\min}.
 } \tag{27}
\]

In particular the equal-fiber theorem can now be stated without a
left/right qualification: **all nonempty fibers of either translation at
`x` have the same size `n/d(x)`**.

These arguments use finiteness essentially, first to produce sharp
neighbors and then to turn tight cardinality into surjectivity. They do
not contradict the infinite rectangle-closure counterexample above.

### Prime orders

A finite E1485 magma of prime order has a constant row or column:
choose a sharp edge and use the factorization `n=r(a)c(e)`.
One factor must be one. The constant-row/column classification therefore
forces its order to be a power of two. Consequently **the only prime in
the finite spectrum is 2**.

In particular the exclusions of orders 11 and 13 have a mathematical proof
here, independent of the reported SAT computations. This note does not
itself replace any pending Lean declarations.

## Exact ranks of the individual mixed projections

For arbitrary `x,y`, there is an exact description of the image
of the idempotent transformation `L_xR_y`:

\[
 \operatorname{im}(L_xR_y)
 =\{u:(y*x)*u=x\}. \tag{28}
\]

The inclusion from left to right is (W). Conversely, if
`(y*x)*u=x`, the dual identity gives

\[
 u=((y*x)*u)*(u*y)=x*(u*y),
\]

which exhibits `u` in the image. The right-hand side of (28) is a
nonempty fiber of `L_{y*x}`, so the uniform-fiber theorem gives

\[
 \boxed{
 \operatorname{rank}(L_xR_y)=\frac{n}{d(y*x)}\ge d_{\min}.
 } \tag{29}
\]

The two mixed transformations `L_xR_y` and `R_yL_x`
have bijective images: the maps are `R_y` and `L_x`,
using their idempotence. They therefore have equal ranks.

If `a` is central, then every `a*x` has maximum degree,
because `a ⇒ a*x`. Thus for every fixed `x` there is an
individual projection of minimum rank:

\[
 \operatorname{rank}(L_xR_a)=d_{\min}. \tag{30}
\]

The distinction between an individual projection and an arbitrary product
is important. The preceding argument proves that the minimum rank among
the generators `L_xR_y`, for fixed `x`, is `d_min`.
It does not yet prove the same lower bound for products of generators.
Their common image `K(x)` could a priori be smaller. Establishing
that no further rank drop occurs would prove that every sharp out-degree
is `d_min`; duality would give the corresponding in-degrees.

A concrete stronger target is that, for a central vertex `h`,

\[
 \operatorname{im}(L_aR_h)=K(a).
\]

Equivalently, one would prove
`a*((a*(x*h))*y)=a*(x*h)` for all `a,x,y`. Equation (30)
already gives this generator image cardinality `d_min`; what is missing
is that every other generator fixes it pointwise. This assertion remains
**unproved for finite models**, and it must not be inferred from the rank
calculation. Without finiteness it is false, by the following explicit seed.

Use the five-color relaxed structure from the rectangle-closure section,
with eight distinct seed vertices:

| Vertex | A | X | H | V | U | Y | T | F |
|---|---|---|---|---|---|---|---|---|
| Color | 0 | 1 | 2 | 3 | 1 | 3 | 1 | 4 |

Retain exactly the edges of the four good product paths

\[
 X*H=V,\qquad A*V=U,\qquad U*Y=T,\qquad A*T=F.
\]

There are no two good paths with the same endpoints in this seed. Its good
two-edge paths are precisely the four displayed ones, together with
`U→V→H` and `F→T→Y`. The other two-edge path `A→U→T` is bad, with colors
`(0,1,1)`. Every seed edge is supported by a displayed good product path.
The greedy completion therefore gives an E1485 magma in which `H` is
central (its color is 2), but

\[
 A*((A*(X*H))*Y)=F\ne U=A*(X*H).
\]

In particular no purely equational proof of this proposed projection lemma
from (W) and centrality can succeed. A finite proof would need additional
counting or stabilization beyond the universal identities.

One proposed shortcut is actually false even in finite models:
`p(x,y)=x` does not imply `d(x)≤d(y)`. In the twisted order-32
model, using the main note's bit labeling, `p(3,8)=3`, but
`d(3)=4>2=d(8)`. Thus a degree-monotonicity argument using the
pair relation must incorporate additional hypotheses.

### Image intersections: a narrower finite target

For fixed `a`, write `I_b=im(L_aR_b)`. The band identities prove

\[
 \operatorname{im}(P_bP_c)=I_b\cap I_c.
\]

Indeed `P_b` preserves the fixed points of `P_c`, and conversely;
the composite lands in both images and fixes their intersection. Thus a
sufficient finite condition for uniform sharp degrees is that **the family
`{I_b:b∈M}` is closed under binary intersections**. Its finite total
intersection would then itself be a generator image, of size at least
`d_min` by (29), while (14) gives the opposite inequality.

This closure holds in the 390 archived models and the twisted order-32
model, but remains **unproved in general**. Do not replace it by closure
of the transformations themselves: compositions need not equal a generator
even in order-eight examples.

Uniform fibers do not supply an abstract shortcut either. For central
`h`, `P_h=L_aR_h` does have uniform fibers of size `n/d_min`:
centrality makes `L_a` injective on `Col(h)`, since `(a*v)*h=v`
there. But the two transformations

```text
P = (1,1,3,3),   Q = (1,2,1,2)
```

on `{1,2,3,4}` are uniform rank-two idempotents satisfying both band
identities, while both composites are constant. This is an abstract
transformation example, not an E1485 magma; it shows exactly why additional
magma structure is needed.

Even actual mixed projections can be nonuniform: in order-eight bank
model index 2 (zero-based), `a=2,b=3` gives
`P_b=(4,4,4,5,4,5,4,4)`, of minimum rank two but fiber sizes six and
two. The always-valid formula is

\[
 |P_b^{-1}(u)|=\frac{n}{d(b)}
     |\operatorname{Col}(b)\cap L_a^{-1}(u)|.
\]

It follows by counting the equally sized fibers of `R_b`; the intersection
on the right need not have cardinality independent of `u`.

## A mixed adjacency identity

Let `A` be the ordinary adjacency matrix and `B` the sharp adjacency
matrix. The products `AB` and `BA` have entries in `{0,1}`: any path
containing a sharp edge is good, so its middle vertex must be `a*c`.
More precisely,

\[
 (AB)_{ac}=1\iff (a*c)\Rightarrow c,
 \qquad
 (BA)_{ac}=1\iff a\Rightarrow(a*c).
\]

The required other ordinary edge always exists by the definition of the
operation graph. Since `B` is a subrelation of `A`, these descriptions
also give the entrywise identity

\[
 \boxed{B^2=(AB)\cap(BA).} \tag{31}
\]

Here the intersection is of the corresponding zero-one relations, not
ordinary matrix multiplication. This identity is universal and does not
require finiteness. It does not by itself establish transitivity of any
of these relations or identify a Boolean quotient.

## Reproducible finite-table checks

[1485_structure_check.py](../scripts/1485_structure_check.py) checks the
rectangular inverse maps, uniform fibers, tight-edge characterization,
row/column balance, central/minimum-degree equivalence, and mixed-rank
formula directly on supplied tables. With no arguments it checks the
twisted Boolean model of order 32. It accepts these public archives:

- [Kevin M's ten order-eight tables](https://raw.githubusercontent.com/bafflingbits/brute1485/main/n8_unique.txt).
- [Order-sixteen portable archive](https://leanprover.zulipchat.com/user_uploads/3121/yhypw8DyvXPuEzeZlCVfcgXT/Mace4-1485-size-16-181-models-isofilter-portable.txt), containing 180 tables.
- [Order-eighteen portable archive](https://leanprover.zulipchat.com/user_uploads/3121/j7VDLA59M2XUUMvGWY78WM3M/Mace4-1485-size-18-200-models-portable.txt), containing 200 tables.

After downloading them, run, with the actual local paths:

```sh
python3 scripts/1485_structure_check.py n8_unique.txt n16-models.txt n18-models.txt
```

All 390 archived tables and the additional twisted order-32 model passed.
The script separately labels the observed sharp-degree regularity and
square cardinality of the central set as empirical: neither is proved
in general here. These regression checks support, but do not replace,
the mathematical proofs and are not exhaustive searches or Lean checks.

## Further finite consequences (18 September)

The [two-degree note](1485_two_degree_research.md) develops the weighted
balance identity into sharp-degree moment equations and a five-cycle bound.
It excludes all orders `2p` for odd primes, all `3p` for primes `p>3`,
and all odd prime cubes, and sharpens the general distinct-semiprime bound.
These are pen-and-paper proofs, not new catalogue assertions.

The [projection note](1485_image_research.md) proves that every nontrivial
step of the fixed-left projection semigroup strictly decreases translation
degree. It also isolates why this does not yet give the required rank lower
bound. The full square/twice-square converse is still unproved here.

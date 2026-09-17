# E1485: counting good-path-reflecting Boolean quotients

Research note, 17 September 2026. This proves a conditional finite-spectrum
theorem. **It does not prove that every finite E1485 magma admits the quotient
required below.** The constant-row classification used here is proved in
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

Three further assertions remain **unproved**:

1. Every nonempty finite E1485 magma has a central vertex.
2. Every minimum-row vertex in a finite model is central (a stronger
   proposed assertion).
3. In a **finite** model, every element of `Bₐ` is central.

The third assertion holds in the examined finite examples but is false
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

The observed equalities `k(a)=h(a)=r_L=r_R` are not established by
these bounds. In particular common fixed points do not by themselves
show that a minimum-row vertex is central.

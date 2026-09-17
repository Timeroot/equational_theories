# E1485 with involutive squaring: the pair relation needs finiteness

Research note, 17 September 2026. The finite square/twice-square spectrum
conjecture remains open. This note establishes an obstruction to one proposed
proof route: **involutive squaring does not, for arbitrary infinite models,
make the pair relation below transitive, compatible with multiplication, or
goodness-reflecting.** Explicit finite certificates produce countable
counterexamples through the existing greedy construction.

These are not finite counterexamples. The corresponding properties hold in
all 390 examined finite tables of orders 8, 16, and 18. Thus the results below
identify places where a proof of the proposed finite reduction must use
finiteness. No Lean source, axiom, or implication-board entry is changed.

## 1. The relation and its unconditional identities

Write

\[
 (y*x)*(x*(z*y))=x \tag{W}
\]

and use its established dual

\[
 ((y*z)*x)*(x*y)=x. \tag{D}
\]

Define

\[
 s(x)=x*x,\qquad p(x,y)=(y*x)*(x*y),\qquad
 R(x,y)\iff p(x,y)=x\ \text{and}\ p(y,x)=y.
\]

The additional identity E151 is `s(s(x))=x`.

The following two path identities follow from (W) and (D):

\[
 a*((a*b)*(b*c))=a*b,\qquad ((a*b)*(b*c))*c=b*c. \tag{1}
\]

For the first, replace the initial `a` by `((b*c)*a)*(a*b)` using (D),
then apply (D) again. For the second, replace the final `c` by
`(b*c)*(c*(a*b))` using (W), then apply (W) again.

Consequently

\[
 p(x,y)*y=x*y,\qquad x*p(y,x)=x*y. \tag{2}
\]

Three further identities require no E151 assumption:

\[
 \begin{aligned}
 p(x,p(y,x))&=p(x,y),\\
 p(p(x,y),y)&=p(x,y),\\
 p(p(x,y),p(y,x))&=p(x,y). \tag{3}
 \end{aligned}
\]

The first follows by expanding `p` and applying (2) to both factors. For
the second put `q=p(x,y)` and `a=x*y`. Identity (D) gives `q*(a*y)=a`,
while (W) gives `(y*q)*(q*(a*y))=q`; use (2) to identify the result with
`p(q,y)`. Finally the first identity gives `p(y,q)=p(y,x)`, and the first
and second identities together give the third.

There is also the useful chain identity

\[
 ((z*x)*(x*y))*((x*y)*(y*w))=x*y. \tag{4}
\]

Indeed put `q=(z*x)*(x*y)`, `a=x*y`, `b=y*w`. By (1), `q*y=a`.
Two instances of (D) now give `(b*q)*a=q` and
`((b*q)*a)*(a*b)=a`, proving (4).

Let `T(x,y)=(x*y,y*x)` and let `S(x,y)=(y,x)`. Substituting in (4)
gives

\[
 T^3=ST,\qquad T^5=T. \tag{5}
\]

Here `S` commutes with `T`. Since `R(x,y)` is equivalent to
`T²(x,y)=S(x,y)`, equation (5) proves

\[
 \boxed{R=\operatorname{im}T.} \tag{6}
\]

In particular, every reversed-product pair `(a*b,b*a)` lies in `R`, and
every pair in `R` has that form. The map
`(x,y)↦(p(x,y),p(y,x))=T⁴(x,y)` is a retraction onto `R`.

The relation is always symmetric. Its reflexivity is exactly E151, because
`p(x,x)=s(s(x))`. Moreover, **transitivity of `R` alone would imply
E151**: every element is a product by (W), so (6) makes `R` serial;
a symmetric, serial, transitive relation is reflexive. The converse is
false in countable models, as shown below.

## 2. A countable construction from finite certificates

The construction is the one implemented by
`RelaxedVeryWeakCentralGroupoid.Greedy.exists_extension` in
[WeakCentralGroupoids.lean](../equational_theories/WeakCentralGroupoids.lean).
Here is the precise version used in this note.

Let `B` be a finite set of colors, `P` a directed relation on `B`, and
`G(a,b,c)` a ternary relation specifying allowed good paths. Assume:

1. Every ordered pair `(a,c)` admits at least one `b` with `G(a,b,c)`.
2. `G(a,b,c)` implies `P(a,b)` and `P(b,c)`.
3. `G(a,b,c)`, `G(c,d,e)`, and `P(e,a)` imply `G(b,c,d)`.

Start with a finite directed graph on distinct vertices in `B×ℕ`, whose
edges respect `P`. Require that for each ordered pair of vertices there is
at most one two-edge path whose color triple belongs to `G`. Such a graph
is called a consistent seed here.

Enumerate all ordered pairs of `B×ℕ`. If a pair `u,v` has no allowed
good path, choose an allowed middle color and a fresh vertex `w` of that
color, and add `u→w→v`. This preserves consistency: the only new
two-edge path with old endpoints and new middle is the intended one;
paths with the fresh vertex as an endpoint have a uniquely determined
middle. The union therefore has exactly one allowed good path between
every ordered pair. Define `u*v` to be its middle vertex.

Condition 3 proves (W), by applying the five-cycle rule to the product
paths defining `y*x` and `x*(z*y)`. The carrier `B×ℕ` is countably
infinite, and every good path required in the seed continues to define
the same product.

For E151, impose the additional finite condition

\[
 G(a,b,a)\iff G(b,a,b). \tag{7}
\]

If `v=u*u`, then `u→v→u` is good. Its reverse return path
`v→u→v` has the same edges and is good by (7), so uniqueness gives
`v*v=u`. Thus every resulting magma satisfies E151.

One graph detail matters: arbitrary seed edges need not be edges of the
eventual magma's associated graph. **Every edge used below belongs to an
explicitly required good product path.** Such an edge is an actual magma
edge, since a product `a*c=b` supplies both `a→b` and `b→c`.

## 3. A three-color certificate: transitivity and compatibility fail

For colors `0,1,2`, the following entry `M[a,c]` lists all allowed middle
colors `b`, meaning `G(a,b,c)`:

| `a \ c` | 0 | 1 | 2 |
|---|---|---|---|
| 0 | `{2}` | `{2}` | `{0}` |
| 1 | `{2}` | `{1,2}` | `{1}` |
| 2 | `{0}` | `{1}` | `{0,1}` |

Take exactly the edges occurring in these good triples:

\[
 0\to0,2;\qquad 1\to1,2;\qquad 2\to0,1.
\]

The appendix verifies totality, (7), and all `3⁵=243` instances of the
five-cycle rule. These entries describe a relaxed structure, not a
three-element E1485 magma.

### Failure of transitivity

Take seven distinct vertices with colors

| Vertex | X | Y | Z | U | V | W | T |
|---|---|---|---|---|---|---|---|
| Color | 0 | 1 | 2 | 2 | 2 | 1 | 1 |

Use the edges of the two directed four-cycles

\[
 X\to U\to Y\to V\to X,\qquad
 Y\to W\to Z\to T\to Y.
\]

Every two-edge path within either four-cycle is good. The seed is
consistent, as is also checked in the appendix. Its extension therefore
satisfies

\[
 X*Y=U,\quad Y*X=V,\quad U*V=Y,\quad V*U=X,
\]

and the analogous four equalities for `Y,Z,W,T`. Hence `R(X,Y)` and
`R(Y,Z)`.

But both `X*Z` and `Z*X` have color `0`, by the table. Their product
`p(X,Z)` consequently has color `2`, whereas `X` has color `0`.
Thus `p(X,Z)≠X`, and `R(X,Z)` fails. The one-sided relation
`p(x,y)=x` is not transitive either.

### Failure of multiplication compatibility

Use a separate seed over the same three-color certificate. Its seven
distinct vertices have colors

| Vertex | X | Y | Z | U | V | A | B |
|---|---|---|---|---|---|---|---|
| Color | 2 | 1 | 0 | 1 | 1 | 0 | 2 |

Require the good paths expressing

\[
 X*Y=U,\quad Y*X=V,\quad U*V=Y,\quad V*U=X,
 \qquad Z*X=A,\quad Z*Y=B.
\]

This seed is consistent. It gives `R(X,Y)`, but `A` has color `0` and
`B` color `2`, so the preceding color argument gives `p(A,B)≠A`.
Consequently

\[
 R(X,Y)\quad\text{but}\quad\neg R(Z*X,Z*Y).
\]

Thus even compatibility under one fixed left translation fails. Taking
the opposite magma also gives failure under a fixed right translation:
(D) ensures that opposites remain E1485 magmas, and both E151 and the term
`p` are unchanged by passing to the opposite operation.

### A short proposed central-vertex term also fails

The candidate `c(y)=(y*(y*y))*(y*(y*y))` was central in all 390 finite
tables examined, but it is not universally central under E151.

Use distinct vertices `X,Y,S,T,C,U,Z,V,D` with colors
`2,1,1,2,0,0,2,0,2`, respectively. The good-path requirements

\[
 Y*Y=S,\quad Y*S=T,\quad T*T=C,\quad
 X*C=U,\quad C*Z=V,\quad U*V=D
\]

form a consistent seed. In its extension, `c(Y)=C`, but
`(X*C)*(C*Z)=D≠C`. This refutes only that proposed term, not the
existence of some central vertex.

### Why this particular three-color obstruction cannot be finite

There is no finite strict realization of this three-color certificate in
which all three colors occur. Thus the use of infinity in these examples
is necessary, not merely an artifact of the construction.

Suppose such a realization exists, and let `n₀,n₁,n₂>0` be its color
fiber sizes. Write the six possibly nonzero adjacency blocks as

\[
 A_{00}=D,\quad A_{11}=E,\quad A_{02}=B,\quad
 A_{20}=C,\quad A_{12}=F,\quad A_{21}=G.
\]

Unique existence of allowed good paths gives, among other equations,

\[
 \begin{gathered}
 BC=J_{00},\quad BG=J_{01},\quad FC=J_{10},\\
 E^2+FG=J_{11},\quad CB+GF=J_{22},\quad
 EF=J_{12},\quad GE=J_{21}. \tag{8}
 \end{gathered}
\]

Here `Jᵢⱼ` is the all-ones `nᵢ×nⱼ` matrix. Let `eᵢ,fᵢ` denote
row sums of `E,F`, and `e'ⱼ,g'ⱼ` column sums of `E,G`. Computing `E³`
on its two sides gives

\[
 E J_{11}-J_{12}G=J_{11}E-FJ_{21},
\]

so `eᵢ+fᵢ=e'ⱼ+g'ⱼ=r` for a common nonnegative integer `r`.
From `F(CB+GF)=FJ₂₂`, using (8), we get

\[
 FJ_{22}=J_{10}B+J_{11}F-EJ_{12}.
\]

Hence every column sum of `B` plus the corresponding column sum of `F`
equals `r`. Now `B(CB+GF)=BJ₂₂` becomes
`J₀₀B+J₀₁F=BJ₂₂`, so every row sum of `B` is `r`.
Similarly, `(CB+GF)G=J₂₂G` gives

\[
 J_{22}G=CJ_{01}+GJ_{11}-J_{21}E,
\]

so every row sum of `C` plus the corresponding row sum of `G` is `r`.

Taking row sums in `BC=J₀₀` and `BG=J₀₁` together now yields
`r²=n₀+n₁`. On the other hand, combine row sums in the equations
`E²+FG=J₁₁`, `EF=J₁₂`, and `FC=J₁₀`. Their combined left side
has row sums

\[
 E(\operatorname{rows}(E)+\operatorname{rows}(F))+
 F(\operatorname{rows}(C)+\operatorname{rows}(G))
 =r^2\mathbf 1,
\]

whereas the right side has row sums `n₀+n₁+n₂`. Thus `n₂=0`, a
contradiction. This excludes finite realizations of this certificate;
it does not show that every hypothetical finite failure of `R` would
admit this three-color description.

## 4. A five-color certificate: goodness reflection fails

Use the following allowed middle sets, with `P` again consisting exactly
of the edges occurring in allowed good triples:

| `a \ c` | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| 0 | `{1}` | `{2}` | `{0}` | `{2}` | `{1}` |
| 1 | `{4}` | `{0}` | `{0}` | `{4}` | `{1}` |
| 2 | `{1}` | `{1}` | `{3}` | `{3}` | `{1,3}` |
| 3 | `{4}` | `{2}` | `{3}` | `{2,4}` | `{3}` |
| 4 | `{0}` | `{0}` | `{0,3}` | `{3}` | `{3}` |

The appendix verifies the construction's conditions, including all
`5⁵=3,125` five-cycle instances.

Take eight distinct vertices `X,Y,Z,Q,U,V,A,B` with respective colors
`0,0,0,1,2,4,2,2`. Require the good paths expressing

\[
 \begin{gathered}
 X*A=Y,\qquad Y*B=Z,\qquad X*Z=Q,\\
 Y*Q=U,\qquad Q*Y=V,\qquad V*U=Y,\qquad U*V=Q.
 \end{gathered}
\]

The seed is consistent. The first two products give actual magma edges
`X→Y→Z`. The last four products give `R(Y,Q)`, while `X*Z=Q≠Y`.
Therefore

\[
 X\to Y\to Z,\qquad R(Y,X*Z),\qquad Y\ne X*Z.
\]

This refutes the proposed reflection implication for arbitrary E1485+E151
magmas. It is not a claim about a quotient in this example: the relation
need not be a congruence. It refutes precisely the local implication that
would give reflection if the finite relation were proved to be a congruence.

## 5. What remains open in this route

For **finite** E1485+E151 magmas, the present work neither proves nor
refutes transitivity, compatibility, or goodness reflection of `R`.
The 390 archived tables satisfy all three properties, and their quotients
are Boolean NAND magmas. The conditional counting theorem in
[the graph research note](1485_graph_research.md) would apply once the
required quotient properties were established in general.

The countable counterexamples explain why equational or unrestricted Horn
proof searches for these implications cannot succeed. Additional finite
counting, stabilization, or another specifically finite argument is required.
The weaker identity `p(p(x,y),x)=p(x,y)` remains unproved in this work;
it should not be conflated with transitivity, and no counterexample to it
is claimed here.

## Appendix: reproducible finite certificate check

The following standalone Python uses only the standard library. It checks
both relaxed structures and all four seeds, including the uniqueness
condition needed by the greedy construction. It also checks the color
obstruction used for transitivity and compatibility. These are finite
checks supporting the supplied countable-construction proof, not Lean
kernel verification of a new theorem.

```python
from itertools import product

M3 = [
    [{2}, {2}, {0}],
    [{2}, {1, 2}, {1}],
    [{0}, {1}, {0, 1}],
]
M5 = [
    [{1}, {2}, {0}, {2}, {1}],
    [{4}, {0}, {0}, {4}, {1}],
    [{1}, {1}, {3}, {3}, {1, 3}],
    [{4}, {2}, {3}, {2, 4}, {3}],
    [{0}, {0}, {0, 3}, {3}, {3}],
]

def certificate(M):
    n = len(M)
    G = {(a, b, c) for a, c in product(range(n), repeat=2)
         for b in M[a][c]}
    P = {(a, b) for a, b, c in G} | {(b, c) for a, b, c in G}
    assert all(M[a][c] for a, c in product(range(n), repeat=2))
    assert all(((a, b, a) in G) == ((b, a, b) in G)
               for a, b in product(range(n), repeat=2))
    for a, b, c, d, e in product(range(n), repeat=5):
        if (a, b, c) in G and (c, d, e) in G and (e, a) in P:
            assert (b, c, d) in G
    return G, P

def seed(M, colors, triples):
    G, P = certificate(M)
    E = {(a, b) for a, b, c in triples}
    E |= {(b, c) for a, b, c in triples}
    assert all((colors[a], colors[b]) in P for a, b in E)
    assert all((colors[a], colors[b], colors[c]) in G
               for a, b, c in triples)
    for a, c in product(range(len(colors)), repeat=2):
        middles = [b for b in range(len(colors))
                   if (a, b) in E and (b, c) in E
                   and (colors[a], colors[b], colors[c]) in G]
        assert len(middles) <= 1

# X,Y,Z,U,V,W,T; the two good four-cycles.
seed(M3, [0, 1, 2, 2, 2, 1, 1], [
    (0, 3, 1), (1, 4, 0), (3, 1, 4), (4, 0, 3),
    (1, 5, 2), (2, 6, 1), (5, 2, 6), (6, 1, 5),
])
# X,Y,Z,U,V,A,B; compatibility.
seed(M3, [2, 1, 0, 1, 1, 0, 2], [
    (0, 3, 1), (1, 4, 0), (3, 1, 4), (4, 0, 3),
    (2, 5, 0), (2, 6, 1),
])
# X,Y,S,T,C,U,Z,V,D; the proposed central term.
seed(M3, [2, 1, 1, 2, 0, 0, 2, 0, 2], [
    (1, 2, 1), (1, 3, 2), (3, 4, 3),
    (0, 5, 4), (4, 7, 6), (5, 8, 7),
])
# X,Y,Z,Q,U,V,A,B; reflection with actual edge witnesses.
seed(M5, [0, 0, 0, 1, 2, 4, 2, 2], [
    (0, 1, 6), (1, 2, 7), (0, 3, 2), (1, 4, 3),
    (3, 5, 1), (5, 1, 4), (4, 3, 5),
])
p_colors = set().union(*(M3[u][v]
    for u in M3[2][0] for v in M3[0][2]))
assert p_colors == {2}  # p(x,z) cannot have color 0 when x=0,z=2.
print("All relaxed-structure and seed certificates pass.")
```

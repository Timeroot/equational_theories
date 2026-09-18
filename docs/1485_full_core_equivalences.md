# Equivalent forms of the remaining finite central-core conjecture

Research note, 18 September 2026. Let `M` be a nonempty finite E1485
magma of order `n`, with minimum and maximum translation degrees `r,s`,
so `n=rs`. Let `Z` and `T` be the central and top classes, and put
`m=|Z|`, `t=|T|`. The results below are reductions, not a proof of
any of the equivalent conjectural properties in general.

The [full-core quotient theorem](1485_full_core_quotient.md) already
proves square-or-double-square order assuming `m=r²`.

## Full core, sharp regularity, and the extreme class counts

The following conditions are equivalent:

1. `m=r²`.
2. Sharp adjacency is `r`-regular in both directions.
3. `Σ_x d(x)=n Σ_x 1/d(x)`.
4. `|T|=|Z|`.
5. Every product of two top vertices is central.

The [sharp-degree defect theorem](1485_sharp_degree_defect.md) proves
the equivalence of 2 and 3. The
[full-core sharp-regularity theorem](1485_full_core_sharp_regularity.md)
proves 1 implies 2. Conversely, if all top vertices have `r` central
neighbors in both directions, their central incidence counts give

\[
tr=mr,\qquad tr^2=m^2.
\]

Thus `t=m=r²`, proving 2 implies 1. Under 1, the same incidence
argument gives 4. Conversely, write `k_u^+≤r` for the central
out-degree of each top vertex. The identity `Σ_u k_u^+=rm`,
together with `t=m`, forces every `k_u^+=r`. Its dual forces
every `k_u^-=r`; the second moment again gives `m=r²`.

Condition 1 implies 5 by the
[top-rectangle count](1485_full_central_core.md). Conversely, the
central rectangle at any central `h` consists of `r²` products
of top vertices. Condition 5 makes them all central, so `m≥r²`;
the established opposite inequality gives equality.

## Reversing a central product

The same conditions are equivalent to

\[
\boxed{u*v\in Z\quad\Longrightarrow\quad v*u\in Z
\quad\text{for every }u,v.}                     \tag{1}
\]

Under full core, a central product `u*v` has top endpoints, and
5 applies to their reverse product. Conversely, fix central `h`.
For `u∈Row(h)` and `v∈Col(h)`, centrality gives `v*u=h`.
Equation (1) would therefore make every element `u*v` of the
`r²`-element central rectangle central. This proves full core.

Thus proving symmetry of central-valued products is sufficient to
finish the spectrum by this route. It is a genuinely finite target:
the [existing countable counterexample](1485_graph_research.md#why-rectangle-closure-cannot-be-proved-purely-equationally)
has `v*u=h` central but `u*v` noncentral.

For top `u,v`, the uniform-rank formula also says

\[
u*v\in Z
\iff \operatorname{rank}(L_vR_u)=s.
\]

The desired symmetry asks to transfer this *maximal-rank* condition
to `L_uR_v`. It does not assert equality of those ranks for arbitrary
products; that stronger assertion is false in twisted Boolean models.

## An exact count of the asymmetric central-valued pairs

Let `B` and `C` be the central-to-top and top-to-central incidence
matrices, and put `K=CB`. This is the zero-one matrix on `T` whose
entry `K_uv` is one precisely when `u*v` is central. Central
endpoint uniqueness gives `BC=J_m`.

Write `k^-=B^T1` and `k^+=C1`. The ordinary central row and
column sizes are `r`, so

\[
\sum_{u,v}K_{uv}=r^2m,\qquad
K^2=k^+(k^-)^T,\qquad
\operatorname{tr}(K^2)=m^2.
\]

Because `K` is zero-one, its trace-square counts ordered pairs for
which both products are central. Subtraction gives

\[
\boxed{\#\{(u,v)\in T^2:u*v\in Z,\ v*u\notin Z\}
=m(r^2-m).}                                    \tag{2}
\]

In particular `K` is symmetric exactly when full core holds. In
Frobenius norm the same identity is

\[
\|K-K^T\|_F^2=2m(r^2-m).
\]

The [incidence counterexample](1485_central_incidence_obstruction.md)
shows why the basic central/top matrix identities alone cannot make
this defect vanish. Additional finite multiplication information is
still required.

## A one-variable equivalent target: squares of top elements

Write `S(x)=x*x`. Exactly `m` top elements have central square:

\[
\boxed{|\{t\in T:S(t)\in Z\}|=m.}                 \tag{3}
\]

Indeed this cardinality is `tr(K)=tr(CB)=tr(BC)=m`.
There is also a concrete bijection: squaring sends each central `z`
to a top element `S(z)` and satisfies `S²(z)=z`. Conversely, if
`S(t)=z` is central, the ordinary path `z→t→z` is good because
its endpoints are central, so `S(z)=t`. Thus squaring exchanges `Z`
with precisely this subset of `T`.

It follows from the extreme-class equivalence above that

\[
\boxed{|Z|=r²\quad\Longleftrightarrow\quad
S(t)\in Z\text{ for every }t\in T.}               \tag{4}
\]

This is a simpler statement of the remaining conjecture, not a proof
of it. It still genuinely uses maximal degree; it does not assert
that every square is central or that squaring is globally involutive.

In a finite model one also has `T=Z*Z`. The inclusion from right to
left follows because products with central factors are top. Conversely,
each top `t` has central sharp neighbors `z⇒t⇒w`; that path is
good, giving `t=z*w`. Thus (4) is equivalently the two-central-element
target

\[
S(z*w)\in Z\quad\text{for all }z,w\in Z.          \tag{5}
\]

Even (5) cannot be proved without a finite hypothesis. In the same
five-color relaxed graph used for the known infinite counterexample,
retain seven edges on five distinct lifts:

```text
2 → 3,  3 → 0,  0 → 4,  4 → 2,  0 → 0,  0 → 1,  1 → 0.
```

Their good paths have unique middles for their ordered endpoints, and
every retained edge is supported by a good product path. The regression
script verifies these conditions, so greedy completion gives a countable
E1485 magma. The lifts `3,4` are central, while the retained good paths
give `3*4=0` and `0*0=1`. The bad path `1→0→0` shows that `1`
is not central. Hence `S(3*4)` is not central. This counterexample
does not address the finite statement (5).

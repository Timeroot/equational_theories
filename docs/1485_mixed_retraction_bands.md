# Mixed-coordinate bands: local identities and an infinite obstruction

Research note, 20 September 2026. These are algebraic facts and a
countable counterexample, not a proof of the finite spectrum conjecture.
The counterexample below also satisfies involutive squaring, E151.

Write

\[
\lambda_{a,b}(x)=(a*x)*(x*b).
\]

## The two one-parameter families are right-regular bands

The standard path identities give

\[
a*\lambda_{a,b}(x)=a*x,\qquad
\lambda_{a,b}(x)*b=x*b.
\]

Consequently every `λ_{a,b}` is idempotent. Fixing either parameter
also gives the right-regular-band identities

\[
\begin{aligned}
\lambda_{a,b}\lambda_{a,c}\lambda_{a,b}
 &=\lambda_{a,c}\lambda_{a,b},\\
\lambda_{a,b}\lambda_{c,b}\lambda_{a,b}
 &=\lambda_{c,b}\lambda_{a,b}.
\end{aligned}                                                   \tag{1}
\]

Composition is read from right to left. For the first identity, restrict
to a fiber of `L_a`, with value `t`. All transformations in that row
preserve this fiber, and on it

\[
\lambda_{a,b}(x)=t*(x*b)=L_tR_b(x).
\]

The [mixed-projection band identity](1485_graph_research.md#finite-sharp-successors-and-predecessors-a-proved-theorem)
therefore proves the result. The second identity is its column-dual.
These statements do not require finiteness or a central parameter.

Also `λ_{b,a}=id` whenever `a→b`, by the basic rectangular
recovery identity. The common fixed set of all the two-parameter
transformations is exactly the central set, directly from the definition
of centrality.

## The whole two-parameter family is not universally a band

It is false, even under E1485 and E151 together, that

\[
\lambda_{a,b}\lambda_{c,d}\lambda_{a,b}
=\lambda_{c,d}\lambda_{a,b}                                  \tag{2}
\]

for arbitrary parameters. Here is a four-vertex seed for a countable
counterexample. The vertices `u,v,a,c` are distinct. Prescribe

| Product | Value | Product | Value | Product | Value |
| --- | --- | --- | --- | --- | --- |
| `a*u` | `v` | `u*v` | `a` | `v*a` | `u` |
| `c*u` | `u` | `u*a` | `u` | `u*u` | `v` |
| `a*v` | `v` | `v*v` | `u` | `v*u` | `c` |

Then

\[
\lambda_{a,v}(u)=v*a=u,
\qquad
\lambda_{c,a}(u)=u*u=v,
\qquad
\lambda_{a,v}(v)=v*u=c\ne v.                                \tag{3}
\]

Thus (2) fails at `u`, with `(a,b,c,d)=(a,v,c,a)`.
In fact both `a` and `c` are central vertices in the extension below.
Having some central parameters therefore does not justify combining
the two separate band identities in (1).

### Why the seed has an E1485+E151 extension

Use the five-color relaxed structure from
[the involutive-squaring note](1485_involutive_research.md#4-a-five-color-certificate-goodness-reflection-fails).
Assign colors `0,1,2,4` to `u,v,a,c`, respectively. Its allowed
middle-color sets are

```text
[{1}, {2}, {0},   {2},   {1}],
[{4}, {0}, {0},   {4},   {1}],
[{1}, {1}, {3},   {3},   {1,3}],
[{4}, {2}, {3},   {2,4}, {3}],
[{0}, {0}, {0,3}, {3},   {3}].
```

The nine prescribed product paths are all allowed. In their union of
edges, each ordered endpoint pair has at most one allowed middle.
Every retained edge is part of a prescribed good product path, so it
is an actual magma edge in the extension. The established greedy
construction therefore gives a countable E1485 magma retaining all
nine products. The certificate's return-path symmetry gives E151.
Every ordinary two-edge path with middle color 2 or 4 is allowed;
the vertices `a,c` are consequently central.

The following independent, solver-free check verifies the full relaxed
certificate, the seed, and the last centrality assertion. It checks all
`5^5` instances of the five-cycle condition; it does not inspect an
infinite operation table or constitute Lean verification.

```python
from itertools import product

M = [
    [{1}, {2}, {0}, {2}, {1}],
    [{4}, {0}, {0}, {4}, {1}],
    [{1}, {1}, {3}, {3}, {1, 3}],
    [{4}, {2}, {3}, {2, 4}, {3}],
    [{0}, {0}, {0, 3}, {3}, {3}],
]
G = {(a, b, c) for a, c in product(range(5), repeat=2)
     for b in M[a][c]}
P = {(a, b) for a, b, c in G} | {(b, c) for a, b, c in G}
assert all(M[a][c] for a, c in product(range(5), repeat=2))
assert all(((a, b, a) in G) == ((b, a, b) in G)
           for a, b in product(range(5), repeat=2))
for a, b, c, d, e in product(range(5), repeat=5):
    if (a, b, c) in G and (c, d, e) in G and (e, a) in P:
        assert (b, c, d) in G
for b in (2, 4):
    assert all((a, b, c) in G for a, c in product(range(5), repeat=2)
               if (a, b) in P and (b, c) in P)

# Vertex indices u=0, v=1, a=2, c=3.
colors = [0, 1, 2, 4]
triples = {
    (2, 1, 0), (0, 2, 1), (1, 0, 2),
    (3, 0, 0), (0, 0, 2), (0, 1, 0),
    (2, 1, 1), (1, 0, 1), (1, 3, 0),
}
E = {(a, b) for a, b, c in triples}
E |= {(b, c) for a, b, c in triples}
assert all(tuple(colors[x] for x in t) in G for t in triples)
for a, c in product(range(4), repeat=2):
    assert sum((a, b) in E and (b, c) in E
               and (colors[a], colors[b], colors[c]) in G
               for b in range(4)) <= 1
print("The four-vertex mixed-band obstruction passes.")
```

## Parameter-image identities also require a finite argument

Fix central `k`, put `z=k*k`, `T(t)=t*z`, and write
`I_t=im λ_{t,k}`. Since these maps are idempotent,
`x∈I_t` is equivalent to `λ_{t,k}(x)=x`.

The independent standard-library checker
[1485_mixed_retraction_obstruction_check.py](../scripts/1485_mixed_retraction_obstruction_check.py)
verifies five seeds, including the preceding band counterexample and
the following four parameter-image obstructions. No SAT result is a
premise: the script directly checks the displayed certificates,
seed consistency, and the relevant term values.

| Proposed unrestricted assertion | Counterexample |
| --- | --- |
| `I_{z*(t*z)}=I_t` | Six-vertex seed with `z*(t*z)=k` and `x∈I_t\I_k`; both `k,t` are central. |
| `I_{T^10(t)}⊆I_t` | Six-vertex seed below; it fails for **every exponent at least two**, after the parameter has stabilized. |
| `I_{(T^8(t)*u)*z}⊆I_u` | Eight-vertex seed below; `T²(t)=t`, and `k,t,u` are central. |
| `I_{(h*u)*z}⊆I_h` for central `h` | Eleven-vertex seed in the checker, with both `k,h` central. |

The third row directly refutes unrestricted right absorption for the
proposed full meet formula. It is not inferred by assuming that `T`
is surjective.

### Stabilization does not give unrestricted image shrinkage

Use the three-color E151 certificate from the
[involutive-squaring note](1485_involutive_research.md#3-a-three-color-certificate-transitivity-and-compatibility-fail).
Its allowed middle sets are

```text
[{2}, {2},   {0}],
[{2}, {1,2}, {1}],
[{0}, {1},   {0,1}].
```

Take distinct vertices `k,z,t,a,b,x` with colors `2,1,2,1,1,0`.
Prescribe the eight products

\[
k*k=z,\quad t*z=a,\quad a*z=b,\quad b*z=b,
\]
\[
t*x=x,\quad b*x=t,\quad x*x=t,\quad x*k=x.
\]

Then `T^j(t)=b` for every `j≥2`, but

\[
\lambda_{b,k}(x)=t*x=x,\qquad
\lambda_{t,k}(x)=x*x=t\ne x.
\]

Thus no unrestricted eventual-inclusion argument of this form is
available, even after reaching a fixed parameter of `T`.

### The full meet counterexample has a periodic parameter

Over the same three-color certificate, take distinct vertices
`x,z,b,v,c,k,t,u`, with colors `0,1,1,1,1,2,2,2`.
Prescribe

\[
k*k=z,\quad t*z=c,\quad c*z=t,\quad t*u=b,\quad b*z=v,
\]
\[
x*k=x,\quad v*x=u,\quad u*x=x,\quad x*x=u.
\]

The period-two equations give `T^8(t)=t`, so the proposed meet
parameter is exactly `v=(T^8(t)*u)*z`. Nevertheless

\[
\lambda_{v,k}(x)=u*x=x,\qquad
\lambda_{u,k}(x)=x*x=u\ne x.
\]

The colors of `k,t,u` are central. The periodicity is an actual
retained two-cycle, so the failure persists when `t` is required to
belong to the stable image of `T`.

## Global sharp neighbors do not remove the obstruction

The counterexample can be required to have a sharp predecessor and a
sharp successor at **every** vertex. Thus adding that particular
finite-derived theorem as an abstract existence axiom does not make
the unrestricted band assertion true.

Here is a general extension argument. In a relaxed color structure,
call an allowed edge `a→b` *color-sharp* if

\[
P(b,c)\Longrightarrow G(a,b,c),\qquad
P(d,a)\Longrightarrow G(d,a,b)
\]

for all colors `c,d`. Any actual edge with these colors is sharp
in every strict completion respecting the certificate. In the displayed
five-color certificate, color-sharp successor and predecessor choices
for colors `0,1,2,3,4` are respectively

```text
successor:   2 4 1 2 0
predecessor: 4 2 0 2 1
```

To give an existing vertex `x` a sharp successor, add a path
`x→y→w`, with `y,w` fresh. Choose the color of `y` to be a
color-sharp successor of the color of `x`; choose any allowed
successor color for `w`. The required product path is good. This
extension is consistent: every new two-edge path has a fresh endpoint,
and that endpoint's sole incoming edge determines its middle, or it
is the prescribed path with fresh middle `y`. The edge `x→y`
is supported by that product path and remains sharp in every later
extension.

Dually, add `w→y→x`, with `w,y` fresh, choosing `y→x`
color-sharp and `w→y` allowed. This supplies a supported sharp
predecessor and preserves consistency for the same reason. Every color
has an allowed incoming and outgoing edge, by totality of good paths.

Interleave these two requests for every vertex with the original
enumeration of all product endpoint pairs. Always using fresh vertices
of the requested colors is possible in the countably infinite supply.
The resulting magma retains the seed, satisfies E1485 and E151, and
has both kinds of sharp neighbor everywhere. This is a construction
of one suitable completion, not a claim that every greedy completion
has the extra property.

The same argument applies to both other certificates used in the
research notes. For the three-color certificate, take successor and
predecessor choices both equal to `(2,1,0)`. For the five-color
central-rectangle certificate, take successors `(4,3,2,0,1)` and
predecessors `(3,4,2,1,0)`.

Consequently, finite cardinality comparisons and uniform **finite**
fiber counts remain substantive ingredients. One cannot replace all
uses of finiteness by the bare existence of sharp neighbors.

## Finite questions remain separate

The obstruction is countable, not finite. In particular it does not
refute (2) in finite E1485 models, nor the diagonal specialization
`Q_y Q_z Q_y=Q_z Q_y` for `Q_y(x)=(y*x)*(x*y)`.
The diagonal specialization passed all 394 archived/generated finite
tables checked in this investigation, but it is not proved here.

Do not replace the remaining rank problem by a claim that all diagonal
generator images are intersection-closed. This is false already in
the twisted Boolean model of order 32: with the bit labeling in the
main note,

\[
\operatorname{im}Q_1=\{0,4,8,12\},\qquad
\operatorname{im}Q_2=\{0,8,16,24\}.
\]

Their intersection has two elements, whereas the possible image sizes
of `Q_y` are `1,4,8,16,32`. This does not concern intersection
closure in a fixed-central-parameter family `λ_{t,k}`, which is a
different proposed route.

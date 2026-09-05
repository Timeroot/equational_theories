## A twist of the semi-symmetric quasigroup law

A magma satisfying this law is a quasigroup (left and right multiplication are bijective).  The left and right cubing maps `B: x ↦ x◇(x◇x)` and `C: x ↦ (x◇x)◇x` are automorphisms that cubes to the identity and are inverses of each other (`B(x◇y) = B(x)◇B(y)` and `B(B(B(x))) = C(C(C(x))) = B(C(x)) = C(B(x)) = x`).

The magma satisfies the middle crossed inverse property `B(y)◇(x◇y)=x` or equivalently `(B(y)◇x)◇y=x`.  It also satisfies the left and right crossed inverse property stating that `(y◇x)◇y` and `y◇(x◇y)` are `y`-independent, specifically `(y◇x)◇y = B(B(x))` and `y◇(x◇y) = B(x)`, namely the dual laws [4588](https://teorth.github.io/equational_theories/implications/?4588) and [4273](https://teorth.github.io/equational_theories/implications/?4273).

A more symmetrical way to state these facts is that for any three elements `x,y,z` of the magma the nine equations `x◇y=z`, `B(x◇B(y))=z`, `B(B(x)◇y)=z`, `y◇z=B(x)`, `y◇B(z)=x`, `B(y)◇z=x`, `B(z◇x)=y`, `z◇B(x)=B(y)`, `B(z)◇x=B(y)` are equivalent.

The left and right division operations defined by `x◇(x:y) = y` and `(x/y)◇y = x` satisfy the same law.  They are not merely first-order definable but *terms*, with four leaves each:
```
x : y = y ◇ C(x) = y ◇ ((x◇x)◇x),        x / y = y ◇ B(x) = y ◇ (x◇(x◇x)),
```
where the second reading of `/` is the crossed inverse property `(B(y)◇x)◇y = x` above, `B(y)◇x` and `y◇B(x)` being equal.  So the whole parastrophic family of `◇` — the operation, its opposite, the two divisions and their opposites — lives inside the term clone of `◇`.  Searching all `1,338` distinct two-variable `◇`-words of at most six leaves over a bank of models finds **exactly six** that are quasigroup operations, and they are exactly those six parastrophes; the rest of the clone is not cancellative.

All four division identities
```
x ◇ (y ◇ C(x)) = y,      (x◇y) ◇ C(x) = y,      (y ◇ B(x)) ◇ y = x,      y ◇ B(x◇y) = x
```
are consequences of 692 alone, with no finiteness hypothesis; a prover gets each of them, and the two cancellation laws, in seconds.  The first is not even a derivation — it is the law read at `z := y`, so **row surjectivity is free** and only the injectivity half is work.  That is exactly the pair `DiagRow.RowQG` asks for, and `RowQG_Equation692` records it, which is what lets the `Equation3` cell of this source hold over every carrier rather than only the finite ones.

In short, this law is a twist of the semi-symmetric quasigroup [law 14](https://teorth.github.io/equational_theories/implications/?14) `x = y◇(x◇y)` by an automorphism that cubes to the identity.  Analogous twists of law 14 include [law 66](https://teorth.github.io/equational_theories/implications/?66), [law 692](https://teorth.github.io/equational_theories/implications/?692), [law 695](https://teorth.github.io/equational_theories/implications/?695), [law 880](https://teorth.github.io/equational_theories/implications/?880), [law 978](https://teorth.github.io/equational_theories/implications/?978), [law 1073](https://teorth.github.io/equational_theories/implications/?1073), [law 1492](https://teorth.github.io/equational_theories/implications/?1492), [law 1496](https://teorth.github.io/equational_theories/implications/?1496), [law 1695](https://teorth.github.io/equational_theories/implications/?1695), [law 1719](https://teorth.github.io/equational_theories/implications/?1719).

## The twist is all-or-nothing

`B` cannot be partly trivial: if `B(a) = a` for a *single* element `a`, then `B` is the identity everywhere.  (This is a first-order consequence of 692 alone; an automated prover finds it quickly.)  Moreover `B = id` is precisely law 14 — the law implies 692, and 692 together with `B = id` implies it back.  So the models of 692 fall into exactly two disjoint families:

1. the semi-symmetric quasigroups (law 14), where the twist is trivial; and
2. the models where `B` has no fixed point at all, so every `⟨B⟩`-orbit has exactly three elements.

## The second family is a `Z/3`-extension

Let `M ⊨ 692` with `B` fixed-point-free.  Because `B` is an automorphism, the orbit space `Q = M/⟨B⟩` inherits an operation `*`, and:

* `Q` satisfies law 14, and `Q` has **no idempotent**;
* choosing a transversal identifies `M` with `Q × Z/3` in such a way that
  ```
  (q,i) ◇ (p,j) = (q*p, -(i+j) + μ(q,p))
  ```
  for a function `μ : Q × Q → Z/3` satisfying the cocycle condition `μ(p, q*p) = μ(q,p) + 1`.

Here `B(q,i) = (q, i+1)`.  Conversely, *every* pair `(Q, μ)` with `Q ⊨ 14` and `μ` a cocycle gives a model of 692 with `B` fixed-point-free, so this is a complete classification of the second family.

The cocycle condition is best read through the map `σ(q,p) = (p, q*p)` on `Q × Q`.  Law 14 gives `p*(q*p) = q` and `(q*p)*q = p`, so `σ³ = id`: the orbit of `(q,p)` is `{(q,p), (p,c), (c,q)}` with `c = q*p`.  The condition says `μ∘σ = μ + 1`, which is solvable exactly when `σ` has no fixed point, i.e. exactly when `Q` has no idempotent (`σ(q,p) = (q,p)` forces `p = q` and `q*q = q`).  When it is solvable, `μ` is an arbitrary choice of one value per `σ`-orbit, so there are `3^(|Q|²/3)` cocycles.

## Consequences for the order

Since all `σ`-orbits have size three, `3 | |Q|²`, hence `3 | |Q|`, hence

> **every finite model of 692 that is not a semi-symmetric quasigroup has order divisible by 9.**

The idempotent-free semi-symmetric quasigroups are scarce: up to isomorphism there is exactly one of order 3 (`Z/3` with `q*p = -(q+p)+1`), there are two of order 6, and there are none of order 1, 2, 4, 5 or 7.  So the smallest models of 692 outside law 14 have order 9; there are exactly three of them up to isomorphism (the extensions of the order-3 quasigroup by its `3³ = 27` cocycles give 54 labelled tables in 3 isomorphism classes), and each has an automorphism group of order 9 acting regularly.  The next size is 18, over the two idempotent-free semi-symmetric quasigroups of order 6.

## Affine models

Over a commutative ring `R`, the affine operation `x ◇ y = a x + b y + k` satisfies 692 exactly when
```
b = a⁻¹  (equivalently b = -a²),    a³ = -1,    k (a+1)² = 0.
```
For such a model `B(x) = x + (a⁻¹+1) k`, so it is a semi-symmetric quasigroup iff `(a+1) k = 0`.  When `N := (a⁻¹+1) k ≠ 0` one has `(a⁻¹+1) N = 0` and `3N = 0`, which is the 3-torsion the classification above predicts.

The universal coefficient ring is `Z[a]/(a³+1) = Z ×_{F₃} Z[ζ₆]`, glued over `Z/3`.  In the `Z` component `a = -1` and `k(a+1)² = 0` is vacuous, but so is `(a+1)k ≠ 0`, so that component only ever produces law-14 models.  In the Eisenstein component `a² - a + 1 = 0`, so `(a+1)² = 3a` and the conditions become `3k = 0` with `(a+1)k ≠ 0`.  The smallest such coefficient ring is `F₃[N]/(N²)` with `a = -1 + N`, which gives affine models on a carrier of order 9, matching the bound above.

## The clone of the order-9 model

Take the smallest non-quasigroup model: `Q = Z/3` with `q*p = -(q+p)+1`, extended by the cocycle `μ = 2`.  In the affine coordinates of the previous section it is `x ◇ y = P x + (I - P) y + ρ` over `(Z/3)²` with
```
P = [[2,2],[0,2]],    ρ = (0,1).
```
Every binary term of this magma is again affine, `u(x,y) = P' x + Q' y + ρ'` with `P' + Q' = I` and `P' = αI + βN` (`N = [[0,1],[0,0]]`), so the binary **clone has exactly `81` members**, indexed by `(α, β, ρ') ∈ Z/3 × Z/3 × (Z/3)²`; the diamond is `(α,β,ρ') = (2,2,(0,1))`.

It has exactly **three maximal proper subclones**, of sizes `54`, `27` and `27`:

| subclone | description | invariant |
| --- | --- | --- |
| `M₀` (54) | `α ∈ {0,1}` | one argument is blind to `x ↦ x + e₁` and the other is equivariant |
| `M₁` (27) | `β = 0`, i.e. `P'` scalar | shifting an argument by `x ↦ x + e₂` moves the value inside its own orbit |
| `M₂` (27) | `ρ' ∈ ⟨e₁⟩` | as `M₁` for `e₁`, and `u(x,x)` stays in the orbit of `x` |

Their union is exactly the `69` members that do **not** generate `◇` back — only the `12` members outside all three are reverse-readable.  Each of the three invariants in the right-hand column is a property of an operation alone, closed under composition with any operation having it, so it certifies a subclone without any reference to `692`.  That is enough to refute `TermStructuralFrom` (over finite magmas, hence over all magmas) for every target of `692` that some clone member realises: the realising members all land in the union, so none of them can recover `◇`.  This is `Definability/Shift692.lean`, which settles 36 targets at once.

## The affine clone in closed form

The previous section computed one clone by hand.  It is worth doing in general, because the answer is a formula.  Over any commutative ring, with `x ◇ y = a x + b y + k` and `s := a + b - 1`, **every** binary term is
```
□(x, y) = (1 - q + r s) x + q y + r k,        q, r ∈ R,
```
and conversely each `(q, r)` is realised.  Both projections are there (`(q,r) = (0,0)` and `(1,0)`), the diamond itself is `(b, 1)`, and composing `(q₁, r₁)` with `(q₂, r₂)` along `◇` gives `(a q₁ + b q₂, a r₁ + b r₂ + 1)` — the `x`-coefficient works out because `1 - (a+b) + s = 0` and nothing else.  So the clone is a *quotient of `R²`*, and a refutation is a scan of `|R|²` operations rather than a closure computation.  This is `Definability/AffineClone.lean`, which is hypothesis-free and applies to every affine magma over every commutative ring.

Deciding a law on one member costs nothing either: a term in variables `v₁ … v_n` evaluates to `Σ cᵢ vᵢ + e d` where `cᵢ` and `e` obey `cᵢ(N) = p cᵢ(L) + q cᵢ(R)` and `e(N) = p e(L) + q e(R) + 1`, so the law holds iff the `cᵢ` agree and `(e(L) - e(R)) d = 0` — no enumeration of assignments.  (A pleasant corollary: instantiating the law at the all-zero assignment and at each unit vector already implies the general case, so `n+1` ground instances are a *complete* certificate, not merely a necessary condition.  That is what `Definability/Aff692.lean` emits.)

Specialising to `L = 14`, a member `p x + q y + d` is a semi-symmetric quasigroup operation iff `p q = 1`, `p + q² = 0` and `(q+1) d = 0`; eliminating `p` this is
```
q³ = -1,        r s = -(q² - q + 1),        (q + 1) r k = 0.
```

## Only one small ring separates 692 from 14

An affine model of 692 refutes `Law14.TermDefinableFromFin Law692` exactly when *no* pair `(q, r)` solves that system.  Two observations make the hunt short.

* The branch `q = -1` makes the third equation vacuous, leaving `r s = -3`.  So `-3 ∉ s R` is a necessary condition — but not a sufficient one; `Z/63` with `b = 5` satisfies it and still fails, because `Z/63 = Z/9 × Z/7` has cube roots of `-1` other than `-1` and one may be chosen componentwise.
* Conversely a ring wants *few* cube roots of `-1`, which pushes towards local rings of characteristic `9`; but in characteristic `3` the element `b + 1` is nilpotent, `s = -(b+1)²`, and `r = 0` solves the system outright.

An exhaustive search settles it.  Over `Z/m` for every `m ≤ 600` there is no refuting affine model.  Widening to the family
```
R(ms, g) = Z[u] / (ms₀, u^d - g(u), ms₁ u, ms₂ u², …),        additive group ⊕ᵢ Z/msᵢ,
```
which contains every `Z/m`, every finite field, every Galois ring, every `Z/m[u]/(g)` and the mixed-modulus quotients that only appear inside them, and running over all `8,208` presentations of order at most `128`, **exactly one ring refutes**:
```
R₈₁ = (Z/9)[u] / (u³, 3u),        additive group Z/9 ⊕ Z/3 ⊕ Z/3.
```
It is `Z/9[β]/(β³+1)` — the universal coefficient ring of the previous section, reduced mod 9 — cut down by the ideal `(u³)` where `u = β + 1`; the quotient is the smallest one that still works, the full `729`-element ring and its `243`-element quotient being the only others.  Inside `R₈₁` there are `324` refuting triples `(a, b, k)`; the one used in Lean is
```
b = u - 1,    a = -b²,    k = u² - u,    s = a + b - 1 = -3 - u²,    B x = x + (b+1)k = x - u²,
```
so `B` is a fixed-point-free translation of order 3, as the classification demands,
and the reason it works is a single `decide`: `r (3 + u²) = 3 r₀ + r₀ u²` never equals `3`, because that would need `r₀ ≡ 1 mod 3` in the `1`-coordinate and `r₀ ≡ 0 mod 3` in the `u²`-coordinate at once.

`Definability/Aff692.lean` builds `R₈₁` as a three-field structure with a `CommRing` instance whose every axiom is `ext <;> simp <;> ring`, checks `692` on it by `native_decide`, and scans all `6,561` clone members against eight targets that none of them satisfies:
```
14, 477, 1113, 1492, 1519, 3272, 3472, 3588.
```
Since 692 is the implication-maximal law the model satisfies, and refutations of definability travel from stronger sources to weaker ones, these eight statements close **892** cells of the definability board and finish 692 as a source for term-definability.

## Definable companions of a single finite model

On a finite carrier, `∅`-definability of an operation is the same thing as invariance under the automorphism group, so for one fixed model `M ⊨ 692` both definability flavours become finite enumerations:

* `DefinableOnMagma L M` holds iff some `Aut(M)`-invariant binary operation satisfies `L`;
* `StructuralOnMagma L M` holds iff some operation with `Aut(□) = Aut(M)` **exactly** satisfies `L` — the forward half asks `Aut(M) ⊆ Aut(□)` and the reverse half asks `Aut(□) ⊆ Aut(M)`.

Listing the invariant operations is easy: pick one representative of each `Aut(M)`-orbit on `M²`, give it any value fixed by that pair's stabiliser, and the rest of its orbit is forced (consistently, because two group elements carrying the representative to the same pair differ by a stabiliser element).  So the count is `∏ |Fix(stab)|` over the orbits, and it is small exactly when `Aut(M)` is large.  A sample of the 692 bank, one row per distinct invariant family (several non-isomorphic models can share an order, and orders 4, 5, 6 and 7 each carry more than one):

| order | `\|Aut\|` | definable companions | of which `Aut`-exact |
| --- | --- | --- | --- |
| 3 | 6 | 3 | 3 |
| 3 | 3 | 27 | 24 |
| 4 | 12 | 4 | 2 |
| 4 | 2 | 65 536 | 65 188 |
| 5 | 12 | 40 | 16 |
| 6 | 6 | 20 736 | 20 446 |
| 7 | 42 | 7 | 5 |
| 7 | 24 | 567 | 162 |
| **7** | **168** | **3** | **1** |
| 9 | 9 | 387 420 489 | — |

The gap between the last two rows is the whole story.  An order-9 model — the smallest one outside law 14 — has `Aut` of order 9 acting regularly, hence nine orbits with trivial stabiliser and `9⁹` definable companions against a term clone of only `81`; it can never refute anything.  The order-7 model with `|Aut| = 168` refutes almost everything.

## The Fano plane decides the structural flavour

That model is the **Steiner quasigroup of the Fano plane**: the seven points of `PG(2,2)`, with `x ◇ y` the third point on the line through `x` and `y` (and `x ◇ x = x`),
```
0 6 5 4 3 2 1        Aut = GL(3,2),  |Aut| = 168,  2-transitive
6 1 4 5 2 3 0
5 4 2 6 1 0 3
4 5 6 3 0 1 2
3 2 1 0 4 6 5
2 3 0 1 6 5 4
1 0 3 2 5 4 6
```
It is idempotent and satisfies law 14, hence 692.  Because `GL(3,2)` is 2-transitive there are just two orbits on pairs: the diagonal, whose representative has stabiliser `GL(2,2)` and hence forced value `x`, and everything else, whose representative `(0,1)` has trivial stabiliser and so is free.  That leaves **three** definable companions in total — the two projections and `◇` itself — and the projections have the full symmetric group `S₇`, so exactly **one** is `Aut`-exact.  Therefore

> every `∅`-definable binary operation on the Fano Steiner quasigroup is a projection or `◇`.
> In particular `L.StructuralFromFin Law692` implies that the Fano quasigroup satisfies `L`, and
> `L.DefinableFromFin Law692` implies that `L` is satisfied by the Fano quasigroup or by a
> projection.

This is the sharpest one-model test the board admits, and it is *complete* for that model: there is nothing left to try there.  Running it, together with the same enumeration at every other banked model, over all `4,694` laws refutes `DefinableFromFin` for `2,562` of them and `StructuralFromFin` for `4,550`.  **Neither refutes anything the board did not already know** — zero new cells, and zero disagreements with a recorded positive.  So the finite-model lane for 692 is closed: every remaining open cell has an `Aut`-exact companion on every model that can be built, and they all look positive rather than negative.

## Word companions are exhausted

The positive side is blocked from the other direction.  A companion produced by a two-variable term `W` is automatically definable, so only the reverse half `Aut(W) ⊆ Aut(M)` has to be checked, and the Fano model makes that check nearly free.  Over a twelve-model core spanning the orders `1 … 9`:

* `39,586` distinct `◇`-words of at most **eight** leaves (distinct as operations on the core);
* `2,126` of them pass `Aut(W) ⊆ Aut(M)` on every core model;
* **none** of those satisfies any of the fifty targets whose structural flavour is still open.

The two guarded shapes of `AutBox` fare no better: the diagonal box `x □ y = (x = y ? A(x,x) : x ◇ y)` was screened over `82,500` diagonal shapes of up to twelve leaves, and the idempotent box `x □ y = (x = y ? x : W(x,y))` over the same word list, with the same outcome.  Combined with the parastrophe count above — the divisions are already terms, so "let the companion be a quasigroup and recover `◇` through its first-order divisions" collapses back onto the term clone — every term-shaped positive route for 692's structural cells is spent.

What remains open is therefore genuinely between the two: a companion that is definable but not term-definable, uniformly across all models of 692.  The natural candidates are guards that are invisible on the law-14 side and active on the `Z/3`-extension side, for instance
```
x □ y = if x = y then D(x, y) else (if y = x ◇ x then A(x, y) else x ◇ y),
```
whose guard set is empty on every idempotent model — in particular on the Fano model, where the companion is forced to be `◇` — and has one cell per element on every `B`-fixed-point-free model.

## The dichotomy is now a theorem

`Definability/Branch692.lean` replaces the prover appeals above with Lean proofs.  Writing
`rot692 x = x ◇ (x ◇ x)` for `B`, it carries

```
rot692_eq         y ◇ (x ◇ y) = B x                    (uniformly in y)
rot692_sandwich   (y ◇ B x) ◇ y = x
rot692_inj        B is injective
rot692_op_left    B x ◇ y = B (B (x ◇ y))
rot692_op_right   x ◇ B y = B (B (x ◇ y))
rot692_cube       B (B (B x)) = x
rot692_hom        B (x ◇ y) = B x ◇ B y
equation14_of_rot692_fixed   B a = a for one a  →  Equation14
branch692         Equation14 ∨ ∀ x, B x ≠ x
equation14_iff_rot692_id     Equation14 ↔ B = id
```

`rot692_eq` and `rot692_sandwich` are Vampire superposition chains transcribed through
`Superposition.lean`; the two absorption laws are `grind` with a raised budget; `rot692_cube` is the
calculation `B²x = x ◇ (B x ◇ x) = B⁵x` followed by injectivity twice.  The point of `branch692` is
that both of its disjuncts are *sentences* — `Set.Definable ∅` admits no parameters, so a case split
on the branch is legal, whereas a split naming a fixed point of `B` would not be.

## A companion for law 14 is a choice of one pair per triple

On the law-14 branch `◇` is itself a companion for every target that 14 implies, which is 60 of the
70 targets of this source that are still open somewhere and 29 of the 31 open for definability.  So
the whole definability question for 692 is: **on a `Z/3`-extension, is there a `∅`-definable `w`
with `w(y, w(x,y)) = x`?**

Unwind what such a `w` is.  Put `z = w(x,y)`; law 14 applied twice gives `w(y,z) = x` and
`w(z,x) = y`, so `w` is exactly a partition of `M × M` into cyclic triples
`(x,y) → (y,z) → (z,x)`.  The natural candidates are the *lifts* `w = B^{c(x,y)}(x ◇ y)`, which keep
`z` inside the `⟨B⟩`-orbit that `◇` already produces.  For those, the identity `y ◇ (x ◇ y) = B x`
and `y ◇ B^k u = B^{2k}(y ◇ u)` turn law 14 into a single cocycle condition on the phase,
```
c(y, w(x,y)) = c(x,y) - 1,
```
and equivariance `w(Bx, By) = B w(x,y)` into `c(Bx, By) = c(x,y)` — which is automatic for a
quantifier-free `c`, because `B` is an automorphism and so every term satisfies
`t(Bx, By) = B t(x,y)`.  Around one `σ`-triple the phase therefore takes the values `c`, `c-1`,
`c+1`: all three, once each.  A phase that factors through `Q × Q` is thus the same thing as a
**transversal of the `σ`-orbits** — the pairs carrying `c = 0` — so a definable companion of that
kind is a definable way to pick one pair out of each cyclic triple `{(q,p), (p,c), (c,q)}`.  Nothing
in the language distinguishes the three, and that is the entire difficulty.

## The finite side is uniformly positive, the uniform side is not

Per model there is no obstruction at all.  Over the 186 banked models with `B` fixed-point-free
(orders 9 and 18), a CP-SAT search for an `Aut(M)`-invariant companion — which on a finite carrier
is exactly `DefinableOnMagma Equation14 M` — succeeds on **every one of them**, and already succeeds
with the lift shape.  Adding the 320 order-27 extensions built from the 40 idempotent-free
semi-symmetric quasigroups of order 9 changes nothing.  So there is no finite refuter to be found
here: every open definability cell of this source is positive-shaped, and what is missing is a
formula, not a model.

Searching for that formula uniformly is where it stops.  A quantifier-free companion is a map from
quantifier-free types to terms, so fix a leaf bound and the search is one CP-SAT instance over all
models at once.  With the lift shape:

| leaves | terms | quantifier-free types | uniform phase |
| --- | --- | --- | --- |
| 2 | 6 | 11 | none |
| 3 | 22 | 338 | none |
| 4 | 102 | 5 317 | **exists** |

Four leaves is exactly enough, which is unsurprising — all three lift values are available there,
since `B u = z ◇ (u ◇ z)` and `B² u = (z ◇ u) ◇ z` for *any* `z`, so
```
B⁰(x◇y) = x ◇ y,      B¹(x◇y) = x ◇ ((x◇y) ◇ x),      B²(x◇y) = (x ◇ (x◇y)) ◇ x.
```
But a phase spread over 5 317 types is not something one writes down.  What one would write is a
shallow decision tree, and there is none.  The order-9 models pin the shape: each has exactly three
valid phases, all inducing the same partition of its 81 pairs into three blocks of 27, so a usable
set of tests has to separate those blocks — a covering condition.  The 5 151 term equations with at
most four leaves collapse to **783 distinct predicates** once their truth tables over all models are
compared, of which **1 717 pairs** separate the blocks, and *none* of them supports a valid phase
under any of the `3⁴` labellings.  So the phase cannot be computed from two term equations of that
size, and the branch-B half of `Definable(692 → 14)` — worth 58 cells on its own — needs either a
deeper guard or a companion that is not a lift.

## The automorphism group of a `Z/3`-extension

The searches above want `Aut(M)` for a great many order-18 and order-27 models, and computing it by
backtracking on 27 points is slow enough to be the bottleneck.  The extension coordinates give it in
closed form instead.  `B` is a term, so every automorphism commutes with it and therefore descends
to the quotient; writing `φ(a,i) = (ψ a, i + s(a))` with `ψ : Q → Q` and `s : Q → Z/3`, the
computation

```
φ((a,i) ◇ (b,j)) = (ψ(a*b),  μ(a,b) - i - j + s(a*b))
φ(a,i) ◇ φ(b,j) = (ψa * ψb, μ(ψa,ψb) - i - s(a) - j - s(b))
```

says that `φ ∈ Aut(M)` iff `ψ ∈ Aut(Q)` and

> **`μ(ψa, ψb) - μ(a,b) = s(a) + s(b) + s(a*b)`  for all `a, b`.**

For each of the (few) automorphisms of `Q` that is one inhomogeneous `F₃`-linear system in the `|Q|`
unknowns `s(a)`; it either has no solution — `ψ` does not lift — or a full coset of solutions, and
the coset is a subgroup of `(Z/3)^{|Q|}` containing the constants, which is `⟨B⟩`.  So
`Aut(M)` is an extension of a subgroup of `Aut(Q)` by that solution space, and one solves `|Aut(Q)|`
tiny linear systems instead of searching `S₂₇`.  In practice this turns minutes into milliseconds,
and it explains the census: a random cocycle over a random `Q` lifts nothing, so the 320 generated
order-27 models all have `|Aut(M)| = 3`, exactly `⟨B⟩`, with all 243 pair-orbits free.

## The lift shape is not always available

The lift restriction looked free, because it is free on everything one stumbles across.  It is not a
theorem.

Reread the cocycle condition as an action.  A lift-shaped companion is a transversal of the
`σ`-orbits, and `Aut(M)` permutes those orbits; an invariant transversal exists iff no automorphism
maps a `σ`-orbit *to itself* nontrivially, i.e. iff no `φ ∈ Aut(M)` sends `(x,y)` to `(y, x◇y)`.
Downstairs that reads: no `ψ ∈ Aut(Q)` has

```
ψ²(a) = a * ψ(a)      for some a
```

(from `ψa = b`, `ψb = a*b`).  Call such a `ψ` a **rotator**.  The question is whether an
idempotent-free law-14 quotient can have one, and CP-SAT answers it: for `|Q| = 3` and `6` no
rotator exists, and for `|Q| = 9`, `12` and `15` one does.  Of those three, the order-12 and
order-15 examples turn out to be harmless — the linear system above has no solution for any cocycle,
so their rotator never reaches `Aut(M)` — but the order-9 example lifts.  Its extension is an
explicit **`M` of order 27** with `|Aut(M)| = 9` (so `B` generates only a third of it) whose
automorphism group contains a rotator, and on it

* the lift-shaped search over all 81 `Aut(M)`-orbits of pairs is **unsatisfiable**;
* an `Aut(M)`-invariant law-14 companion nevertheless exists, found in two seconds — and it is a
  totally idempotent Mendelsohn triple system, unrelated to `◇`: only 27 of the 729 pairs land in
  the `⟨B⟩`-orbit that `◇` produces, and which one it lands in is not a function of the two
  `⟨B⟩`-orbits it came from.

The control runs the other way: the same test is satisfiable on every banked branch-B model and on
all 400 generated order-18 and all 320 generated order-27 extensions.  Nor is size of `Aut` the
issue.  The most symmetric branch-B models available at order 27 come from

```
Q = (F₃², a * b = -a - b + t),  t ≠ 0,        μ(a,b) = m(b) - m(a) + c,  m linear with m(t) = 1,
```

where `Q` is idempotent-free because `a*a = a + t`, `Aut(Q) = Stab_{GL₂(3)}(t) ⋉ F₃²` has order 54,
and the displayed `μ` solves the cocycle condition identically.  The best of the 72 such tables has
`|Aut(M)| = 162` and only **12** orbits on its 729 pairs — six times more constrained than the
obstructed model — and it still admits a lift.

So the obstruction is not scarcity of orbits but the presence of a rotator, and the conclusion for
the board is sharp in both directions: `DefinableFromFin (692 → 14)` has no finite refuter (every
model built so far, symmetric or not, carries an invariant companion), while the only *writable*
family anyone has proposed for the uniform statement — `B^c(x◇y)` — provably does not cover all
models.  A uniform companion has to be a Mendelsohn system chosen without reference to `◇`.

This also disposes of the last cheap idea, which is to take the companion from the parastrophic
family.  All six parastrophes are terms (§1), and each of them returns a twist rather than the
identity:
```
w = x◇y  ⟹  B x        w = x \ y  ⟹  B² x        w = x / y  ⟹  B² x
w = y◇x  ⟹  B² x       w = y \ x  ⟹  B x         w = y / x  ⟹  B x       (all as w(y, w(x,y)))
```
and post-composing with `B^m` multiplies the answer by `B^{3m} = id`, so it changes nothing.  On the
law-14 branch every one of these *is* a law-14 operation, which is why the split matters; on the
branch-B side none of them is.

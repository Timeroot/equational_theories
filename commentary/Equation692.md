## A twist of the semi-symmetric quasigroup law

A magma satisfying this law is a quasigroup (left and right multiplication are bijective).  The left and right cubing maps `B: x ↦ x◇(x◇x)` and `C: x ↦ (x◇x)◇x` are automorphisms that cubes to the identity and are inverses of each other (`B(x◇y) = B(x)◇B(y)` and `B(B(B(x))) = C(C(C(x))) = B(C(x)) = C(B(x)) = x`).

The magma satisfies the middle crossed inverse property `B(y)◇(x◇y)=x` or equivalently `(B(y)◇x)◇y=x`.  It also satisfies the left and right crossed inverse property stating that `(y◇x)◇y` and `y◇(x◇y)` are `y`-independent, specifically `(y◇x)◇y = B(B(x))` and `y◇(x◇y) = B(x)`, namely the dual laws [4588](https://teorth.github.io/equational_theories/implications/?4588) and [4273](https://teorth.github.io/equational_theories/implications/?4273).

A more symmetrical way to state these facts is that for any three elements `x,y,z` of the magma the nine equations `x◇y=z`, `B(x◇B(y))=z`, `B(B(x)◇y)=z`, `y◇z=B(x)`, `y◇B(z)=x`, `B(y)◇z=x`, `B(z◇x)=y`, `z◇B(x)=B(y)`, `B(z)◇x=B(y)` are equivalent.

The left and right division operations defined by `x◇(x:y) = y` and `(x/y)◇y = x` satisfy the same law.

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

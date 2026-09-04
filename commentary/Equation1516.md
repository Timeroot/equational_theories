A challenging equation, discussed [here](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1516.20-.3E.20255) and in [this chapter of the blueprint](https://teorth.github.io/equational_theories/blueprint/1516-chapter.html).  This law implies [law 255](https://teorth.github.io/equational_theories/implications/?255) in linear models, translation-invariant models, and finite magmas, but can be refuted by a complicated greedy construction.

The fact that it does not imply [law 1489](https://teorth.github.io/equational_theories/implications/?1489) even for finite models was resolved using the [cohomological method](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/485020624), which resulted in a 35-element quasigroup.

This law cannot hold in a non-trivial semigroup (associative magma).

This law is a twist of the [Dupont law 63](https://teorth.github.io/equational_theories/implications/?63) by the squaring map.  The finite spectrum of (cardinalities of finite magmas satisfying) this law is [unknown](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Order.203.20Spectra/with/527073087).

In quasigroups, this law implies that the squaring map `S: x ↦ x◇x` is bijective (with inverse `x ↦ (x◇(x◇x)) ◇ ((x◇(x◇x))◇x)`).

## Small models are scarce, and they are all affine

There is no model of `x = (y◇y) ◇ (x ◇ (x◇y))` of order 2, 3, 4 or 6.  Up to isomorphism there is exactly one of order 5, exactly three of order 7 and exactly one of order 8, and a model of order 9 is known.  Every model of order at most 8 is *affine*: `x ◇ y = a x + b y + k` over a finite field, namely `Z/5`, `Z/7` and `F₈` respectively.

A SAT enumeration settles this exhaustively.  Ask for a table satisfying 1516 and block each model together with its whole isomorphism class; the search terminates at every order up to 8, and the four orders 2, 3, 4, 6 come back unsatisfiable outright.  Mediality `(x◇y)◇(z◇w) = (x◇z)◇(y◇w)` — which every affine magma satisfies — can be attacked directly and much more cheaply: assert 1516 together with a *single* violation of the medial law, placed at a fixed tuple, since only the pattern of coincidences among the four coordinates matters up to isomorphism and there are fourteen such patterns.  That question is unsatisfiable for every order up to 8 as well, so no small model escapes by being medial-but-not-affine either (all the translations `L_c`, `R_c` of these models are bijections, which is what turns mediality into affineness).

This is the reason the definability board cannot be moved from 1516 by exhibiting a finite model: every finite model small enough to find is affine, and §"The `R₂` clone" below shows that on an affine model the coset bound already contains a solution of every open target.  The obstruction genuinely needs the infinite carrier.

## The affine spectrum

Over a commutative ring `R`, expanding the law for `x ◇ y = a x + b y + k` and comparing coefficients gives
```
a b (1 + b) = 1,        a² + a b + b³ = 0,        k (a + b² + b + 1) = 0.
```
The first condition makes `b + b²` invertible with `a = (b + b²)⁻¹`; substituting into the second and clearing denominators leaves a single polynomial condition on `b`:
```
h(b) = b⁷ + 2b⁶ + b⁵ + b³ + b² + 1 = (b³ - b + 1)(b⁴ + 2b³ + 2b² + b + 1) = 0.
```
Both factors are irreducible over `Q`, so the affine models are the ring homomorphisms out of
`U = Z[b, 1/(b+b²)]/(h)`, which has two components:

* **`R₁ = Z[b]/(b³ - b + 1)`** — here `a = 1 - b`, since `(1-b)(b+b²) = b - b³ = 1`.  So **`a + b = 1`**.  The constant is constrained by `a + b² + b + 1 = b² + 2`, which is a non-zero-divisor in `R₁` itself, so `k = 0` there.  This is the cubic field of discriminant `-23`.
* **`R₂ = Z[b]/(b⁴ + 2b³ + 2b² + b + 1)`** — here `1 + (b+b²) + (b+b²)² = 0`, i.e. **`a² + a + 1 = 0`**: `a` is a primitive cube root of unity.  Also `a + b² + b + 1 = 0` identically, so `k` is completely unconstrained.  The quartic has discriminant `117 = 9·13`.

The two components are glued at a single prime: `Res(b³ - b + 1, b⁴ + 2b³ + 2b² + b + 1) = 19`, the common root being `b ≡ 13 (mod 19)`, where `a ≡ 7` and indeed `a + b ≡ 1` and `a³ = 343 ≡ 1 (mod 19)`.

Reducing `h` modulo a prime therefore lists all the affine models in that characteristic.  For example `h ≡ (b+5)(b²+2b+3) · (b⁴+2b³+2b²+b+1)` mod 7 has three roots `b = 2, 5, 1`, giving the parameters `(a,b,k) = (6,2,0), (4,5,0), (4,1,0)` — exactly the three models of order 7.  Mod 5 only the cubic has a root (`b = 3`, so `x ◇ y = 3(x+y)`), which is the unique model of order 5.  Where a factor of `h` stays irreducible one gets a model over an extension field instead: `b³ - b + 1` is irreducible mod 2, giving a model on `F₈`, and `b⁴+2b³+2b²+b+1 ≡ (b²+b+2)²` mod 3, giving one on `F₉`.

## Automorphisms

On an `R₁` model, `a + b = 1` makes *every* affine map `x ↦ u x + v` (`u` a unit) an automorphism, because
`σ(x) ◇ σ(y) = a(ux+v) + b(uy+v) = u(x ◇ y) + (a+b)v = σ(x ◇ y)`.
So `Aut(M) ⊇ AGL(1,R)`.  Over a finite field `F` this is sharp and `AGL(1,F)` is 2-transitive, which pins down the definable structure completely: `M²` has just two `Aut`-orbits — the diagonal, whose representative `(0,0)` has stabiliser `F^×` and hence forced value `0`, and everything else, whose representative `(0,1)` has trivial stabiliser.  Consequently the `R₁` field models carry exactly `|F|` invariant binary operations, namely
```
f_c(x, y) = (1-c) x + c y,     c ∈ F,
```
In every case computed (`F₅, F₇, F₈, F₂₅, F₂₇`) the clone of the magma is *all* of `{f_c}`, so on these models definable and term-definable coincide.  Concretely `|Aut| = 20, 42, 56, 702` for the models on `F₅, F₇, F₈, F₂₇`.

An `R₂` model has `a + b ≠ 1`, so translations are *not* automorphisms; with `k = 0` only the scalings survive and `Aut ⊇ F^×`.  The order-9 model on `F₉` has `|Aut| = 8`, and the two `R₂` models of order 7 have `|Aut| = 6`.

## A term invariant

On any `R₁` model, a term of the magma is an affine form `Σ Aᵢ xᵢ + C` whose coefficients obey
`A(u ◇ v) = a·A(u) + b·A(v)`.  Since the two generators `x` and `y` have coefficient sums `1` and `a + b = 1`, **every term satisfies `Σ Aᵢ = 1`** (and `C = 0`, since `k = 0`).  This is a strong obstruction: a target law whose affine solutions all have coefficient sum different from `1` cannot be realised by any term of any `R₁` model.

## The `R₂` clone, and why the obstruction is characteristic zero

The `R₂` branch is the interesting one, because there `k` is free.  Fix `k = 1` (a unit, so a law's
constant condition stays sharp) and write `s := a + b - 1 = -(2 + b²)`.  Every binary term of
`x ◇ y = a x + b y + k` is affine, and composing along `◇` gives the closed form
```
□(x, y) = (1 - q + r s) x + q y + r k,     (q₁,r₁) ∘ (q₂,r₂) = (a q₁ + b q₂, a r₁ + b r₂ + 1),
```
so a target law imposes exactly three conditions on the pair `(q, r)`: the coefficient of `x`, the
coefficient of `y`, and the constant.  The constant of *every* term is a multiple of `r` — the
recursion is `E(u ◇ v) = P E(u) + q E(v) + 1` with `E(x) = E(y) = 0` — so the third condition
always has the shape
```
r · W(q, r) = 0,
```
and because `R₂` is a **domain** that is a free case split.  Nothing else is needed: no Groebner
basis, no elimination.  Both halves then die in a residue field of degree one.

Take target `63`, `x = y ◇ (x ◇ (x ◇ y))`.  Writing `p = 1 - q + r s` the three conditions are
```
q p (1 + q) = 1,        p + q³ = 0,        (q² + q + 1) · r = 0.
```
* `r = 0` forces `p = 1 - q`, and both of the first two collapse to `q³ - q + 1 = 0`.  That has no
  root modulo `13` at `b = 6` (and none modulo `2`, where `R₂/2 = F₁₆` and `3 ∤ 4`).
* `q² + q + 1 = 0` forces `p = -1`, hence `r s = q - 2`.  Modulo `19` at `b = 13` the element `s`
  vanishes, `q ∈ {7, 11}`, and `q - 2 ∈ {5, 9}` is never `0`.

The same two primes settle all forty-two open targets uniformly:
```
63 73 118 125 222 229 271 274 467 504 667 870 910 917 1086 1685 1692 1722 1729 1895 1898 1922
1925 2541 2697 2710 2737 2900 3140 3143 3269 3279 3345 3475 3482 3548 3881 3888 3954 4081 4084 4157
```
branch `r = 0` is empty over `F₁₃` at `b = 6`, and branch `W = 0` is empty over `F₁₉` at `b = 13`.
The choice of `19` is not a coincidence: it is the resultant of the two factors of `h`, the one
prime where the two affine branches meet and the one prime at which `s` vanishes.

**No finite model of this shape exists.**  The obstruction really does need an infinite carrier:

* over `Z/19^e` the offending solution lifts to every level — Hensel applies because the relevant
  derivative is a unit — and a direct sweep to `e = 8` (`m = 16 983 563 041`) kills nothing, each
  target keeping exactly one solution at every level;
* the exact clone of the model over `F₁₉` is the whole `19 × 19` grid, as is the coset bound over
  `Z/361`;
* at every prime other than `19` the element `s` is a unit, so `r s` can be made anything and the
  second branch never closes;
* products do not help.  In `∏ Z/pᵢ` the pair `(q, r)` ranges over the product freely, so the
  system splits componentwise; every two-component product tried has the full clone (e.g.
  `Z/5 × Z/31`, `|clone| = 24 025` of `24 025`) and refutes only the four targets a single
  component already does.

Those four, `467`, `667`, `2900` and `3140`, are the exception: they are empty over `F₃₁` at
`b = 7` with no case split at all, so a genuinely finite affine model refutes them.  For the other
thirty-eight the split across two different primes is essential, and no finite quotient can carry
it — a finite domain is a field, and no field has both `F₁₃` and `F₁₉` as quotients.

`Definability/R1516.lean` and `Definability/R1516Cover.lean` formalise this, on the nose:
`R₂ = AdjoinRoot (X⁴ + 2X³ + 2X² + X + 1)`, a domain because the quartic reduces to the
irreducible `X⁴ + X + 1` modulo two.  The same clone serves law `2091`,
`x = ((y◇x)◇x) ◇ (y◇y)`, which the *opposite* magma satisfies: swapping `a` and `b` leaves `s`
alone, so `Magma.affFam` is literally the same family.  Between the two sources that is 60 cells
of the definability board, all in the `TermDefinableFrom`-over-all-magmas flavour, which is the
only flavour an infinite carrier can reach.

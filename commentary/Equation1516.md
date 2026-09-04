A challenging equation, discussed [here](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1516.20-.3E.20255) and in [this chapter of the blueprint](https://teorth.github.io/equational_theories/blueprint/1516-chapter.html).  This law implies [law 255](https://teorth.github.io/equational_theories/implications/?255) in linear models, translation-invariant models, and finite magmas, but can be refuted by a complicated greedy construction.

The fact that it does not imply [law 1489](https://teorth.github.io/equational_theories/implications/?1489) even for finite models was resolved using the [cohomological method](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/485020624), which resulted in a 35-element quasigroup.

This law cannot hold in a non-trivial semigroup (associative magma).

This law is a twist of the [Dupont law 63](https://teorth.github.io/equational_theories/implications/?63) by the squaring map.  The finite spectrum of (cardinalities of finite magmas satisfying) this law is [unknown](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Order.203.20Spectra/with/527073087).

In quasigroups, this law implies that the squaring map `S: x ↦ x◇x` is bijective (with inverse `x ↦ (x◇(x◇x)) ◇ ((x◇(x◇x))◇x)`).

## Small models are scarce, and they are all affine

There is no model of `x = (y◇y) ◇ (x ◇ (x◇y))` of order 2, 3, 4 or 6.  Up to isomorphism there is exactly one of order 5 and exactly three of order 7, and models of order 8 and 9 are known.  Every model of order at most 7 is *affine*: `x ◇ y = a x + b y + k` over `Z/n`.

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

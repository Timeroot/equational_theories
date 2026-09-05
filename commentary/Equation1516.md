A challenging equation, discussed [here](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1516.20-.3E.20255) and in [this chapter of the blueprint](https://teorth.github.io/equational_theories/blueprint/1516-chapter.html).  This law implies [law 255](https://teorth.github.io/equational_theories/implications/?255) in linear models, translation-invariant models, and finite magmas, but can be refuted by a complicated greedy construction.

The fact that it does not imply [law 1489](https://teorth.github.io/equational_theories/implications/?1489) even for finite models was resolved using the [cohomological method](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/485020624), which resulted in a 35-element quasigroup.

This law cannot hold in a non-trivial semigroup (associative magma).

This law is a twist of the [Dupont law 63](https://teorth.github.io/equational_theories/implications/?63) by the squaring map.  The finite spectrum of (cardinalities of finite magmas satisfying) this law is [unknown](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Order.203.20Spectra/with/527073087).

In quasigroups, this law implies that the squaring map `S: x ↦ x◇x` is bijective (with inverse `x ↦ (x◇(x◇x)) ◇ ((x◇(x◇x))◇x)`).

## What the law gives with no hypotheses at all

Write `S(x) = x ◇ x` and `φ_y(x) = x ◇ (x◇y)`.  The law *is* the statement

```
L_{S(y)} ∘ φ_y = id      for every y,
```

and read that way it gives, with no hypotheses at all and no derivation worth the name:

* **the rows of squares are onto** — `x` is `L_{S(y)}` applied to `φ_y(x)`, for every `x` and every `y`;
* **each section `φ_y` is injective** — it has a left inverse.

That is all one gets for free, and, as far as any prover here can tell, all one gets at all.  What is conspicuously *missing* is either half of the converse pair, and the two halves are equivalent to each other:

> `L_{S(y)}` is injective  ⟺  `φ_y` is onto.

(Left to right is immediate; right to left, `L_{S(y)}u = L_{S(y)}v` with `u = φ_y(x)`, `v = φ_y(x')` forces `x = x'`.)  Each is a fixed point of the other's proof, which is exactly why the argument closes only when the carrier is finite: there a left inverse is a two-sided inverse, `L_{S(y)}` is a bijection, squaring is injective and therefore onto, every row is a row of squares, and the magma is a left quasigroup.  `cancelLeft_Equation1516`, `sqSurj_Equation1516` and `cancelRight_Equation1516` all carry a `[Finite G]`, and none of them is known without it: Vampire and twee were given `a◇b = a◇c → b = c`, `a◇c = b◇c → a = b` and `∀ z, ∃ y, y◇y = z` as separate conjectures, under refutation and saturation schedules alike, and returned nothing either way.

**Whether `S` is surjective without finiteness is the single open question that governs this source's board.**  It is what separates every `FromFin` result below from its all-magma counterpart: the recovery step wants to read `x◇x` off a companion as the one value missing from a row, and that argument needs every row to be a bijection, not just the rows indexed by squares.

On the affine models the answer is yes, and for a reason that is pure arithmetic rather than counting.  With `x ◇ y = a x + b y + k` the law forces
```
ab(1+b) = 1,        a² + ab + b³ = 0,        k(a + b² + b + 1) = 0,
```
so `a`, `b` and `1+b` are units, and eliminating `a = 1/(b+b²)` from the second equation makes `b` a root of
```
f(t) = t⁷ + 2t⁶ + t⁵ + t³ + t² + 1.
```
Now `S(x) = (a+b)x + k`, so `S` is onto exactly when `s = a + b` is a unit — and `s = a(1 + b² + b³)`, while dividing `f` by `g(t) = t³ + t² + 1` leaves remainder exactly `t`:
```
f(t) = (t⁴ + t³ − t + 1)·g(t) + t.
```
So `g(b)·(b⁴+b³−b+1) = −b`, a unit, hence `g(b) = 1 + b² + b³` is a unit and `s` is a unit — in *every* commutative ring, of any characteristic, with no finiteness anywhere.  An infinite counterexample to square-surjectivity therefore cannot be affine, and by the enumeration in the next section it cannot be small either.

## Small models are scarce, and they are all affine

There is no model of `x = (y◇y) ◇ (x ◇ (x◇y))` of order 2, 3, 4 or 6.  Up to isomorphism there is exactly one of order 5, exactly three of order 7 and exactly one of order 8, and a model of order 9 is known.  Every model of order at most 8 is *affine*: `x ◇ y = a x + b y + k` over a finite field, namely `Z/5`, `Z/7` and `F₈` respectively.

A SAT enumeration settles this exhaustively.  Ask for a table satisfying 1516 and block each model together with its whole isomorphism class; the search terminates at every order up to 8, and the four orders 2, 3, 4, 6 come back unsatisfiable outright.  Mediality `(x◇y)◇(z◇w) = (x◇z)◇(y◇w)` — which every affine magma satisfies — can be attacked directly and much more cheaply: assert 1516 together with a *single* violation of the medial law, placed at a fixed tuple, since only the pattern of coincidences among the four coordinates matters up to isomorphism and there are fourteen such patterns.  That question is unsatisfiable for every order up to 8 as well, so no small model escapes by being medial-but-not-affine either (all the translations `L_c`, `R_c` of these models are bijections, which is what turns mediality into affineness).

The pattern does not stop at order 8.  The whole model bank — 122 magmas of orders 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 31, 35, 37, 43, 49, 53, 55, 59, 61, 65, 67, 73, 77, 79, 83, 85, 89, 91, 95, 97, 101, 103, 107, 109, 113, 115, 119, 121, 125 and 169 — consists **without exception** of medial quasigroups with an idempotent, so Toyoda's theorem makes every one of them affine over an abelian group, and 75 of them are literally `a x + b y + k` over the cyclic group `Z/n`.  The other 47 sit over elementary abelian groups, at the prime-power orders `8, 9, 16, 25, 27, 49, 121, 125, 169` where the relevant factor of `h` stays irreducible.  Solving `h(b) = 0` over `Z/n` reproduces the cyclic list exactly: `n = 5, 7, 11, 13, 17, 19, 23, 25, 31, 35, 37, 43, 49, 53, 55, 59, …` — and, in the other direction, `h` has no root modulo `2`, `3` or `4`, which is a one-line proof that no model of order 2, 3, 4 or 6 is affine.

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

Sharpening the `R₁` count: of the `|F|` invariant operations `f_c`, the two projections `f_0` and `f_1` have the full symmetric group, and the other `|F| - 2` have automorphism group *exactly* `AGL(1,F)`.  Over `F₈` this is worth spelling out, because `x ↦ x²` is a field automorphism and one might expect `AΓL(1,8)` of order `168`: but `σ(f_c(x,y)) = f_{c²}(σx, σy)`, so Frobenius normalises the family rather than fixing a member, and it is an automorphism of `f_c` only when `c² = c`, i.e. only for the two projections.  Hence `|Aut(M)| = 56` on the nose, and the census reads

| model | `\|Aut\|` | definable companions | of which `Aut`-exact |
| --- | --- | --- | --- |
| `F₅` | 20 | 5 | 3 |
| `F₇` (three of them) | 42 or 6 | 7 | 5 |
| `F₈` | 56 | 8 | 6 |
| `F₉` | 8 | — | — |
| `F₁₁` | 110 | 11 | 9 |

so `StructuralOnMagma L M` on an `R₁` field model is decided by asking whether some interpolation `(1-c)x + cy` with `c ∉ {0,1}` satisfies `L`, and `DefinableOnMagma L M` by allowing `c ∈ {0,1}` too.  Running that test at every banked model over all `4,694` laws refutes `DefinableFromFin` for `2,561` laws and `StructuralFromFin` for `4,577` — and, exactly as for [692](Equation692.md), **it yields no new cells and contradicts no recorded positive**.  The finite-model lane is closed for this source as well; what is left open is left open because it is true, not because the test is too weak.

## Idempotents, and the shape of the diagonal

Two facts about the squaring map fall straight out of the affine spectrum and match the bank exactly.

* `S(x) = (a+b)x + k`, so `x` is idempotent iff `s x = -k` with `s = a + b - 1`.  On the `R₁` branch `s = 0` and `k = 0`, so **every** element is idempotent and `S = id`; on the `R₂` branch `s` is a unit in every finite quotient, so there is **exactly one** idempotent.  Over the whole bank — orders 5, 7, 8, 9, 11, 13 — every model is either totally idempotent or has a single idempotent, with nothing in between.
* `y ◇ x = y` reads `(a-1)y = -(bx + k)`.  On the `R₁` branch `a - 1 = -b` is a unit, so this forces `y = x` and nothing else.  On the `R₂` branch `a² + a + 1 = 0`, so in characteristic 3 the value `a = 1` is allowed, and then the condition loses `y` entirely: the single element `x = -k/b` is a **right identity**.  That is what the two order-9 models do, and it is the reason the "read `x ◇ x` off the row of `x`" recovery has to be handled with care — see below.

The first fact is why the `…FromFin` half of the board is so reachable for 1516: on a totally idempotent model the idempotent companion `x □ y = (x = y ? x : x ◇ y)` **is** `◇`, so the reverse read is free, and on the remaining models the diagonal is a single exceptional point.

## What blocks the all-magma upgrade

For the 37 targets that the idempotent box settles, `StructuralFromFin` is proved and `StructuralFrom` is still open, and the gap is entirely the reverse read.  `DiagRow.definable_graph_row` recovers `x ◇ x` from `□` as *the value missing from the row of `x`*, which needs `RowQG`: every row of `◇` onto.  As recorded above 1516 gives that for free on a finite carrier, and in general only for the rows indexed by squares.

The natural way around it is to define the diagonal by the law rather than by counting.  Reading the law as
```
(x◇x) ◇ (y ◇ (y◇x)) = y
```
exhibits `x ◇ x` as *a* `z` with `z ◇ (y◇(y◇x)) = y`, for every `y` at once and with no surjectivity anywhere.  Translating that into `□` costs three side conditions, because `□` only reproduces `◇` off the diagonal, and the fallback when no witness exists costs a second clause:
```
Δ(x, z)  :=  ∃y [ y ≠ x  ∧  y ≠ y□x  ∧  z ≠ y□(y□x)  ∧  z □ (y□(y□x)) = y ]
             ∨  ( z = x  ∧  ∀w ∀y ¬[ y ≠ x ∧ y ≠ y□x ∧ w ≠ y□(y□x) ∧ w □ (y□(y□x)) = y ] ).
```
Each of the three inequalities is exactly what licenses one `□ ↦ ◇` rewrite, and each excludes at most one `y`: `y = x`, `y = S(S(x))` (if `y◇(y◇x) = S(x)` then the law returns `S(x)◇S(x) = y`), and the elements fixed by right multiplication by `x`.  Two of those three obligations are settled:

* **the fallback is a theorem.**  `(∀y, y = x ∨ y◇x = y ∨ y◇(y◇x) = x◇x) → x◇x = x` follows from 1516 alone, and Vampire gets it in seconds under every schedule — no cancellation axiom needed.  It is not vacuous either: the hypothesis really does hold somewhere.  On the characteristic-3 `R₂` models, where `a = 1` is allowed because `a² + a + 1 = 3 = 0`, the condition `y ◇ x = y` reads `bx + k = 0` and so holds for *every* `y` at the single right identity `x = −k/b`; a sweep of the whole bank finds 54 such `(model, x)` pairs and the conclusion `x◇x = x` holds at all 54.
* **the ∃-branch pins `z` uniquely** — but only by cancelling `y◇(y◇x)` on the right, and **right cancellation is precisely the fact that is not available without finiteness**.

So this route does not dodge the open question after all; it converts "every row is onto" into "one column cancels", which is the same wall seen from the other side.  It is still the shortest bridge on offer: a single lemma, `a ◇ c = b ◇ c → a = b` over all magmas, would carry 41 cells of the board at once, and would need no re-proof of any forward half — the 37 targets it would upgrade already have their `StructuralFromFin` companions verified.

## The reverse read, as a syntax search

`TermStructuralFrom` needs a pair of terms, not one: a `w` over `◇` satisfying the target, and a `v`
over `w` giving `◇` back.  Both halves are small enough to enumerate directly, and the bank is a
sharp filter for the first half — a `w` of at most five leaves that satisfies the target on all 32
models of order at most 27 is a genuine candidate.  Many targets have such a `w`, between 50 and 77
of them apiece; but running the second half over the same models, the *only* pairs that survive are
the trivial ones,

```
target 47 and 2098:  w = y ◇ x,  v = w         target 255 and 1489:  w = x ◇ y,  v = w
```

i.e. the cases where the "companion" is `◇` itself or its opposite.  Those are bank artifacts and
not implications: 1516 does not imply 255 or 1489 (the latter is the 35-element cohomological
counterexample cited at the top), so the uniform `w` is uniform only over the affine models.  For
every other open target the reverse read has no term of that size at all, which is the same wall as
in the previous section approached from the syntactic side: on an `R₁` model the whole clone is
`{(1-c)x + cy}`, and recovering `◇ = a x + b y` from `w = (1-c)x + cy` needs `c` to generate `b`
multiplicatively, which the coefficient-sum invariant below forbids in general.

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

/-!
# Every order from 26143 on carries a magma satisfying Equation 677

A self-contained Lean 4 file. It uses nothing but Lean's core library — no Mathlib, no
Batteries, no `lake` project — and compiles with a bare `lean SpectrumBound3.lean`, in about
two minutes and 1.8 GB of memory. It has been checked with Lean 4.32.2, 4.33.1, 4.34.1 and
4.35.0-rc2.

Write $x \diamond y$ for the magma operation (in Lean, `x * y` through the core `Mul` class).
Equation 677 of the Equational Theories Project is
$$x = y \diamond (x \diamond ((y \diamond x) \diamond y)). \tag{677}$$

The main theorem, `Spectrum677.exists_mul_of_ge`, says that **for every $n \ge 26143$ some
magma with exactly $n$ elements satisfies (677)**: there is a multiplication on `Fin n`
satisfying `Equation677`. `Spectrum677.exists_op_of_ge` restates it for a bare binary
operation on `Fin n`.

Write $A(n; a, b, c)$ for the affine magma $x \diamond y = a x + b y + c$ on $\mathbb{Z}/n$, and
$\Phi_{10}(\zeta) = \zeta^4 - \zeta^3 + \zeta^2 - \zeta + 1$ for the tenth cyclotomic polynomial.

## One gluing theorem

An order is recorded as a model on `{0, …, n - 1}` (`Spectrum677.HasModel`) with an idempotent
element (`Spectrum677.HasPtModel`, a *pointed* model). Every construction but the products, the
affine models and the Paley pencil is one theorem, `Spectrum677.GDD.isModel_glue`, applied to a
**group-divisible design** (`Spectrum677.GDD`): points split into groups, and blocks, two points
of different groups lying in exactly one block, which meets every group at most once. Put `m`
new points in front, give each group, together with the new points, a model in which the new
points form one and the same submagma, and give each block a model with every element
idempotent. Multiplying two points in a group containing both, or in the block through them,
gives a model of order `m` plus the number of points: at two points of one group the law is the
group's; at two points of different groups the computation stays in their block and multiplies
distinct points only (`Spectrum677.IsIdemModel.sep`), so it never consults the diagonal, which
belongs to the groups. That rests on every finite model being left cancellative
(`Spectrum677.IsModel.cancel`), a left translation being onto by (677). With `m = 0` this glues
arbitrary models on the groups; with `m = 1` it adjoins a point at infinity, an idempotent of
each group's model, to every group; with larger `m` a common submagma.

The designs come from three sources and one operation.

* **Truncated transversal designs** (`Spectrum677.Cut`): a `TD(K + 3, q)` with its groups `0`,
  `1`, `2` cut to intervals and the other `K` whole. A `TD(m + 1, q)` is the affine plane over a
  commutative ring with `q` elements and `m` labels whose differences are units
  (`Spectrum677.plane`); the ring axioms are those of core's `Lean.Grind.CommRing`, so that
  `grind` does the algebra. The rings are `ℤ / q`, and the fields $\mathbb{F}_4$,
  $\mathbb{F}_8$, $\mathbb{F}_9$, $\mathbb{F}_{16}$, $\mathbb{F}_{27}$, $\mathbb{F}_{7^3}$,
  $\mathbb{F}_{23^2}$, $\mathbb{F}_{29^2}$ in coordinates, whose inverse tables are checked;
  MacNeish's product combines them, and a difference matrix over $\mathbb{Z}/2 \times
  \mathbb{Z}/6$ gives `TD(5, 12)`. The tests `Spectrum677.tdOK`, `Spectrum677.tdOK167`,
  `Spectrum677.tdOK6` and `Spectrum677.tdOK5`, evaluated by the kernel, are conditions under
  which this gives `TD(82, q)`, `TD(167, q)`, `TD(6, n)` and `TD(5, g)`.
* **Designs developed from base blocks** (`Spectrum677.Dev`): `W` fixed points and `R` orbits
  of `ℤ / N`, the groups the fixed points and the classes modulo a divisor of `N` in each
  orbit, the blocks the translates of a few base blocks. `Spectrum677.Dev.check` certifies by
  evaluation that the keys of the ordered pairs of entries of the base blocks, invariants of
  translation, are distinct and are every key of a pair of points of different groups; then
  the translates form a design (`Spectrum677.Dev.gdd_valid`).
* **Inflation by a constant weight** (`Spectrum677.GDD.inflate`), Wilson's fundamental
  construction: every point becomes `w` points and every block of `k` points a design on `k w`
  points whose groups are the runs of `w` (`Spectrum677.GDD.inflate_valid`).

## The constructions

1. **Affine models** $A(m; a, b, 0)$, when $a b (1 + b^2) \equiv 1$ and
   $a + a^2 b^2 + b^3 \equiv 0 \pmod m$ (`Spectrum677.hasPtModel_of_affineOK`), and
   **products** (`Spectrum677.HasPtModel.mul`).
2. **The two-group truncation** $79 q + s + r$, `s, r ≤ q`, over `TD(82, q)`
   (`Spectrum677.hasPtModel_two`), and the **keep truncation** $79 q + s_1 + s_2 + s_3$,
   $s_1 + s_2 + s_3 \le q + 1$, over the cyclic plane, where a line's point in group `2` is the
   sum of its points in groups `0` and `1`, so that no line keeps all three
   (`Spectrum677.hasPtModel_keep`). The blocks have `79`, `80` or `81` points and carry T79,
   $A(5; 2, 4, 0) \times \mathbb{F}_2[\zeta]/(\Phi_{10})$ and $\mathbb{F}_3[\zeta]/(\Phi_{10})$.
3. **The run truncation** $165 q + s + r$ over `TD(167, q)` (`Spectrum677.hasPtModel_run`), its
   blocks of `165`, `166` and `167` points carrying a model glued along a pairwise balanced
   design developed under `ℤ / 41` (`Spectrum677.isIdemModel_165`), the Paley pencil
   $11 \cdot 15 + 1$ over $\mathbb{F}_2[\zeta]/(\Phi_{10})$ (`Spectrum677.isIdemModel_166`) and
   a two-piece translation-invariant model of order `167`, all with every element idempotent.
4. **The Paley pencil** $11 k + 1$ (`Spectrum677.hasPtModel_paley`): from a pointed model of
   order $k + 1$, one on $\{e\} \cup (\mathbb{Z}/11 \times \mathbb{Z}/k)$, every line
   $\{e\} \cup (\{x\} \times \mathbb{Z}/k)$ a copy of the smaller model, and points of
   different lines multiplying by $(x, s) \diamond (y, t) = ((1 - q) x + q y, t)$ or
   $((1 - q) x + q y, -s - t)$ at $q = 2$, as $y - x$ is a quadratic residue or not.
5. **A point at infinity** $1 + 5 g$ over `TD(5, g)` (`Spectrum677.hasPtModel_inf`), and the
   **two-group truncation with a point at infinity** $1 + 79 q + s + r$
   (`Spectrum677.hasPtModel_inftrunc`).
6. **A truncation adjoined at a cut group** (`Spectrum677.hasPtModel_sub2`,
   `Spectrum677.hasPtModel_subk`): the groups of a glued model are submagmas, so a two-group or
   keep truncation, its cut group `0` of `s` points numbered first, is a model of order
   `s + g` with a submagma of `s` points; on the five groups of `TD(5, g)`, all sharing it,
   with $A(5; 2, 4, 0)$ on the blocks, it gives $5 (79 q + r) + s$ and
   $5 (79 q + s_2 + s_3) + s_1$.
7. **The inflations** (`Spectrum677.hasPtModel_infl`, `Spectrum677.hasPtModel_iinfl`):
   `TD(6, n)` with its group `0` cut to `t ≤ n` points, every point given the weight `4 x`, and
   every block of five or six points replaced by a `5`-GDD of type $(4x)^5$ or $(4x)^6$ —
   `TD(5, 4)`, or a `5`-GDD of type $4^6$ developed under `ℤ / 4`, inflated by `TD(5, x)` — is a
   design with blocks of five points, five groups of `4 x n` points and one of `4 x t`. It
   gives $(5 n + t) \cdot 4 x$, and with a point at infinity $1 + (5 n + t) \cdot 4 x$.

The seeds are the empty and one-element magmas; the nine-element field
$\mathbb{F}_3[\omega]/(\omega^2 - \omega - 1)$ with $x \diamond y = x + \omega y$; the
translation-invariant model T29 and the two-piece models of orders `83` and `227`; two census
models, of orders `69` and `76`, by their tables; the fourth powers $j^4$,
$\mathbb{Z}/j[\zeta]/(\Phi_{10})$ with $x \diamond y = (1 - \zeta) x + \zeta y$
(`Spectrum677.hasPtModel_pow_four`); and five orders from designs:

* $53 = 4 \cdot 13 + 1$ (`Spectrum677.hasPtModel_53`): a resolvable design with blocks of four
  on $3 \cdot 13 + 1$ points, developed under `ℤ / 13`, with a point adjoined to every block of
  each parallel class, the `13` new points a hole carrying $A(13; 9, 11, 0)$;
* $360 = 5 + 5 \cdot 71$ (`Spectrum677.hasPtModel_360`): the submagma of `5` points of the
  census model of order `76` adjoined to the five groups of `TD(5, 71)`;
* `383` (`Spectrum677.hasPtModel_383`): a `5`-GDD of type $7^{52} 19^1$ developed under
  `ℤ / 91`, with $A(19; 7, 3, 0)$ and $A(7; 4, 1, 0)$ on its groups;
* `557` (`Spectrum677.hasPtModel_557`): a design with blocks of five points and a hole of `49`
  points, developed under `ℤ / 127`, with $A(49; 18, 8, 0)$ on the hole;
* $337 = 1 + (5 \cdot 5 + 3) \cdot 12$ (`Spectrum677.hasPtModel_337`): `TD(6, 5)` with a group
  cut to `3` points, inflated by the weight `12` with `TD(5, 12)` and a `5`-GDD of type
  $12^6$ developed under `ℤ / 12` on its blocks, and a point at infinity: $A(37; 26, 2, 0)$ and
  $A(61; 59, 3, 0)$ on its groups.

The orders themselves come from a certificate, which the kernel checks by evaluation.

* **Stage A.** A bitmap, `certH`, records $100370$ orders below $107601$. It is produced from
  the seeds by $10580$ instructions — $2308$ affine certificates, $3415$ products, $972$
  two-group, $202$ keep and $122$ run truncations, $299$ Paley pencils, $11$ two-group and $4$
  keep truncations adjoined at a cut group, $298$ points at infinity, $132$ two-group
  truncations with a point at infinity, and $1647$ inflations and $1170$ inflations with a
  point at infinity — checked in $27$ consecutive blocks, each produced from the bits below it;
  the $107$ instructions whose orders straddle two blocks are listed in both. `certH` records
  every order from $26143$ to $107600$; the largest order below $107601$ it misses is
  $26142$.
* **Stage B.** $1890$ two-group truncations read from `certH` cover every order from $107601$
  to $2491440$.
* **Stage C.** From an interval $[N, X]$ of orders, a two-group truncation $79 q + 0 + r$ with
  the largest suitable $q \le (X + 1 - N)/79$ coprime to $P_{79} = 2 \cdot 3 \cdot 5 \cdots 79$
  extends it to $[N, 80 q]$. After $5263$ such steps $X$ passes $80 (79 (P_{79} + 2) + N)$, and
  beyond that point a $q \equiv 1 \pmod{P_{79}}$ can always be found without search, so a
  strong induction covers every larger order.

## Where the bound stops

No instruction records $26142 = 2 \cdot 3 \cdot 4357$ from the orders of `certH`. Its
factorisations into two factors all have a factor `2`, `3` or `6`, none of which `certH`
records, so no product gives it; and no affine certificate exists modulo `2`, so none exists
modulo $26142$. The other instructions miss it whatever orders are recorded. A two-group
truncation, with or without a point at infinity, needs $323 \le q \le 330$, where `tdOK` fails
throughout: the nearest `q` it accepts are `317` and `331`, and
$81 \cdot 317 = 25677 < 26142 < 26149 = 79 \cdot 331$. A keep truncation needs a `q` coprime to
$P_{79}$ with $327 \le q \le 330$, of which there is none; a run truncation needs
$157 \le q \le 158$, where `tdOK167` fails; a truncation adjoined at a cut group needs $q = 66$,
which passes neither test. $26141$ is a multiple of neither `5` nor `11`, and
$26142 \equiv 2 \pmod 4$, which no inflation gives. This is the bound of the library's
`Magma677.mem_spectrum_of_ge_26143`, reached here by a smaller set of constructions and seeds.

## Conventions and trust

* Finite checks — the tables of the small models, the inverse tables of the finite fields, the
  conditions of the Paley pencil, the base blocks of the developed designs, and the three
  stages of the certificate — are decided by `decide`, the large ones with `decide +kernel`,
  which the kernel evaluates alone: no `native_decide`, no compiled code. Ring identities are
  left to `grind`. The main theorem depends on the axioms `propext`, `Classical.choice` and
  `Quot.sound` only.
* Nothing in the data is trusted: an instruction whose side conditions fail records nothing, a
  wrong bitmap fails its check, a base block in the wrong place fails `Dev.check`, and a wrong
  table fails its check. `SpectrumBound3_gen.py`, beside this file, computes the certificate
  section and replays every check before writing it.
* Products associate to the left: `y * x * y` is $(y \diamond x) \diamond y$.
* The loops of the certificate — `allBelow`, `bitsOf`, `blockAcc`, `ofWords`, `findGood` and
  `chain` — recurse with `Nat.rec` and `List.rec` directly, which keeps the kernel's evaluation
  cheap; `List.rec` has no compiled code in core Lean, so `bitsOf`, `Spectrum677.Dev.check` and
  the certificate machinery are `noncomputable`.
-/


set_option Elab.async false

universe u

/-- **Equation 677**: $x = y \diamond (x \diamond ((y \diamond x) \diamond y))$. -/
def Equation677 (M : Type u) [Mul M] : Prop :=
  ∀ x y : M, x = y * (x * (y * x * y))

namespace Spectrum677

/-- `if_pos`, restated so as not to depend on its name, which moves between versions of Lean. -/
theorem ite_of_pos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  simp [h]

/-- `if_neg`, restated for the same reason. -/
theorem ite_of_neg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by
  simp [h]

/-! ## Models on `{0, …, n - 1}`

A model of order `n` is coded as an operation on `Nat` that maps `{0, …, n - 1}` into itself
and satisfies Equation 677 there. The constructions below build such operations out of
smaller ones, which keeps them free of dependent types; `exists_fin_of_hasModel` turns the
result into an operation on `Fin n`. -/

/-- `op` is a **model of Equation 677 on `{0, …, n - 1}`**: it maps that set into itself and
satisfies $x = y \diamond (x \diamond ((y \diamond x) \diamond y))$ there. -/
structure IsModel (n : Nat) (op : Nat → Nat → Nat) : Prop where
  lt : ∀ x y, x < n → y < n → op x y < n
  eq : ∀ x y, x < n → y < n → op y (op x (op (op y x) y)) = x

/-- Some operation on `{0, …, n - 1}` satisfies Equation 677. -/
def HasModel (n : Nat) : Prop := ∃ op, IsModel n op

/-- Some operation on `{0, …, n - 1}` satisfies Equation 677 and has an idempotent element,
unless `n = 0`: a **pointed** model. -/
def HasPtModel (n : Nat) : Prop := ∃ op, IsModel n op ∧ (n = 0 ∨ ∃ e, e < n ∧ op e e = e)

theorem HasPtModel.hasModel {n : Nat} (h : HasPtModel n) : HasModel n :=
  let ⟨op, h, _⟩ := h
  ⟨op, h⟩

/-- **A model on `{0, …, n - 1}` is an operation on `Fin n` satisfying Equation 677.** -/
theorem exists_fin_of_hasModel {n : Nat} (h : HasModel n) :
    ∃ op : Fin n → Fin n → Fin n, ∀ x y : Fin n, x = op y (op x (op (op y x) y)) := by
  obtain ⟨op, hop⟩ := h
  exact ⟨fun x y => ⟨op x.val y.val, hop.lt _ _ x.isLt y.isLt⟩,
    fun x y => Fin.ext (hop.eq _ _ x.isLt y.isLt).symm⟩

/-- **Transport along an encoding.** Let `V` single out some elements of `α`, and let `enc`,
`dec` be mutually inverse bijections between them and `{0, …, n - 1}`. An operation on `α` that
preserves `V` and satisfies Equation 677 on it gives a model on `{0, …, n - 1}`. -/
theorem IsModel.of_encode {α : Type} (V : α → Prop) {n : Nat} (enc : α → Nat) (dec : Nat → α)
    (henc : ∀ a, V a → enc a < n) (hde : ∀ a, V a → dec (enc a) = a)
    (hdec : ∀ k, k < n → V (dec k)) (hed : ∀ k, k < n → enc (dec k) = k)
    (f : α → α → α) (hf : ∀ x y, V x → V y → V (f x y))
    (h : ∀ x y, V x → V y → f y (f x (f (f y x) y)) = x) :
    IsModel n (fun k l => enc (f (dec k) (dec l))) := by
  constructor
  · intro k l hk hl
    exact henc _ (hf _ _ (hdec k hk) (hdec l hl))
  · intro k l hk hl
    have hK := hdec k hk
    have hL := hdec l hl
    show enc (f (dec l) (dec (enc (f (dec k) (dec (enc (f (dec (enc (f (dec l) (dec k))))
      (dec l)))))))) = k
    rw [hde _ (hf _ _ hL hK), hde _ (hf _ _ (hf _ _ hL hK) hL),
      hde _ (hf _ _ hK (hf _ _ (hf _ _ hL hK) hL)), h _ _ hK hL, hed k hk]

/-! ### Encodings -/

/-- A bijection between a type and `{0, …, n - 1}`. -/
structure Enum (α : Type) (n : Nat) where
  enc : α → Nat
  dec : Nat → α
  enc_lt : ∀ a, enc a < n
  dec_enc : ∀ a, dec (enc a) = a
  enc_dec : ∀ k, k < n → enc (dec k) = k

/-- `a < m` and `b < n` give `a * n + b < m * n`. -/
theorem mul_add_lt {a b m n : Nat} (ha : a < m) (hb : b < n) : a * n + b < m * n := by
  have h1 : (a + 1) * n ≤ m * n := Nat.mul_le_mul_right n ha
  have h2 : (a + 1) * n = a * n + n := Nat.succ_mul a n
  omega

theorem mul_add_div {a b n : Nat} (hb : b < n) : (a * n + b) / n = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add]

theorem mul_add_mod {a b n : Nat} (hb : b < n) : (a * n + b) % n = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- `Fin j` is `{0, …, j - 1}`. -/
def Enum.fin (j : Nat) [NeZero j] : Enum (Fin j) j where
  enc := Fin.val
  dec k := ⟨k % j, Nat.mod_lt _ (Nat.pos_of_neZero j)⟩
  enc_lt a := a.isLt
  dec_enc a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
  enc_dec _ hk := Nat.mod_eq_of_lt hk

/-- Pairs, in base `n`: `(a, b) ↦ a n + b`. -/
def Enum.prod {α β : Type} {m n : Nat} (e₁ : Enum α m) (e₂ : Enum β n) : Enum (α × β) (m * n) where
  enc p := e₁.enc p.1 * n + e₂.enc p.2
  dec k := (e₁.dec (k / n), e₂.dec (k % n))
  enc_lt p := mul_add_lt (e₁.enc_lt p.1) (e₂.enc_lt p.2)
  dec_enc p := by
    have hb := e₂.enc_lt p.2
    simp only [mul_add_div hb, mul_add_mod hb, e₁.dec_enc, e₂.dec_enc]
  enc_dec k hk := by
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hk; omega)
    have h1 : k / n < m := (Nat.div_lt_iff_lt_mul hn).2 hk
    rw [e₁.enc_dec _ h1, e₂.enc_dec _ (Nat.mod_lt _ hn)]
    exact Nat.div_add_mod' k n

/-- **A model on a type with an encoding** gives a model on `{0, …, n - 1}`. -/
theorem Enum.isModel {α : Type} {n : Nat} (e : Enum α n) (f : α → α → α)
    (h : ∀ x y, f y (f x (f (f y x) y)) = x) :
    IsModel n (fun k l => e.enc (f (e.dec k) (e.dec l))) :=
  IsModel.of_encode (fun _ => True) e.enc e.dec (fun a _ => e.enc_lt a) (fun a _ => e.dec_enc a)
    (fun _ _ => trivial) e.enc_dec f (fun _ _ _ _ => trivial) (fun x y _ _ => h x y)

/-- The idempotent law transports along an encoding. -/
theorem Enum.idem {α : Type} {n : Nat} (e : Enum α n) (f : α → α → α) (h : ∀ x, f x x = x) :
    ∀ k, k < n → e.enc (f (e.dec k) (e.dec k)) = k := fun k hk => by
  rw [h, e.enc_dec k hk]

/-! ### Moving an idempotent to `0`

The Paley pencil wants the idempotent of its seed at `0`. Swapping two points is an encoding
of `{0, …, n - 1}` onto itself. -/

/-- The transposition of `0` and `e`. -/
def swap0 (e x : Nat) : Nat := if x = 0 then e else if x = e then 0 else x

theorem swap0_lt {e n x : Nat} (he : e < n) (hx : x < n) : swap0 e x < n := by
  unfold swap0
  split
  · exact he
  · split <;> omega

theorem swap0_swap0 (e x : Nat) : swap0 e (swap0 e x) = x := by
  unfold swap0
  by_cases h0 : x = 0
  · subst h0
    by_cases he : e = 0 <;> simp [he]
  · by_cases hx : x = e
    · subst hx
      simp [h0]
    · simp [h0, hx]

/-- **A pointed model can be relabelled to make `0` its idempotent.** -/
theorem exists_idem_zero {n : Nat} (h : HasPtModel n) (hn : 0 < n) :
    ∃ op, IsModel n op ∧ op 0 0 = 0 := by
  obtain ⟨op, hop, h0 | ⟨e, he, hee⟩⟩ := h
  · omega
  refine ⟨fun k l => swap0 e (op (swap0 e k) (swap0 e l)), ?_, ?_⟩
  · exact IsModel.of_encode (fun x => x < n) (swap0 e) (swap0 e) (fun _ h => swap0_lt he h)
      (fun _ _ => swap0_swap0 e _) (fun _ h => swap0_lt he h) (fun _ _ => swap0_swap0 e _) op
      (fun _ _ hx hy => hop.lt _ _ hx hy) (fun _ _ hx hy => hop.eq _ _ hx hy)
  · show swap0 e (op (swap0 e 0) (swap0 e 0)) = 0
    simp only [swap0, ite_true]
    rw [hee]
    by_cases he0 : e = 0 <;> simp [he0]

/-! ### The empty and one-element models, and products -/

theorem hasPtModel_zero : HasPtModel 0 :=
  ⟨fun x _ => x,
    ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩,
    Or.inl rfl⟩

theorem hasPtModel_one : HasPtModel 1 :=
  ⟨fun _ _ => 0, ⟨fun _ _ _ _ => Nat.zero_lt_one, fun x _ hx _ => by show 0 = x; omega⟩,
    Or.inr ⟨0, Nat.zero_lt_one, rfl⟩⟩

/-- The product of two operations, in base `n`: coordinates `(x / n, x % n)`. -/
def prodOp (n : Nat) (op₁ op₂ : Nat → Nat → Nat) (x y : Nat) : Nat :=
  op₁ (x / n) (y / n) * n + op₂ (x % n) (y % n)

/-- **The product of two models is a model.** -/
theorem IsModel.prod {m n : Nat} {op₁ op₂ : Nat → Nat → Nat} (h₁ : IsModel m op₁)
    (h₂ : IsModel n op₂) : IsModel (m * n) (prodOp n op₁ op₂) := by
  have key : ∀ x y, x < m * n → y < m * n →
      prodOp n op₁ op₂ x y < m * n ∧ prodOp n op₁ op₂ x y / n = op₁ (x / n) (y / n) ∧
        prodOp n op₁ op₂ x y % n = op₂ (x % n) (y % n) := by
    intro x y hx hy
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hx; omega)
    have hb := h₂.lt _ _ (Nat.mod_lt x hn) (Nat.mod_lt y hn)
    have ha := h₁.lt _ _ ((Nat.div_lt_iff_lt_mul hn).2 hx) ((Nat.div_lt_iff_lt_mul hn).2 hy)
    exact ⟨mul_add_lt ha hb, mul_add_div hb, mul_add_mod hb⟩
  constructor
  · intro x y hx hy
    exact (key x y hx hy).1
  · intro x y hx hy
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hx; omega)
    obtain ⟨l1, d1, m1⟩ := key y x hy hx
    obtain ⟨l2, d2, m2⟩ := key _ y l1 hy
    obtain ⟨_, d3, m3⟩ := key x _ hx l2
    show op₁ (y / n) (prodOp n op₁ op₂ x (prodOp n op₁ op₂ (prodOp n op₁ op₂ y x) y) / n) * n +
      op₂ (y % n) (prodOp n op₁ op₂ x (prodOp n op₁ op₂ (prodOp n op₁ op₂ y x) y) % n) = x
    have hxm : x / n < m := (Nat.div_lt_iff_lt_mul hn).2 hx
    have hym : y / n < m := (Nat.div_lt_iff_lt_mul hn).2 hy
    rw [d3, m3, d2, m2, d1, m1, h₁.eq _ _ hxm hym, h₂.eq _ _ (Nat.mod_lt x hn) (Nat.mod_lt y hn)]
    exact Nat.div_add_mod' x n

/-- The product of idempotent models is idempotent. -/
theorem prodOp_idem {m n : Nat} {op₁ op₂ : Nat → Nat → Nat} (h₁ : ∀ x, x < m → op₁ x x = x)
    (h₂ : ∀ x, x < n → op₂ x x = x) : ∀ x, x < m * n → prodOp n op₁ op₂ x x = x := by
  intro x hx
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hx; omega)
  unfold prodOp
  rw [h₁ _ ((Nat.div_lt_iff_lt_mul hn).2 hx), h₂ _ (Nat.mod_lt x hn)]
  exact Nat.div_add_mod' x n

/-- **The pointed orders are closed under multiplication.** -/
theorem HasPtModel.mul {m n : Nat} (h₁ : HasPtModel m) (h₂ : HasPtModel n) :
    HasPtModel (m * n) := by
  obtain ⟨op₁, H₁, h₁⟩ := h₁
  obtain ⟨op₂, H₂, h₂⟩ := h₂
  rcases h₁ with rfl | ⟨e₁, l₁, i₁⟩
  · exact ⟨_, H₁.prod H₂, Or.inl (Nat.zero_mul n)⟩
  rcases h₂ with rfl | ⟨e₂, l₂, i₂⟩
  · exact ⟨_, H₁.prod H₂, Or.inl (Nat.mul_zero m)⟩
  refine ⟨_, H₁.prod H₂, Or.inr ⟨e₁ * n + e₂, mul_add_lt l₁ l₂, ?_⟩⟩
  unfold prodOp
  rw [mul_add_div l₂, mul_add_mod l₂, i₁, i₂]

/-! ### Affine models over `ℤ / m` -/

/-- The **affine certificate** `(m, a, b)`: the conditions under which `x ◇ y = a x + b y` on
`ℤ / m` satisfies Equation 677. -/
def affineOK (m a b : Nat) : Bool :=
  a * b * (1 + b * b) % m == 1 % m && (a + a * a * b * b + b * b * b) % m == 0

/-- Remainders inside a sum can be dropped under an outer remainder. -/
theorem add_mul_mod_mod (A B Z m : Nat) : (A + B * (Z % m)) % m = (A + B * Z) % m := by
  rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]

theorem mul_mod_add_mod (A B Z m : Nat) : (B * (Z % m) + A) % m = (B * Z + A) % m := by
  rw [Nat.add_comm, add_mul_mod_mod, Nat.add_comm]

/-- Equation 677 for `x ◇ y = a x + b y`, expanded: `x` and `y` come out with the two
coefficients of the affine certificate. -/
theorem affine_expand (a b x y : Nat) :
    a * y + b * (a * x + b * (a * (a * y + b * x) + b * y)) =
      x * (a * b * (1 + b * b)) + y * (a + a * a * b * b + b * b * b) := by
  grind

/-- **An affine certificate gives a model**: `x ◇ y = a x + b y` on `ℤ / m`. -/
theorem isModel_affine {m a b : Nat} (hm : 0 < m) (h : affineOK m a b = true) :
    IsModel m (fun x y => (a * x + b * y) % m) := by
  simp only [affineOK, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨fun x y _ _ => Nat.mod_lt _ hm, fun x y hx _ => ?_⟩
  show (a * y + b * ((a * x + b * ((a * ((a * y + b * x) % m) + b * y) % m)) % m)) % m = x
  simp only [mul_mod_add_mod, add_mul_mod_mod]
  rw [affine_expand, Nat.add_mod,
    ← Nat.mul_mod_mod x, ← Nat.mul_mod_mod y, h.1, h.2, Nat.mul_mod_mod, Nat.mul_zero,
    Nat.zero_mod, Nat.add_zero, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hx]

/-- **An affine certificate gives a pointed order**: `0` is idempotent. -/
theorem hasPtModel_of_affineOK {m a b : Nat} (h : affineOK m a b = true) : HasPtModel m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact hasPtModel_zero
  exact ⟨_, isModel_affine hm h, Or.inr ⟨0, hm, by simp⟩⟩

/-! ## Deciding a finite table by evaluation -/

/-- `p k` holds for every `k < n`; a loop the kernel evaluates with `Nat.rec`. -/
def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && p k) n

theorem allBelow_spec {n : Nat} {p : Nat → Bool} (h : allBelow n p = true) :
    ∀ k, k < n → p k = true := by
  induction n with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro k hk
    have h' : (allBelow n p && p n) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hkn : k < n
    · exact ih h'.1 k hkn
    · rw [show k = n by omega]
      exact h'.2

/-- Closure and Equation 677 on `{0, …, n - 1}`, decided pair by pair. -/
def checkModel (n : Nat) (op : Nat → Nat → Nat) : Bool :=
  allBelow n fun x => allBelow n fun y => decide (op x y < n) && op y (op x (op (op y x) y)) == x

theorem isModel_of_checkModel {n : Nat} {op : Nat → Nat → Nat} (h : checkModel n op = true) :
    IsModel n op := by
  have H : ∀ x y, x < n → y < n → op x y < n ∧ op y (op x (op (op y x) y)) = x := by
    intro x y hx hy
    have := allBelow_spec (allBelow_spec h x hx) y hy
    simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this
  exact ⟨fun x y hx hy => (H x y hx hy).1, fun x y hx hy => (H x y hx hy).2⟩

/-- Pack a list of `w`-bit numbers into one natural number, the first entry lowest, so that
the kernel looks an entry up with one shift and one remainder. -/
def pack (w : Nat) (l : List Nat) : Nat := l.foldr (fun a acc => acc <<< w ||| a) 0

/-! ## Left cancellation, and models with every element idempotent

In a model on `{0, …, n - 1}` every left translation `y ◇ -` is onto, since
`x = y ◇ (x ◇ ((y ◇ x) ◇ y))`; a map of a finite set onto itself is one to one, so every
model is left cancellative (`Spectrum677.IsModel.cancel`). In a model with every element
idempotent, the law at two distinct points then multiplies only distinct points
(`Spectrum677.IsIdemModel.sep`), so it never consults the diagonal. -/

/-- No map sends `{0, …, k - 1}` onto `{0, …, k}`. -/
theorem no_surj : ∀ (k : Nat) (g : Nat → Nat), (∀ y, y < k + 1 → ∃ x, x < k ∧ g x = y) → False
  | 0, g, h => by
    obtain ⟨x, hx, -⟩ := h 0 (by omega)
    omega
  | k + 1, g, h => by
    apply no_surj k (fun x => if g x < g k then g x else g x - 1)
    intro y hy
    obtain ⟨x, hx, hgx⟩ := h (if y < g k then y else y + 1) (by split <;> omega)
    have hxk : x ≠ k := by
      intro e
      subst e
      split at hgx <;> omega
    refine ⟨x, by omega, ?_⟩
    show (if g x < g k then g x else g x - 1) = y
    rw [hgx]
    by_cases hyc : y < g k
    · rw [ite_of_pos hyc, ite_of_pos hyc]
    · rw [ite_of_neg hyc, ite_of_neg (by omega)]
      omega

/-- **A map of `{0, …, n - 1}` onto itself is one to one.** -/
theorem inj_of_surj {n : Nat} {f : Nat → Nat} (hs : ∀ y, y < n → ∃ x, x < n ∧ f x = y)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : f a = f b) : a = b := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  apply no_surj k (fun x => f (if x = b then k else x))
  intro y hy
  obtain ⟨z, hz, hfz⟩ := hs y hy
  obtain ⟨z', hz', hz'b, hfz'⟩ : ∃ z', z' < k + 1 ∧ z' ≠ b ∧ f z' = y := by
    by_cases hzb : z = b
    · exact ⟨a, ha, hne, by rw [hab, ← hzb, hfz]⟩
    · exact ⟨z, hz, hzb, hfz⟩
  by_cases hk : z' = k
  · refine ⟨b, by omega, ?_⟩
    simp only [ite_true]
    rw [← hk, hfz']
  · refine ⟨z', by omega, ?_⟩
    simp only [hz'b, ite_false]
    exact hfz'

/-- **Every model is left cancellative.** -/
theorem IsModel.cancel {n : Nat} {op : Nat → Nat → Nat} (h : IsModel n op) {y x x' : Nat}
    (hy : y < n) (hx : x < n) (hx' : x' < n) (he : op y x = op y x') : x = x' :=
  inj_of_surj (f := op y)
    (fun z hz => ⟨_, h.lt _ _ hz (h.lt _ _ (h.lt _ _ hy hz) hy), h.eq z y hz hy⟩) hx hx' he

/-- A model with **every element idempotent**. -/
structure IsIdemModel (n : Nat) (op : Nat → Nat → Nat) : Prop extends IsModel n op where
  idem : ∀ x, x < n → op x x = x

/-- **In an idempotent model the law at two distinct points multiplies only distinct points.**
At distinct `x`, `y`: `y ◇ x = y = y ◇ y` would cancel to `x = y`; `(y ◇ x) ◇ y = x` would make
the law read `y ◇ (x ◇ x) = x`, so `y ◇ x = x` and then `x ◇ y = x = x ◇ x`; and
`x ◇ ((y ◇ x) ◇ y) = y` would make the law read `y ◇ y = x`. -/
theorem IsIdemModel.sep {n : Nat} {op : Nat → Nat → Nat} (h : IsIdemModel n op) {x y : Nat}
    (hx : x < n) (hy : y < n) (hxy : x ≠ y) :
    op y x ≠ y ∧ op (op y x) y ≠ x ∧ op x (op (op y x) y) ≠ y := by
  refine ⟨fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · exact hxy (h.cancel hy hx hy (h1.trans (h.idem y hy).symm))
  · have h677 := h.eq x y hx hy
    rw [h2, h.idem x hx] at h677
    rw [h677] at h2
    exact hxy (h.cancel hx hy hx (h2.trans (h.idem x hx).symm)).symm
  · have h677 := h.eq x y hx hy
    rw [h3, h.idem y hy] at h677
    exact hxy h677.symm

/-- **Equation 677 through a chart.** If `op` agrees along `ι` with a model `f` of order `m`,
it satisfies the law at any two points in the image of `ι`. -/
theorem eq677_of_chart {m : Nat} {f : Nat → Nat → Nat} (hf : IsModel m f)
    {op : Nat → Nat → Nat} {ι : Nat → Nat}
    (hι : ∀ a b, a < m → b < m → op (ι a) (ι b) = ι (f a b)) {i j : Nat} (hi : i < m)
    (hj : j < m) : op (ι j) (op (ι i) (op (op (ι j) (ι i)) (ι j))) = ι i := by
  have h1 := hf.lt _ _ hj hi
  have h2 := hf.lt _ _ h1 hj
  have h3 := hf.lt _ _ hi h2
  rw [hι _ _ hj hi, hι _ _ h1 hj, hι _ _ hi h2, hι _ _ hj h3, hf.eq _ _ hi hj]

/-- **Equation 677 through a block chart.** If `op` agrees along `ι` with an idempotent model
`f` at distinct points, it satisfies the law at the images of any two distinct points. -/
theorem eq677_of_blockChart {m : Nat} {f : Nat → Nat → Nat} (hf : IsIdemModel m f)
    {op : Nat → Nat → Nat} {ι : Nat → Nat}
    (hι : ∀ a b, a < m → b < m → a ≠ b → op (ι a) (ι b) = ι (f a b)) {i j : Nat} (hi : i < m)
    (hj : j < m) (hij : i ≠ j) : op (ι j) (op (ι i) (op (op (ι j) (ι i)) (ι j))) = ι i := by
  obtain ⟨s1, s2, s3⟩ := hf.sep hi hj hij
  have h1 := hf.lt _ _ hj hi
  have h2 := hf.lt _ _ h1 hj
  have h3 := hf.lt _ _ hi h2
  rw [hι _ _ hj hi (Ne.symm hij), hι _ _ h1 hj s1, hι _ _ hi h2 (Ne.symm s2), hι _ _ hj h3 s3.symm,
    hf.eq _ _ hi hj]

/-! ## Gluing along a group-divisible design

A **group-divisible design** (`Spectrum677.GDD`) on the points `{0, …, n - 1}` partitions them
into groups and has blocks, two points of different groups lying in exactly one block and a
block meeting a group at most once. Here a point's group is `grp x`; the group `g` has `gsz g`
points, `gpt g i` the `i`-th of them and `gidx x` the index of `x` in its own group; and the
block through two points of different groups is `blk x y`, with `sz b` points, `pt b i` its
`i`-th point and `idx b x` the index of `x` in it. Blocks are of an arbitrary type `B`.

Put `m` new points `0, …, m - 1` in front, shift the design up by `m`, and give each group,
together with the new points, a model in which the new points form the same submagma (a model
of order `m`); give each block an idempotent model. Two points multiply in the model of a group
containing both, and two points of different groups in the block through them
(`Spectrum677.GDD.glue`). The result is a model (`Spectrum677.GDD.isModel_glue`): the law at two
points of one group, or at a new point, is that group's; at two points of different groups,
the whole computation stays in their block and multiplies distinct points only. With `m = 0`
this is the gluing of arbitrary group models along a design with idempotent blocks; with
`m > 0` the new points are a **common submagma** adjoined to every group. -/

/-- The data of a **group-divisible design**: groups, and the block through two points of
different groups. `Spectrum677.GDD.Valid` states what makes it a design. -/
structure GDD (B : Type) where
  n : Nat
  grp : Nat → Nat
  gsz : Nat → Nat
  gpt : Nat → Nat → Nat
  gidx : Nat → Nat
  blk : Nat → Nat → B
  sz : B → Nat
  pt : B → Nat → Nat
  idx : B → Nat → Nat

namespace GDD

variable {B : Type}

/-- Two points of different groups. -/
def Cross (D : GDD B) (x y : Nat) : Prop := x < D.n ∧ y < D.n ∧ D.grp x ≠ D.grp y

/-- What makes the data a group-divisible design: each group lists its points without
repetition, the block through two points of different groups contains them and lists its
points without repetition, its points lie in distinct groups, and the block through two of its
points is itself. -/
structure Valid (D : GDD B) : Prop where
  gidx_lt : ∀ x, x < D.n → D.gidx x < D.gsz (D.grp x)
  gpt_gidx : ∀ x, x < D.n → D.gpt (D.grp x) (D.gidx x) = x
  gpt_lt : ∀ x i, x < D.n → i < D.gsz (D.grp x) → D.gpt (D.grp x) i < D.n
  grp_gpt : ∀ x i, x < D.n → i < D.gsz (D.grp x) → D.grp (D.gpt (D.grp x) i) = D.grp x
  gidx_gpt : ∀ x i, x < D.n → i < D.gsz (D.grp x) → D.gidx (D.gpt (D.grp x) i) = i
  idx_lt : ∀ x y, D.Cross x y → D.idx (D.blk x y) x < D.sz (D.blk x y)
  pt_idx : ∀ x y, D.Cross x y → D.pt (D.blk x y) (D.idx (D.blk x y) x) = x
  idx_lt' : ∀ x y, D.Cross x y → D.idx (D.blk x y) y < D.sz (D.blk x y)
  pt_idx' : ∀ x y, D.Cross x y → D.pt (D.blk x y) (D.idx (D.blk x y) y) = y
  pt_lt : ∀ x y i, D.Cross x y → i < D.sz (D.blk x y) → D.pt (D.blk x y) i < D.n
  idx_pt : ∀ x y i, D.Cross x y → i < D.sz (D.blk x y) →
    D.idx (D.blk x y) (D.pt (D.blk x y) i) = i
  cross_pt : ∀ x y i j, D.Cross x y → i < D.sz (D.blk x y) → j < D.sz (D.blk x y) → i ≠ j →
    D.grp (D.pt (D.blk x y) i) ≠ D.grp (D.pt (D.blk x y) j)
  blk_pt : ∀ x y i j, D.Cross x y → i < D.sz (D.blk x y) → j < D.sz (D.blk x y) → i ≠ j →
    D.blk (D.pt (D.blk x y) i) (D.pt (D.blk x y) j) = D.blk x y

variable (D : GDD B)

/-- The glued point at index `i` of the chart of group `g`: the new point `i` for `i < m`, and
the point `i - m` of the group, shifted by `m`, otherwise. -/
def gemb (m g i : Nat) : Nat := if i < m then i else m + D.gpt g (i - m)

/-- The index of the glued point `x` in the chart of its group. -/
def gloc (m x : Nat) : Nat := if x < m then x else m + D.gidx (x - m)

/-- **The glued operation**, with the model `emod` on the `m` new points, `gmod g` on the
group `g` with them, and `bmod k` on the blocks of `k` points. -/
def glue (m : Nat) (emod : Nat → Nat → Nat) (gmod bmod : Nat → Nat → Nat → Nat)
    (x y : Nat) : Nat :=
  if x < m ∧ y < m then emod x y
  else if x < m ∨ y < m ∨ D.grp (x - m) = D.grp (y - m) then
    D.gemb m (if x < m then D.grp (y - m) else D.grp (x - m))
      (gmod (if x < m then D.grp (y - m) else D.grp (x - m)) (D.gloc m x) (D.gloc m y))
  else
    m + D.pt (D.blk (x - m) (y - m)) (bmod (D.sz (D.blk (x - m) (y - m)))
      (D.idx (D.blk (x - m) (y - m)) (x - m)) (D.idx (D.blk (x - m) (y - m)) (y - m)))

/-- What the gluing needs: a design, a model on the new points, on each group with the new
points a model agreeing with it there, and an idempotent model on each block. -/
structure GlueOK (m : Nat) (emod : Nat → Nat → Nat) (gmod bmod : Nat → Nat → Nat → Nat) :
    Prop where
  valid : D.Valid
  he : IsModel m emod
  hg : ∀ x, x < D.n → IsModel (m + D.gsz (D.grp x)) (gmod (D.grp x))
  hge : ∀ x, x < D.n → ∀ a b, a < m → b < m → gmod (D.grp x) a b = emod a b
  hb : ∀ x y, D.Cross x y → IsIdemModel (D.sz (D.blk x y)) (bmod (D.sz (D.blk x y)))

variable {D}

theorem glue_ee {m : Nat} {emod : Nat → Nat → Nat} {gmod bmod : Nat → Nat → Nat → Nat}
    {x y : Nat} (hx : x < m) (hy : y < m) : D.glue m emod gmod bmod x y = emod x y := by
  unfold glue
  rw [ite_of_pos ⟨hx, hy⟩]

theorem glue_grp {m : Nat} {emod : Nat → Nat → Nat} {gmod bmod : Nat → Nat → Nat → Nat}
    {x y g : Nat} (hxy : ¬(x < m ∧ y < m))
    (hg : (x < m → D.grp (y - m) = g) ∧ (¬x < m → D.grp (x - m) = g))
    (hc : x < m ∨ y < m ∨ D.grp (x - m) = D.grp (y - m)) :
    D.glue m emod gmod bmod x y = D.gemb m g (gmod g (D.gloc m x) (D.gloc m y)) := by
  unfold glue
  rw [ite_of_neg hxy, ite_of_pos hc]
  by_cases hx : x < m
  · rw [ite_of_pos hx, hg.1 hx]
  · rw [ite_of_neg hx, hg.2 hx]

theorem glue_blk {m : Nat} {emod : Nat → Nat → Nat} {gmod bmod : Nat → Nat → Nat → Nat}
    {x y : Nat} (hx : ¬x < m) (hy : ¬y < m) (hc : D.grp (x - m) ≠ D.grp (y - m)) :
    D.glue m emod gmod bmod x y = m + D.pt (D.blk (x - m) (y - m))
      (bmod (D.sz (D.blk (x - m) (y - m))) (D.idx (D.blk (x - m) (y - m)) (x - m))
        (D.idx (D.blk (x - m) (y - m)) (y - m))) := by
  unfold glue
  rw [ite_of_neg (fun h => hx h.1), ite_of_neg (by omega)]

section
variable {m : Nat} {emod : Nat → Nat → Nat} {gmod bmod : Nat → Nat → Nat → Nat}

/-- The chart of the group of the point `x` of the design. -/
theorem gemb_spec (hv : D.Valid) {x i : Nat} (hx : x < D.n) (hi : i < m + D.gsz (D.grp x)) :
    D.gemb m (D.grp x) i < m + D.n ∧ (D.gemb m (D.grp x) i < m ↔ i < m) ∧
      (¬i < m → D.grp (D.gemb m (D.grp x) i - m) = D.grp x) ∧
      D.gloc m (D.gemb m (D.grp x) i) = i := by
  unfold gemb gloc
  by_cases him : i < m
  · rw [ite_of_pos him, ite_of_pos him]
    exact ⟨by omega, Iff.rfl, fun h => absurd him h, rfl⟩
  · rw [ite_of_neg him]
    have h1 := hv.gpt_lt x (i - m) hx (by omega)
    have h2 := hv.grp_gpt x (i - m) hx (by omega)
    have h3 := hv.gidx_gpt x (i - m) hx (by omega)
    refine ⟨by omega, by omega, fun _ => ?_, ?_⟩
    · rw [show m + D.gpt (D.grp x) (i - m) - m = D.gpt (D.grp x) (i - m) by omega, h2]
    · rw [ite_of_neg (by omega), show m + D.gpt (D.grp x) (i - m) - m =
        D.gpt (D.grp x) (i - m) by omega, h3]
      omega

theorem gloc_spec (hv : D.Valid) {x : Nat} (hx : x < m + D.n) (hxm : ¬x < m) :
    D.gloc m x < m + D.gsz (D.grp (x - m)) ∧ D.gemb m (D.grp (x - m)) (D.gloc m x) = x := by
  unfold gemb gloc
  rw [ite_of_neg hxm, ite_of_neg (by omega)]
  have h1 := hv.gidx_lt (x - m) (by omega)
  have h2 := hv.gpt_gidx (x - m) (by omega)
  refine ⟨by omega, ?_⟩
  rw [show m + D.gidx (x - m) - m = D.gidx (x - m) by omega, h2]
  omega

/-- **The group chart**: on the group of `x` with the new points, the glued operation is the
group's model. -/
theorem glue_gemb (hok : D.GlueOK m emod gmod bmod) {x a b : Nat} (hx : x < D.n)
    (ha : a < m + D.gsz (D.grp x)) (hb : b < m + D.gsz (D.grp x)) :
    D.glue m emod gmod bmod (D.gemb m (D.grp x) a) (D.gemb m (D.grp x) b) =
      D.gemb m (D.grp x) (gmod (D.grp x) a b) := by
  obtain ⟨ea1, ea2, ea3, ea4⟩ := gemb_spec (m := m) hok.valid hx ha
  obtain ⟨eb1, eb2, eb3, eb4⟩ := gemb_spec (m := m) hok.valid hx hb
  by_cases hab : a < m ∧ b < m
  · rw [glue_ee (ea2.2 hab.1) (eb2.2 hab.2), hok.hge x hx a b hab.1 hab.2]
    have hc := (hok.he).lt a b hab.1 hab.2
    unfold gemb
    rw [ite_of_pos hab.1, ite_of_pos hab.2, ite_of_pos hc]
  · rw [glue_grp (g := D.grp x), ea4, eb4]
    · intro h
      exact hab ⟨ea2.1 h.1, eb2.1 h.2⟩
    · constructor
      · intro h
        have hb' : ¬b < m := fun hb' => hab ⟨ea2.1 h, hb'⟩
        exact eb3 hb'
      · intro h
        exact ea3 (fun h' => h (ea2.2 h'))
    · by_cases h1 : a < m
      · exact Or.inl (ea2.2 h1)
      by_cases h2 : b < m
      · exact Or.inr (Or.inl (eb2.2 h2))
      · exact Or.inr (Or.inr (by rw [ea3 h1, eb3 h2]))

/-- **The block chart**: on the block through two points of different groups, the glued
operation is the block's model at distinct points. -/
theorem glue_blk_pt (hok : D.GlueOK m emod gmod bmod) {x y i j : Nat} (hxy : D.Cross x y)
    (hi : i < D.sz (D.blk x y)) (hj : j < D.sz (D.blk x y)) (hij : i ≠ j) :
    D.glue m emod gmod bmod (m + D.pt (D.blk x y) i) (m + D.pt (D.blk x y) j) =
      m + D.pt (D.blk x y) (bmod (D.sz (D.blk x y)) i j) := by
  have hv := hok.valid
  rw [glue_blk (by omega) (by omega)]
  · simp only [Nat.add_sub_cancel_left]
    rw [hv.blk_pt x y i j hxy hi hj hij, hv.idx_pt x y i hxy hi, hv.idx_pt x y j hxy hj]
  · simp only [Nat.add_sub_cancel_left]
    exact hv.cross_pt x y i j hxy hi hj hij

theorem glue_lt (hok : D.GlueOK m emod gmod bmod) {x y : Nat} (hx : x < m + D.n)
    (hy : y < m + D.n) : D.glue m emod gmod bmod x y < m + D.n := by
  have hv := hok.valid
  by_cases hxy : x < m ∧ y < m
  · rw [glue_ee hxy.1 hxy.2]
    have := hok.he.lt x y hxy.1 hxy.2
    omega
  by_cases hc : x < m ∨ y < m ∨ D.grp (x - m) = D.grp (y - m)
  · by_cases hxm : x < m
    · have hym : ¬y < m := fun h => hxy ⟨hxm, h⟩
      obtain ⟨l1, e1⟩ := gloc_spec hv hy hym
      have l0 : D.gloc m x < m + D.gsz (D.grp (y - m)) := by
        unfold gloc
        rw [ite_of_pos hxm]
        omega
      rw [glue_grp (g := D.grp (y - m)) hxy ⟨fun _ => rfl, fun h => absurd hxm h⟩ hc]
      exact (gemb_spec hv (by omega) ((hok.hg _ (by omega)).lt _ _ l0 l1)).1
    · obtain ⟨l1, e1⟩ := gloc_spec hv hx hxm
      have l2 : D.gloc m y < m + D.gsz (D.grp (x - m)) := by
        by_cases hym : y < m
        · unfold gloc
          rw [ite_of_pos hym]
          omega
        · have hg : D.grp (x - m) = D.grp (y - m) := by omega
          rw [hg]
          exact (gloc_spec hv hy hym).1
      rw [glue_grp (g := D.grp (x - m)) hxy ⟨fun h => absurd h hxm, fun _ => rfl⟩ hc]
      exact (gemb_spec hv (by omega) ((hok.hg _ (by omega)).lt _ _ l1 l2)).1
  · have hxm : ¬x < m := by omega
    have hym : ¬y < m := by omega
    have hg : D.grp (x - m) ≠ D.grp (y - m) := by omega
    have hxy' : D.Cross (x - m) (y - m) := ⟨by omega, by omega, hg⟩
    rw [glue_blk hxm hym hg]
    have h1 := hv.idx_lt _ _ hxy'
    have h2 := hv.idx_lt' _ _ hxy'
    have h3 := hv.pt_lt _ _ _ hxy' ((hok.hb _ _ hxy').lt _ _ h1 h2)
    omega

/-- **The glued operation is a model.** -/
theorem isModel_glue (hok : D.GlueOK m emod gmod bmod) :
    IsModel (m + D.n) (D.glue m emod gmod bmod) := by
  have hv := hok.valid
  refine ⟨fun x y hx hy => glue_lt hok hx hy, fun x y hx hy => ?_⟩
  by_cases hxy : x < m ∧ y < m
  · have := eq677_of_chart (op := D.glue m emod gmod bmod) (ι := fun a => a) hok.he
      (fun a b ha hb => glue_ee ha hb) hxy.1 hxy.2
    exact this
  by_cases hc : x < m ∨ y < m ∨ D.grp (x - m) = D.grp (y - m)
  · -- the group of whichever point is outside the new points
    obtain ⟨z, hz, hzm, hgx, hgy⟩ : ∃ z, z < m + D.n ∧ ¬z < m ∧
        (¬x < m → D.grp (x - m) = D.grp (z - m)) ∧ (¬y < m → D.grp (y - m) = D.grp (z - m)) := by
      by_cases hxm : x < m
      · have hym : ¬y < m := fun h => hxy ⟨hxm, h⟩
        exact ⟨y, hy, hym, fun h => absurd hxm h, fun _ => rfl⟩
      · refine ⟨x, hx, hxm, fun _ => rfl, fun hym => ?_⟩
        rcases hc with h | h | h
        · exact absurd h hxm
        · exact absurd h hym
        · exact h.symm
    have hzn : z - m < D.n := by omega
    have hch : ∀ w, w < m + D.n → (¬w < m → D.grp (w - m) = D.grp (z - m)) →
        D.gloc m w < m + D.gsz (D.grp (z - m)) ∧
          D.gemb m (D.grp (z - m)) (D.gloc m w) = w := by
      intro w hw hwg
      by_cases hwm : w < m
      · unfold gloc gemb
        rw [ite_of_pos hwm, ite_of_pos hwm]
        exact ⟨by omega, rfl⟩
      · have := gloc_spec hv hw hwm
        rw [← hwg hwm]
        exact this
    obtain ⟨lx, ex⟩ := hch x hx hgx
    obtain ⟨ly, ey⟩ := hch y hy hgy
    have := eq677_of_chart (op := D.glue m emod gmod bmod) (ι := D.gemb m (D.grp (z - m)))
      (hok.hg _ hzn) (fun a b ha hb => glue_gemb hok hzn ha hb) lx ly
    rwa [ex, ey] at this
  · have hxm : ¬x < m := by omega
    have hym : ¬y < m := by omega
    have hg : D.grp (x - m) ≠ D.grp (y - m) := by omega
    have hxy' : D.Cross (x - m) (y - m) := ⟨by omega, by omega, hg⟩
    have h1 := hv.idx_lt _ _ hxy'
    have h2 := hv.idx_lt' _ _ hxy'
    have hne : D.idx (D.blk (x - m) (y - m)) (x - m) ≠ D.idx (D.blk (x - m) (y - m)) (y - m) := by
      intro e
      apply hg
      have := congrArg (D.pt (D.blk (x - m) (y - m))) e
      rw [hv.pt_idx _ _ hxy', hv.pt_idx' _ _ hxy'] at this
      rw [this]
    have := eq677_of_blockChart (op := D.glue m emod gmod bmod)
      (ι := fun i => m + D.pt (D.blk (x - m) (y - m)) i) (hok.hb _ _ hxy')
      (fun a b ha hb hab => glue_blk_pt hok hxy' ha hb hab) h1 h2 hne
    simp only [hv.pt_idx _ _ hxy', hv.pt_idx' _ _ hxy'] at this
    rwa [show m + (x - m) = x by omega, show m + (y - m) = y by omega] at this

/-- A new point idempotent in its model stays idempotent. -/
theorem glue_idem_e {e : Nat} (he : e < m) (hee : emod e e = e) :
    D.glue m emod gmod bmod e e = e := by
  rw [glue_ee he he, hee]

/-- A point of the design idempotent in its group's model stays idempotent. -/
theorem glue_idem_g (hok : D.GlueOK m emod gmod bmod) {x i : Nat} (hx : x < D.n)
    (hi : i < m + D.gsz (D.grp x)) (hii : gmod (D.grp x) i i = i) :
    D.glue m emod gmod bmod (D.gemb m (D.grp x) i) (D.gemb m (D.grp x) i) =
      D.gemb m (D.grp x) i := by
  rw [glue_gemb hok hx hi hi, hii]

end

end GDD
/-! ## Transversal designs

A transversal design `TD(k, g)` has `k` groups of `g` points and a set of lines, each line
meeting each group in one point, such that two points of different groups lie on exactly one
line. Here the points of group `i` are numbered `0, …, g - 1`, `pt L i` is the point of the
line `L` in group `i`, and `line i c j d` is the line through the point `c` of group `i` and the
point `d` of group `j`. -/

/-- A **transversal design** `TD(k, g)`. -/
structure TD (k g : Nat) where
  /-- The lines. -/
  Line : Type
  /-- The point of a line in a group. -/
  pt : Line → Nat → Nat
  /-- The line through a point of one group and a point of another. -/
  line : Nat → Nat → Nat → Nat → Line
  pt_lt : ∀ L i, i < k → pt L i < g
  pt_line : ∀ i j c d, i < k → j < k → i ≠ j → c < g → d < g →
    pt (line i c j d) i = c ∧ pt (line i c j d) j = d
  line_pt : ∀ L i j, i < k → j < k → i ≠ j → line i (pt L i) j (pt L j) = L

namespace TD

/-- **MacNeish's product** `TD(k, g₁) × TD(k, g₂) → TD(k, g₁ g₂)`: a point of a group is a pair
of points, in base `g₂`, and a line a pair of lines. -/
def prod {k g₁ g₂ : Nat} (D₁ : TD k g₁) (D₂ : TD k g₂) : TD k (g₁ * g₂) where
  Line := D₁.Line × D₂.Line
  pt L i := D₁.pt L.1 i * g₂ + D₂.pt L.2 i
  line i c j d := (D₁.line i (c / g₂) j (d / g₂), D₂.line i (c % g₂) j (d % g₂))
  pt_lt L i hi := mul_add_lt (D₁.pt_lt L.1 i hi) (D₂.pt_lt L.2 i hi)
  pt_line i j c d hi hj hij hc hd := by
    have hg : 0 < g₂ := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hc; omega)
    obtain ⟨a1, a2⟩ := D₁.pt_line i j _ _ hi hj hij ((Nat.div_lt_iff_lt_mul hg).2 hc)
      ((Nat.div_lt_iff_lt_mul hg).2 hd)
    obtain ⟨b1, b2⟩ := D₂.pt_line i j _ _ hi hj hij (Nat.mod_lt c hg) (Nat.mod_lt d hg)
    rw [a1, b1, a2, b2]
    exact ⟨Nat.div_add_mod' c g₂, Nat.div_add_mod' d g₂⟩
  line_pt L i j hi hj hij := by
    have hi2 := D₂.pt_lt L.2 i hi
    have hj2 := D₂.pt_lt L.2 j hj
    rw [mul_add_div hi2, mul_add_mod hi2, mul_add_div hj2, mul_add_mod hj2,
      D₁.line_pt L.1 i j hi hj hij, D₂.line_pt L.2 i j hi hj hij]

end TD

/-! ### The affine plane over a commutative ring

Let `R` be a commutative ring coded on `{0, …, q - 1}`, and `lam 0, …, lam (m - 1)` elements of
`R` whose differences are units. The lines `(a, b) ∈ R × R` and the groups `0` (the slopes)
and `i + 1` (the points `a · lam i + b`) form a `TD(m + 1, q)`. The ring axioms come from
`Lean.Grind.CommRing`, so that `grind` does the algebra. -/

section Plane

variable {R : Type} [Lean.Grind.CommRing R]

/-- An inverse of `x`, when there is one. -/
noncomputable def ringInv (x : R) : R := @Classical.epsilon R ⟨0⟩ (fun u => x * u = 1)

theorem mul_ringInv {x : R} (h : ∃ u, x * u = 1) : x * ringInv x = 1 :=
  Classical.epsilon_spec h

/-- The point of the line `L = (a, b)` in group `i`: its slope `a` in group `0`, and
`a · lam (i - 1) + b` in group `i ≥ 1`. -/
def planePt {q : Nat} (e : Enum R q) (lam : Nat → R) (L : R × R) : Nat → Nat
  | 0 => e.enc L.1
  | i + 1 => e.enc (L.1 * lam i + L.2)

/-- The line through the point `c` of group `i` and the point `d` of group `j`. -/
noncomputable def planeLine {q : Nat} (e : Enum R q) (lam : Nat → R) :
    Nat → Nat → Nat → Nat → R × R
  | 0, _, 0, _ => (0, 0)
  | 0, c, j + 1, d => (e.dec c, e.dec d - e.dec c * lam j)
  | i + 1, c, 0, d => (e.dec d, e.dec c - e.dec d * lam i)
  | i + 1, c, j + 1, d =>
    ((e.dec d - e.dec c) * ringInv (lam j - lam i),
      e.dec c - (e.dec d - e.dec c) * ringInv (lam j - lam i) * lam i)

/-- **The affine plane over `R`** is a `TD(m + 1, q)`. -/
noncomputable def plane {q : Nat} (e : Enum R q) (m : Nat) (lam : Nat → R)
    (hu : ∀ i j, i < m → j < m → i ≠ j → ∃ u, (lam j - lam i) * u = 1) : TD (m + 1) q where
  Line := R × R
  pt := planePt e lam
  line := planeLine e lam
  pt_lt L i _ := by cases i <;> exact e.enc_lt _
  pt_line i j c d hi hj hij hc hd := by
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j =>
        refine ⟨e.enc_dec c hc, ?_⟩
        show e.enc (e.dec c * lam j + (e.dec d - e.dec c * lam j)) = d
        rw [show e.dec c * lam j + (e.dec d - e.dec c * lam j) = e.dec d by grind]
        exact e.enc_dec d hd
    | succ i =>
      cases j with
      | zero =>
        refine ⟨?_, e.enc_dec d hd⟩
        show e.enc (e.dec d * lam i + (e.dec c - e.dec d * lam i)) = c
        rw [show e.dec d * lam i + (e.dec c - e.dec d * lam i) = e.dec c by grind]
        exact e.enc_dec c hc
      | succ j =>
        have hu' := mul_ringInv (hu i j (by omega) (by omega) (by omega))
        constructor
        · show e.enc ((e.dec d - e.dec c) * ringInv (lam j - lam i) * lam i +
            (e.dec c - (e.dec d - e.dec c) * ringInv (lam j - lam i) * lam i)) = c
          rw [show (e.dec d - e.dec c) * ringInv (lam j - lam i) * lam i +
            (e.dec c - (e.dec d - e.dec c) * ringInv (lam j - lam i) * lam i) = e.dec c by grind]
          exact e.enc_dec c hc
        · show e.enc ((e.dec d - e.dec c) * ringInv (lam j - lam i) * lam j +
            (e.dec c - (e.dec d - e.dec c) * ringInv (lam j - lam i) * lam i)) = d
          rw [show (e.dec d - e.dec c) * ringInv (lam j - lam i) * lam j +
            (e.dec c - (e.dec d - e.dec c) * ringInv (lam j - lam i) * lam i) = e.dec d by grind]
          exact e.enc_dec d hd
  line_pt L i j hi hj hij := by
    obtain ⟨a, b⟩ := L
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j =>
        show (e.dec (e.enc a), e.dec (e.enc (a * lam j + b)) - e.dec (e.enc a) * lam j) = (a, b)
        rw [e.dec_enc, e.dec_enc]
        congr 1
        grind
    | succ i =>
      cases j with
      | zero =>
        show (e.dec (e.enc a), e.dec (e.enc (a * lam i + b)) - e.dec (e.enc a) * lam i) = (a, b)
        rw [e.dec_enc, e.dec_enc]
        congr 1
        grind
      | succ j =>
        have hu' := mul_ringInv (hu i j (by omega) (by omega) (by omega))
        show ((e.dec (e.enc (a * lam j + b)) - e.dec (e.enc (a * lam i + b))) *
            ringInv (lam j - lam i), e.dec (e.enc (a * lam i + b)) -
            (e.dec (e.enc (a * lam j + b)) - e.dec (e.enc (a * lam i + b))) *
            ringInv (lam j - lam i) * lam i) = (a, b)
        rw [e.dec_enc, e.dec_enc]
        have ha : (a * lam j + b - (a * lam i + b)) * ringInv (lam j - lam i) = a := by grind
        rw [ha]
        congr 1
        grind

/-- **Labels coded by distinct numbers below `q` differ by units**, when every nonzero element
of `R` has an inverse, as in a field. -/
theorem units_of_field {q : Nat} (e : Enum R q) (m : Nat) (hm : m ≤ q)
    (hinv : ∀ x : R, x ≠ 0 → ∃ u, x * u = 1) :
    ∀ i j, i < m → j < m → i ≠ j → ∃ u, (e.dec j - e.dec i) * u = 1 := by
  intro i j hi hj hij
  refine hinv _ fun h => hij ?_
  have h' : e.dec j = e.dec i := by grind
  have := congrArg e.enc h'
  rw [e.enc_dec j (by omega), e.enc_dec i (by omega)] at this
  exact this.symm

end Plane

/-! ### The plane over `ℤ / q`

The labels are `0, 1, …, m - 1`. Their differences are units when `q` is coprime to every
positive number below `m`: by Bezout's identity. -/

/-- **Bezout's identity**, over the integers. -/
theorem bezout (a b : Nat) : ∃ x y : Int, x * a + y * b = (Nat.gcd a b : Int) := by
  refine Nat.gcd.induction a b (fun n => ⟨0, 1, by simp⟩) (fun m n _ ih => ?_)
  obtain ⟨x, y, h⟩ := ih
  refine ⟨y - x * ((n / m : Nat) : Int), x, ?_⟩
  rw [Nat.gcd_rec m n, ← h]
  have h2 : ((n % m : Nat) : Int) + (m : Int) * ((n / m : Nat) : Int) = (n : Int) := by
    have := Nat.mod_add_div n m
    exact_mod_cast this
  grind

/-- A residue coprime to the modulus has an inverse. -/
theorem exists_mul_mod_eq_one {d q : Nat} (hq : 0 < q) (h : Nat.gcd d q = 1) :
    ∃ t, d * t % q = 1 % q := by
  obtain ⟨x, y, hxy⟩ := bezout d q
  rw [h] at hxy
  have hq' : (q : Int) ≠ 0 := by omega
  refine ⟨(x % (q : Int)).toNat, ?_⟩
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.natCast_emod, Int.natCast_mul,
    Int.toNat_of_nonneg (Int.emod_nonneg _ hq'), Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
  have : (d : Int) * x = 1 + (-y) * q := by grind
  rw [this, Int.add_mul_emod_self_right]
  rfl

section Residues

variable {q : Nat} [NeZero q]

/-- The residue of `g` modulo `q`. -/
def emb (g : Nat) : Fin q := ⟨g % q, Nat.mod_lt _ (Nat.pos_of_neZero q)⟩

theorem emb_add (a b : Nat) : (emb (a + b) : Fin q) = emb a + emb b := by
  apply Fin.ext
  simp only [emb, Fin.val_add, Nat.add_mod_mod, Nat.mod_add_mod]

theorem emb_mul (a b : Nat) : (emb (a * b) : Fin q) = emb a * emb b := by
  apply Fin.ext
  simp only [emb, Fin.val_mul, Nat.mul_mod_mod, Nat.mod_mul_mod]

theorem emb_one : (emb 1 : Fin q) = 1 := Fin.ext rfl

theorem emb_zero : (emb 0 : Fin q) = 0 := Fin.ext rfl

theorem exists_emb_inv {d : Nat} (h : Nat.gcd d q = 1) : ∃ u : Fin q, emb d * u = 1 := by
  obtain ⟨t, ht⟩ := exists_mul_mod_eq_one (Nat.pos_of_neZero q) h
  exact ⟨emb t, by rw [← emb_mul, ← emb_one]; exact Fin.ext ht⟩

/-- **The difference of two labels below `m` is a unit** of `ℤ / q`, when `q` is coprime to
every positive number below `m`. -/
theorem exists_inv_sub {m : Nat} (hq : ∀ d, 0 < d → d < m → Nat.gcd d q = 1) {g₁ g₂ : Nat}
    (h₁ : g₁ < m) (h₂ : g₂ < m) (hne : g₁ ≠ g₂) :
    ∃ u : Fin q, (emb g₂ - emb g₁) * u = 1 := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨u, hu⟩ := exists_emb_inv (q := q) (hq (g₂ - g₁) (by omega) (by omega))
    have he : (emb g₂ : Fin q) = emb g₁ + emb (g₂ - g₁) := by
      rw [← emb_add, Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
    exact ⟨u, by rw [he]; grind⟩
  · obtain ⟨u, hu⟩ := exists_emb_inv (q := q) (hq (g₁ - g₂) (by omega) (by omega))
    have he : (emb g₁ : Fin q) = emb g₂ + emb (g₁ - g₂) := by
      rw [← emb_add, Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
    exact ⟨-u, by rw [he]; grind⟩

end Residues

/-- **The cyclic plane** `TD(m + 1, q)` over `ℤ / q`, with the labels `0, …, m - 1`. -/
noncomputable def cyclicPlane (q m : Nat) [NeZero q]
    (hq : ∀ d, 0 < d → d < m → Nat.gcd d q = 1) : TD (m + 1) q :=
  plane (Enum.fin q) m emb fun _ _ hi hj hij => exists_inv_sub hq hi hj hij

/-- **In the cyclic plane, the point in group `2` is the sum of those in groups `0` and `1`**:
the line `(a, b)` passes through `a`, `0 · a + b` and `1 · a + b`. -/
theorem cyclicPlane_pt_two {q m : Nat} [NeZero q] {hq} (L : Fin q × Fin q) :
    (cyclicPlane q m hq).pt L 2 =
      ((cyclicPlane q m hq).pt L 0 + (cyclicPlane q m hq).pt L 1) % q := by
  show (L.1 * emb 1 + L.2).val = (L.1.val + (L.1 * emb 0 + L.2).val) % q
  rw [emb_one, emb_zero, show L.1 * (1 : Fin q) = L.1 by grind,
    show L.1 * (0 : Fin q) + L.2 = L.2 by grind]
  exact Fin.val_add L.1 L.2

/-- The product of the primes up to `79`. -/
def P79 : Nat :=
  2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 37 * 41 * 43 * 47 * 53 * 59 * 61 * 67 *
    71 * 73 * 79

/-- Every `d` from `1` to `80` divides `P79 ^ 6`. -/
theorem dvd_P79_pow {d : Nat} (h0 : 0 < d) (h : d ≤ 80) : d ∣ P79 ^ 6 := by
  have := allBelow_spec (p := fun d => d == 0 || P79 ^ 6 % d == 0) (by decide +kernel) d
    (by omega : d < 81)
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  exact Nat.dvd_of_mod_eq_zero (this.resolve_left (by omega))

/-- **An order coprime to `P79` is coprime to every `d` from `1` to `80`.** -/
theorem gcd_eq_one_of_le {q d : Nat} (hq : Nat.gcd q P79 = 1) (h0 : 0 < d) (h : d ≤ 80) :
    Nat.gcd d q = 1 :=
  Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right (dvd_P79_pow h0 h) (Nat.Coprime.pow_right 6 hq))

theorem neZero_of_gcd {q : Nat} (hq : Nat.gcd q P79 = 1) : NeZero q :=
  ⟨by rintro rfl; rw [Nat.gcd_zero_left] at hq; exact absurd hq (by decide)⟩

/-- **`TD(82, q)` for `q` coprime to `P79`**: the cyclic plane with the labels `0, …, 80`. -/
noncomputable def cyclicTD {q : Nat} (hq : Nat.gcd q P79 = 1) : TD 82 q :=
  @cyclicPlane q 81 (neZero_of_gcd hq) fun _ h0 h => gcd_eq_one_of_le hq h0 (by omega)

/-! ### Quadratic, cubic and quartic extensions of `ℤ / p`

`Q2 p c₀ c₁` is `(ℤ / p)[ω] / (ω² - c₁ ω - c₀)`, `Q3 p r₀ r₁` is `(ℤ / p)[x] / (x³ - r₁ x - r₀)`
and `Q4 p r₀ r₁` is `(ℤ / p)[x] / (x⁴ - r₁ x - r₀)`, in coordinates. All are commutative rings
whatever the parameters, with the ring axioms checked coordinate by coordinate by `grind`. When
`p` is prime and the polynomial irreducible they are fields; the transversal designs below need
only that the nonzero elements have inverses, which a table checks. -/

section Fields

open Fin.NatCast Fin.IntCast

/-- `(ℤ / p)[ω] / (ω² - c₁ ω - c₀)`: the element `a + b ω`. -/
structure Q2 (p : Nat) (c₀ c₁ : Fin p) where
  a : Fin p
  b : Fin p
deriving DecidableEq

namespace Q2

variable {p : Nat} {c₀ c₁ : Fin p}

theorem ext' {x y : Q2 p c₀ c₁} (h1 : x.a = y.a) (h2 : x.b = y.b) : x = y := by
  cases x; cases y; simp_all

instance : Add (Q2 p c₀ c₁) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg (Q2 p c₀ c₁) := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub (Q2 p c₀ c₁) := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
/-- `(a + b ω) (c + d ω) = (a c + c₀ b d) + (a d + b c + c₁ b d) ω`. -/
instance : Mul (Q2 p c₀ c₁) :=
  ⟨fun x y => ⟨x.a * y.a + c₀ * (x.b * y.b), x.a * y.b + x.b * y.a + c₁ * (x.b * y.b)⟩⟩
@[simp] theorem add_a (x y : Q2 p c₀ c₁) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : Q2 p c₀ c₁) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_a (x : Q2 p c₀ c₁) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : Q2 p c₀ c₁) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : Q2 p c₀ c₁) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : Q2 p c₀ c₁) : (x - y).b = x.b - y.b := rfl
@[simp] theorem mul_a (x y : Q2 p c₀ c₁) : (x * y).a = x.a * y.a + c₀ * (x.b * y.b) := rfl
@[simp] theorem mul_b (x y : Q2 p c₀ c₁) :
    (x * y).b = x.a * y.b + x.b * y.a + c₁ * (x.b * y.b) := rfl

variable [NeZero p]

instance : NatCast (Q2 p c₀ c₁) := ⟨fun n => ⟨(n : Fin p), 0⟩⟩
instance : IntCast (Q2 p c₀ c₁) := ⟨fun n => ⟨(n : Fin p), 0⟩⟩
instance (n : Nat) : OfNat (Q2 p c₀ c₁) n := ⟨⟨(n : Fin p), 0⟩⟩
instance : SMul Nat (Q2 p c₀ c₁) := ⟨fun n x => (n : Q2 p c₀ c₁) * x⟩
instance : SMul Int (Q2 p c₀ c₁) := ⟨fun n x => (n : Q2 p c₀ c₁) * x⟩

/-- Powers, by repeated multiplication. -/
def npow (x : Q2 p c₀ c₁) : Nat → Q2 p c₀ c₁
  | 0 => 1
  | n + 1 => npow x n * x

instance : HPow (Q2 p c₀ c₁) Nat (Q2 p c₀ c₁) := ⟨npow⟩

@[simp] theorem natCast_a (n : Nat) : (n : Q2 p c₀ c₁).a = n := rfl
@[simp] theorem natCast_b (n : Nat) : (n : Q2 p c₀ c₁).b = 0 := rfl
@[simp] theorem intCast_a (n : Int) : (n : Q2 p c₀ c₁).a = n := rfl
@[simp] theorem intCast_b (n : Int) : (n : Q2 p c₀ c₁).b = 0 := rfl
@[simp] theorem ofNat_a (n : Nat) : (OfNat.ofNat n : Q2 p c₀ c₁).a = (n : Fin p) := rfl
@[simp] theorem ofNat_b (n : Nat) : (OfNat.ofNat n : Q2 p c₀ c₁).b = 0 := rfl
@[simp] theorem zero_a : (0 : Q2 p c₀ c₁).a = 0 := rfl
@[simp] theorem zero_b : (0 : Q2 p c₀ c₁).b = 0 := rfl
@[simp] theorem one_a : (1 : Q2 p c₀ c₁).a = 1 := rfl
@[simp] theorem one_b : (1 : Q2 p c₀ c₁).b = 0 := rfl
@[simp] theorem nsmul_def (n : Nat) (x : Q2 p c₀ c₁) : n • x = (n : Q2 p c₀ c₁) * x := rfl
@[simp] theorem zsmul_def (n : Int) (x : Q2 p c₀ c₁) : n • x = (n : Q2 p c₀ c₁) * x := rfl

@[simp] theorem fin_intCast_natCast (n : Nat) : (((n : Int) : Fin p)) = (n : Fin p) := rfl

instance : Lean.Grind.CommRing (Q2 p c₀ c₁) where
  add_zero x := by apply Q2.ext' <;> simp <;> grind
  add_comm x y := by apply Q2.ext' <;> simp <;> grind
  add_assoc x y z := by apply Q2.ext' <;> simp <;> grind
  mul_assoc x y z := by apply Q2.ext' <;> simp <;> grind
  mul_one x := by apply Q2.ext' <;> simp <;> grind
  one_mul x := by apply Q2.ext' <;> simp <;> grind
  left_distrib x y z := by apply Q2.ext' <;> simp <;> grind
  right_distrib x y z := by apply Q2.ext' <;> simp <;> grind
  zero_mul x := by apply Q2.ext' <;> simp <;> grind
  mul_zero x := by apply Q2.ext' <;> simp <;> grind
  pow_zero x := rfl
  pow_succ x n := rfl
  ofNat_succ n := by apply Q2.ext' <;> simp <;> grind
  ofNat_eq_natCast n := rfl
  nsmul_eq_natCast_mul n x := rfl
  neg_add_cancel x := by apply Q2.ext' <;> simp <;> grind
  sub_eq_add_neg x y := by apply Q2.ext' <;> simp <;> grind
  neg_zsmul i x := by apply Q2.ext' <;> simp <;> grind
  zsmul_natCast_eq_nsmul n x := by apply Q2.ext' <;> simp <;> grind
  intCast_neg i := by apply Q2.ext' <;> simp <;> grind
  mul_comm x y := by apply Q2.ext' <;> simp <;> grind

/-- `Q2 p c₀ c₁` has `p * p` elements: `a + b ω` is coded by `b p + a`. -/
def enum : Enum (Q2 p c₀ c₁) (p * p) where
  enc x := x.b.val * p + x.a.val
  dec n := ⟨emb n, emb (n / p)⟩
  enc_lt x := mul_add_lt x.b.isLt x.a.isLt
  dec_enc x := by
    apply Q2.ext'
    · exact Fin.ext (mul_add_mod x.a.isLt)
    · apply Fin.ext
      show (x.b.val * p + x.a.val) / p % p = x.b.val
      rw [mul_add_div x.a.isLt, Nat.mod_eq_of_lt x.b.isLt]
  enc_dec n hn := by
    have hp := Nat.pos_of_neZero p
    show n / p % p * p + n % p = n
    rw [Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hp).2 hn)]
    exact Nat.div_add_mod' n p

end Q2

/-- `(ℤ / p)[x] / (x³ - r₁ x - r₀)`: the element `a + b x + c x²`. -/
structure Q3 (p : Nat) (r₀ r₁ : Fin p) where
  a : Fin p
  b : Fin p
  c : Fin p
deriving DecidableEq

namespace Q3

variable {p : Nat} {r₀ r₁ : Fin p}

theorem ext' {x y : Q3 p r₀ r₁} (h1 : x.a = y.a) (h2 : x.b = y.b) (h3 : x.c = y.c) : x = y := by
  cases x; cases y; simp_all

instance : Add (Q3 p r₀ r₁) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c⟩⟩
instance : Neg (Q3 p r₀ r₁) := ⟨fun x => ⟨-x.a, -x.b, -x.c⟩⟩
instance : Sub (Q3 p r₀ r₁) := ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c⟩⟩
/-- The product, reduced by `x³ = r₀ + r₁ x` and `x⁴ = r₀ x + r₁ x²`. -/
instance : Mul (Q3 p r₀ r₁) :=
  ⟨fun x y => ⟨x.a * y.a + r₀ * (x.b * y.c + x.c * y.b),
    x.a * y.b + x.b * y.a + r₁ * (x.b * y.c + x.c * y.b) + r₀ * (x.c * y.c),
    x.a * y.c + x.b * y.b + x.c * y.a + r₁ * (x.c * y.c)⟩⟩
@[simp] theorem add_a (x y : Q3 p r₀ r₁) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : Q3 p r₀ r₁) : (x + y).b = x.b + y.b := rfl
@[simp] theorem add_c (x y : Q3 p r₀ r₁) : (x + y).c = x.c + y.c := rfl
@[simp] theorem neg_a (x : Q3 p r₀ r₁) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : Q3 p r₀ r₁) : (-x).b = -x.b := rfl
@[simp] theorem neg_c (x : Q3 p r₀ r₁) : (-x).c = -x.c := rfl
@[simp] theorem sub_a (x y : Q3 p r₀ r₁) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : Q3 p r₀ r₁) : (x - y).b = x.b - y.b := rfl
@[simp] theorem sub_c (x y : Q3 p r₀ r₁) : (x - y).c = x.c - y.c := rfl
@[simp] theorem mul_a (x y : Q3 p r₀ r₁) :
    (x * y).a = x.a * y.a + r₀ * (x.b * y.c + x.c * y.b) := rfl
@[simp] theorem mul_b (x y : Q3 p r₀ r₁) : (x * y).b =
    x.a * y.b + x.b * y.a + r₁ * (x.b * y.c + x.c * y.b) + r₀ * (x.c * y.c) := rfl
@[simp] theorem mul_c (x y : Q3 p r₀ r₁) :
    (x * y).c = x.a * y.c + x.b * y.b + x.c * y.a + r₁ * (x.c * y.c) := rfl

variable [NeZero p]

instance : NatCast (Q3 p r₀ r₁) := ⟨fun n => ⟨(n : Fin p), 0, 0⟩⟩
instance : IntCast (Q3 p r₀ r₁) := ⟨fun n => ⟨(n : Fin p), 0, 0⟩⟩
instance (n : Nat) : OfNat (Q3 p r₀ r₁) n := ⟨⟨(n : Fin p), 0, 0⟩⟩
instance : SMul Nat (Q3 p r₀ r₁) := ⟨fun n x => (n : Q3 p r₀ r₁) * x⟩
instance : SMul Int (Q3 p r₀ r₁) := ⟨fun n x => (n : Q3 p r₀ r₁) * x⟩

/-- Powers, by repeated multiplication. -/
def npow (x : Q3 p r₀ r₁) : Nat → Q3 p r₀ r₁
  | 0 => 1
  | n + 1 => npow x n * x

instance : HPow (Q3 p r₀ r₁) Nat (Q3 p r₀ r₁) := ⟨npow⟩

@[simp] theorem natCast_a (n : Nat) : (n : Q3 p r₀ r₁).a = n := rfl
@[simp] theorem natCast_b (n : Nat) : (n : Q3 p r₀ r₁).b = 0 := rfl
@[simp] theorem natCast_c (n : Nat) : (n : Q3 p r₀ r₁).c = 0 := rfl
@[simp] theorem intCast_a (n : Int) : (n : Q3 p r₀ r₁).a = n := rfl
@[simp] theorem intCast_b (n : Int) : (n : Q3 p r₀ r₁).b = 0 := rfl
@[simp] theorem intCast_c (n : Int) : (n : Q3 p r₀ r₁).c = 0 := rfl
@[simp] theorem ofNat_a (n : Nat) : (OfNat.ofNat n : Q3 p r₀ r₁).a = (n : Fin p) := rfl
@[simp] theorem ofNat_b (n : Nat) : (OfNat.ofNat n : Q3 p r₀ r₁).b = 0 := rfl
@[simp] theorem ofNat_c (n : Nat) : (OfNat.ofNat n : Q3 p r₀ r₁).c = 0 := rfl
@[simp] theorem zero_a : (0 : Q3 p r₀ r₁).a = 0 := rfl
@[simp] theorem zero_b : (0 : Q3 p r₀ r₁).b = 0 := rfl
@[simp] theorem zero_c : (0 : Q3 p r₀ r₁).c = 0 := rfl
@[simp] theorem one_a : (1 : Q3 p r₀ r₁).a = 1 := rfl
@[simp] theorem one_b : (1 : Q3 p r₀ r₁).b = 0 := rfl
@[simp] theorem one_c : (1 : Q3 p r₀ r₁).c = 0 := rfl
@[simp] theorem nsmul_def (n : Nat) (x : Q3 p r₀ r₁) : n • x = (n : Q3 p r₀ r₁) * x := rfl
@[simp] theorem zsmul_def (n : Int) (x : Q3 p r₀ r₁) : n • x = (n : Q3 p r₀ r₁) * x := rfl

instance : Lean.Grind.CommRing (Q3 p r₀ r₁) where
  add_zero x := by apply Q3.ext' <;> simp <;> grind
  add_comm x y := by apply Q3.ext' <;> simp <;> grind
  add_assoc x y z := by apply Q3.ext' <;> simp <;> grind
  mul_assoc x y z := by apply Q3.ext' <;> simp <;> grind
  mul_one x := by apply Q3.ext' <;> simp <;> grind
  one_mul x := by apply Q3.ext' <;> simp <;> grind
  left_distrib x y z := by apply Q3.ext' <;> simp <;> grind
  right_distrib x y z := by apply Q3.ext' <;> simp <;> grind
  zero_mul x := by apply Q3.ext' <;> simp <;> grind
  mul_zero x := by apply Q3.ext' <;> simp <;> grind
  pow_zero x := rfl
  pow_succ x n := rfl
  ofNat_succ n := by apply Q3.ext' <;> simp <;> grind
  ofNat_eq_natCast n := rfl
  nsmul_eq_natCast_mul n x := rfl
  neg_add_cancel x := by apply Q3.ext' <;> simp <;> grind
  sub_eq_add_neg x y := by apply Q3.ext' <;> simp <;> grind
  neg_zsmul i x := by apply Q3.ext' <;> simp <;> grind
  zsmul_natCast_eq_nsmul n x := by apply Q3.ext' <;> simp <;> grind
  intCast_neg i := by apply Q3.ext' <;> simp <;> grind
  mul_comm x y := by apply Q3.ext' <;> simp <;> grind

/-- `Q3 p r₀ r₁` has `p * p * p` elements: `a + b x + c x²` is coded by `(c p + b) p + a`. -/
def enum : Enum (Q3 p r₀ r₁) (p * p * p) where
  enc x := (x.c.val * p + x.b.val) * p + x.a.val
  dec n := ⟨emb n, emb (n / p), emb (n / p / p)⟩
  enc_lt x := mul_add_lt (mul_add_lt x.c.isLt x.b.isLt) x.a.isLt
  dec_enc x := by
    have h1 := mul_add_lt x.c.isLt x.b.isLt
    apply Q3.ext'
    · exact Fin.ext (mul_add_mod x.a.isLt)
    · apply Fin.ext
      show ((x.c.val * p + x.b.val) * p + x.a.val) / p % p = x.b.val
      rw [mul_add_div x.a.isLt, mul_add_mod x.b.isLt]
    · apply Fin.ext
      show ((x.c.val * p + x.b.val) * p + x.a.val) / p / p % p = x.c.val
      rw [mul_add_div x.a.isLt, mul_add_div x.b.isLt, Nat.mod_eq_of_lt x.c.isLt]
  enc_dec n hn := by
    have hp := Nat.pos_of_neZero p
    show (n / p / p % p * p + n / p % p) * p + n % p = n
    have h1 : n / p / p < p := by
      rw [Nat.div_div_eq_div_mul]
      exact (Nat.div_lt_iff_lt_mul (Nat.mul_pos hp hp)).2 (by rwa [Nat.mul_assoc] at hn)
    rw [Nat.mod_eq_of_lt h1, Nat.div_add_mod' (n / p) p]
    exact Nat.div_add_mod' n p

end Q3

/-- `(ℤ / p)[x] / (x⁴ - r₁ x - r₀)`: the element `a + b x + c x² + d x³`. -/
structure Q4 (p : Nat) (r₀ r₁ : Fin p) where
  a : Fin p
  b : Fin p
  c : Fin p
  d : Fin p
deriving DecidableEq

namespace Q4

variable {p : Nat} {r₀ r₁ : Fin p}

theorem ext' {x y : Q4 p r₀ r₁} (h1 : x.a = y.a) (h2 : x.b = y.b) (h3 : x.c = y.c)
    (h4 : x.d = y.d) : x = y := by
  cases x; cases y; simp_all

instance : Add (Q4 p r₀ r₁) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩⟩
instance : Neg (Q4 p r₀ r₁) := ⟨fun x => ⟨-x.a, -x.b, -x.c, -x.d⟩⟩
instance : Sub (Q4 p r₀ r₁) := ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩⟩
/-- The product, reduced by `x⁴ = r₀ + r₁ x`, `x⁵ = r₀ x + r₁ x²` and `x⁶ = r₀ x² + r₁ x³`. -/
instance : Mul (Q4 p r₀ r₁) :=
  ⟨fun x y => ⟨x.a * y.a + r₀ * (x.b * y.d + x.c * y.c + x.d * y.b),
    x.a * y.b + x.b * y.a + r₁ * (x.b * y.d + x.c * y.c + x.d * y.b) + r₀ * (x.c * y.d + x.d * y.c),
    x.a * y.c + x.b * y.b + x.c * y.a + r₁ * (x.c * y.d + x.d * y.c) + r₀ * (x.d * y.d),
    x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a + r₁ * (x.d * y.d)⟩⟩
@[simp] theorem add_a (x y : Q4 p r₀ r₁) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : Q4 p r₀ r₁) : (x + y).b = x.b + y.b := rfl
@[simp] theorem add_c (x y : Q4 p r₀ r₁) : (x + y).c = x.c + y.c := rfl
@[simp] theorem add_d (x y : Q4 p r₀ r₁) : (x + y).d = x.d + y.d := rfl
@[simp] theorem neg_a (x : Q4 p r₀ r₁) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : Q4 p r₀ r₁) : (-x).b = -x.b := rfl
@[simp] theorem neg_c (x : Q4 p r₀ r₁) : (-x).c = -x.c := rfl
@[simp] theorem neg_d (x : Q4 p r₀ r₁) : (-x).d = -x.d := rfl
@[simp] theorem sub_a (x y : Q4 p r₀ r₁) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : Q4 p r₀ r₁) : (x - y).b = x.b - y.b := rfl
@[simp] theorem sub_c (x y : Q4 p r₀ r₁) : (x - y).c = x.c - y.c := rfl
@[simp] theorem sub_d (x y : Q4 p r₀ r₁) : (x - y).d = x.d - y.d := rfl
@[simp] theorem mul_a (x y : Q4 p r₀ r₁) :
    (x * y).a = x.a * y.a + r₀ * (x.b * y.d + x.c * y.c + x.d * y.b) := rfl
@[simp] theorem mul_b (x y : Q4 p r₀ r₁) : (x * y).b = x.a * y.b + x.b * y.a +
    r₁ * (x.b * y.d + x.c * y.c + x.d * y.b) + r₀ * (x.c * y.d + x.d * y.c) := rfl
@[simp] theorem mul_c (x y : Q4 p r₀ r₁) : (x * y).c = x.a * y.c + x.b * y.b + x.c * y.a +
    r₁ * (x.c * y.d + x.d * y.c) + r₀ * (x.d * y.d) := rfl
@[simp] theorem mul_d (x y : Q4 p r₀ r₁) :
    (x * y).d = x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a + r₁ * (x.d * y.d) := rfl

variable [NeZero p]

instance : NatCast (Q4 p r₀ r₁) := ⟨fun n => ⟨(n : Fin p), 0, 0, 0⟩⟩
instance : IntCast (Q4 p r₀ r₁) := ⟨fun n => ⟨(n : Fin p), 0, 0, 0⟩⟩
instance (n : Nat) : OfNat (Q4 p r₀ r₁) n := ⟨⟨(n : Fin p), 0, 0, 0⟩⟩
instance : SMul Nat (Q4 p r₀ r₁) := ⟨fun n x => (n : Q4 p r₀ r₁) * x⟩
instance : SMul Int (Q4 p r₀ r₁) := ⟨fun n x => (n : Q4 p r₀ r₁) * x⟩

/-- Powers, by repeated multiplication. -/
def npow (x : Q4 p r₀ r₁) : Nat → Q4 p r₀ r₁
  | 0 => 1
  | n + 1 => npow x n * x

instance : HPow (Q4 p r₀ r₁) Nat (Q4 p r₀ r₁) := ⟨npow⟩

@[simp] theorem natCast_a (n : Nat) : (n : Q4 p r₀ r₁).a = n := rfl
@[simp] theorem natCast_b (n : Nat) : (n : Q4 p r₀ r₁).b = 0 := rfl
@[simp] theorem natCast_c (n : Nat) : (n : Q4 p r₀ r₁).c = 0 := rfl
@[simp] theorem natCast_d (n : Nat) : (n : Q4 p r₀ r₁).d = 0 := rfl
@[simp] theorem intCast_a (n : Int) : (n : Q4 p r₀ r₁).a = n := rfl
@[simp] theorem intCast_b (n : Int) : (n : Q4 p r₀ r₁).b = 0 := rfl
@[simp] theorem intCast_c (n : Int) : (n : Q4 p r₀ r₁).c = 0 := rfl
@[simp] theorem intCast_d (n : Int) : (n : Q4 p r₀ r₁).d = 0 := rfl
@[simp] theorem ofNat_a (n : Nat) : (OfNat.ofNat n : Q4 p r₀ r₁).a = (n : Fin p) := rfl
@[simp] theorem ofNat_b (n : Nat) : (OfNat.ofNat n : Q4 p r₀ r₁).b = 0 := rfl
@[simp] theorem ofNat_c (n : Nat) : (OfNat.ofNat n : Q4 p r₀ r₁).c = 0 := rfl
@[simp] theorem ofNat_d (n : Nat) : (OfNat.ofNat n : Q4 p r₀ r₁).d = 0 := rfl
@[simp] theorem zero_a : (0 : Q4 p r₀ r₁).a = 0 := rfl
@[simp] theorem zero_b : (0 : Q4 p r₀ r₁).b = 0 := rfl
@[simp] theorem zero_c : (0 : Q4 p r₀ r₁).c = 0 := rfl
@[simp] theorem zero_d : (0 : Q4 p r₀ r₁).d = 0 := rfl
@[simp] theorem one_a : (1 : Q4 p r₀ r₁).a = 1 := rfl
@[simp] theorem one_b : (1 : Q4 p r₀ r₁).b = 0 := rfl
@[simp] theorem one_c : (1 : Q4 p r₀ r₁).c = 0 := rfl
@[simp] theorem one_d : (1 : Q4 p r₀ r₁).d = 0 := rfl
@[simp] theorem nsmul_def (n : Nat) (x : Q4 p r₀ r₁) : n • x = (n : Q4 p r₀ r₁) * x := rfl
@[simp] theorem zsmul_def (n : Int) (x : Q4 p r₀ r₁) : n • x = (n : Q4 p r₀ r₁) * x := rfl

instance : Lean.Grind.CommRing (Q4 p r₀ r₁) where
  add_zero x := by apply Q4.ext' <;> simp <;> grind
  add_comm x y := by apply Q4.ext' <;> simp <;> grind
  add_assoc x y z := by apply Q4.ext' <;> simp <;> grind
  mul_assoc x y z := by apply Q4.ext' <;> simp <;> grind
  mul_one x := by apply Q4.ext' <;> simp <;> grind
  one_mul x := by apply Q4.ext' <;> simp <;> grind
  left_distrib x y z := by apply Q4.ext' <;> simp <;> grind
  right_distrib x y z := by apply Q4.ext' <;> simp <;> grind
  zero_mul x := by apply Q4.ext' <;> simp <;> grind
  mul_zero x := by apply Q4.ext' <;> simp <;> grind
  pow_zero x := rfl
  pow_succ x n := rfl
  ofNat_succ n := by apply Q4.ext' <;> simp <;> grind
  ofNat_eq_natCast n := rfl
  nsmul_eq_natCast_mul n x := rfl
  neg_add_cancel x := by apply Q4.ext' <;> simp <;> grind
  sub_eq_add_neg x y := by apply Q4.ext' <;> simp <;> grind
  neg_zsmul i x := by apply Q4.ext' <;> simp <;> grind
  zsmul_natCast_eq_nsmul n x := by apply Q4.ext' <;> simp <;> grind
  intCast_neg i := by apply Q4.ext' <;> simp <;> grind
  mul_comm x y := by apply Q4.ext' <;> simp <;> grind

/-- `Q4 p r₀ r₁` has `p * p * p * p` elements: `a + b x + c x² + d x³` is coded by
`((d p + c) p + b) p + a`. -/
def enum : Enum (Q4 p r₀ r₁) (p * p * p * p) where
  enc x := ((x.d.val * p + x.c.val) * p + x.b.val) * p + x.a.val
  dec n := ⟨emb n, emb (n / p), emb (n / p / p), emb (n / p / p / p)⟩
  enc_lt x := mul_add_lt (mul_add_lt (mul_add_lt x.d.isLt x.c.isLt) x.b.isLt) x.a.isLt
  dec_enc x := by
    apply Q4.ext'
    · exact Fin.ext (mul_add_mod x.a.isLt)
    · apply Fin.ext
      show (((x.d.val * p + x.c.val) * p + x.b.val) * p + x.a.val) / p % p = x.b.val
      rw [mul_add_div x.a.isLt, mul_add_mod x.b.isLt]
    · apply Fin.ext
      show (((x.d.val * p + x.c.val) * p + x.b.val) * p + x.a.val) / p / p % p = x.c.val
      rw [mul_add_div x.a.isLt, mul_add_div x.b.isLt, mul_add_mod x.c.isLt]
    · apply Fin.ext
      show (((x.d.val * p + x.c.val) * p + x.b.val) * p + x.a.val) / p / p / p % p = x.d.val
      rw [mul_add_div x.a.isLt, mul_add_div x.b.isLt, mul_add_div x.c.isLt,
        Nat.mod_eq_of_lt x.d.isLt]
  enc_dec n hn := by
    have hp := Nat.pos_of_neZero p
    show ((n / p / p / p % p * p + n / p / p % p) * p + n / p % p) * p + n % p = n
    have h1 : n / p / p / p < p := by
      apply Nat.div_lt_of_lt_mul
      apply Nat.div_lt_of_lt_mul
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.mul_assoc, ← Nat.mul_assoc]
      exact hn
    rw [Nat.mod_eq_of_lt h1, Nat.div_add_mod' (n / p / p) p, Nat.div_add_mod' (n / p) p]
    exact Nat.div_add_mod' n p

end Q4

/-- **Inverses from a check.** If `0` is coded by `0` and every nonzero code `c` below `q` has
a code `d` with `dec c * dec d = 1`, every nonzero element has an inverse. -/
theorem exists_inv_of_check {R : Type} [Lean.Grind.CommRing R] {q : Nat} (e : Enum R q)
    (h0 : e.dec 0 = 0) (h : ∀ c, c < q → c ≠ 0 → ∃ d, e.dec c * e.dec d = 1) :
    ∀ x : R, x ≠ 0 → ∃ u, x * u = 1 := by
  intro x hx
  have hc : e.enc x ≠ 0 := fun h' => hx (by rw [← e.dec_enc x, h', h0])
  obtain ⟨d, hd⟩ := h (e.enc x) (e.enc_lt x) hc
  rw [e.dec_enc] at hd
  exact ⟨_, hd⟩

/-- A table of inverses, checked entry by entry. -/
def invCheck {R : Type} [Lean.Grind.CommRing R] [DecidableEq R] {q : Nat} (e : Enum R q)
    (t : Nat → Nat) : Bool :=
  allBelow q fun c => c == 0 || decide (e.dec c * e.dec (t c) = 1)

theorem exists_inv_of_invCheck {R : Type} [Lean.Grind.CommRing R] [DecidableEq R] {q : Nat}
    (e : Enum R q) (t : Nat → Nat) (h : invCheck e t = true) :
    ∀ c, c < q → c ≠ 0 → ∃ d, e.dec c * e.dec d = 1 := by
  intro c hc hc0
  have := allBelow_spec h c hc
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨t c, this.resolve_left hc0⟩

end Fields

/-! ### The fields used, and their planes -/

/-- Look an entry up in a list of numbers. -/
def tableAt (t : List Nat) (c : Nat) : Nat := t.getD c 0

theorem gf4_inv : ∀ x : Q2 2 1 1, x ≠ 0 → ∃ u, x * u = 1 :=
  exists_inv_of_check Q2.enum (by decide)
    (exists_inv_of_invCheck Q2.enum (tableAt [0, 1, 3, 2]) (by decide +kernel))

theorem gf9_inv : ∀ x : Q2 3 1 1, x ≠ 0 → ∃ u, x * u = 1 :=
  exists_inv_of_check Q2.enum (by decide)
    (exists_inv_of_invCheck Q2.enum (tableAt [0, 1, 2, 5, 8, 3, 7, 6, 4]) (by decide +kernel))

/-- `TD(5, 4)`: the plane over `GF(4) = F₂[ω]/(ω² + ω + 1)`, with every element a label. -/
noncomputable def td4 : TD 5 4 :=
  plane (Q2.enum (p := 2) (c₀ := 1) (c₁ := 1)) 4 Q2.enum.dec
    (units_of_field Q2.enum 4 (Nat.le_refl _) gf4_inv)

/-- `TD(5, 9)`: the plane over `GF(9) = F₃[ω]/(ω² - ω - 1)`. -/
noncomputable def td9 : TD 5 9 :=
  plane (Q2.enum (p := 3) (c₀ := 1) (c₁ := 1)) 4 Q2.enum.dec
    (units_of_field Q2.enum 4 (by decide) gf9_inv)

theorem gf8_inv : ∀ x : Q3 2 1 1, x ≠ 0 → ∃ u, x * u = 1 :=
  exists_inv_of_check Q3.enum (by decide)
    (exists_inv_of_invCheck Q3.enum (tableAt [0, 1, 5, 6, 7, 2, 3, 4]) (by decide +kernel))

theorem gf27_inv : ∀ x : Q3 3 1 1, x ≠ 0 → ∃ u, x * u = 1 :=
  exists_inv_of_check Q3.enum (by decide)
    (exists_inv_of_invCheck Q3.enum (tableAt [0, 1, 2, 11, 15, 12, 19, 24, 21, 22, 26, 3, 5, 20,
      23, 4, 25, 18, 17, 6, 13, 8, 9, 14, 7, 16, 10]) (by decide +kernel))

/-- `TD(5, 8)`: the plane over `GF(8) = F₂[x]/(x³ - x - 1)`. -/
noncomputable def td8 : TD 5 8 :=
  plane (Q3.enum (p := 2) (r₀ := 1) (r₁ := 1)) 4 Q3.enum.dec
    (units_of_field Q3.enum 4 (by decide) gf8_inv)

/-- `TD(5, 27)`: the plane over `GF(27) = F₃[x]/(x³ - x - 1)`. -/
noncomputable def td27 : TD 5 27 :=
  plane (Q3.enum (p := 3) (r₀ := 1) (r₁ := 1)) 4 Q3.enum.dec
    (units_of_field Q3.enum 4 (by decide) gf27_inv)

/-! ### `TD(5, 12)` from a difference matrix

Three mutually orthogonal Latin squares of order `12` exist, and so does `TD(5, 12)`, which no
field gives. Here it comes from a difference matrix over `ℤ/2 × ℤ/6`, the element `(a, b)` coded
`6 a + b`: five rows `d12 0, …, d12 4` of twelve entries such that for any two rows `i ≠ j` the
differences `d12 i c - d12 j c` run over the whole group. The lines are the pairs `(c, h)`,
coded `12 c + h`, meeting group `i` in `d12 i c + h`; the line through two points is found by
searching the twelve columns. Everything is checked by evaluation (`td12_check`). -/

/-- Addition in `ℤ/2 × ℤ/6`, the element `(a, b)` coded `6 a + b`. -/
def g12add (x y : Nat) : Nat := (x / 6 + y / 6) % 2 * 6 + (x % 6 + y % 6) % 6

/-- Subtraction in `ℤ/2 × ℤ/6`. -/
def g12sub (x y : Nat) : Nat := (x / 6 + y / 6) % 2 * 6 + (x % 6 + 6 - y % 6) % 6

/-- The difference matrix, row by row, four bits an entry. -/
def d12Packed : Nat :=
  pack 4 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    0, 2, 1, 6, 8, 7, 10, 9, 11, 4, 3, 5, 0, 3, 8, 10, 1, 9, 2, 6, 5, 7, 11, 4,
    0, 4, 10, 9, 7, 1, 11, 5, 3, 2, 8, 6]

/-- The entry of row `i`, column `c` of the difference matrix. -/
def d12 (i c : Nat) : Nat := (d12Packed >>> (4 * (12 * i + c))) % 16

/-- The column `c` with `d12 i c - d12 j c = δ`, or `12` if there is none. -/
def d12col (i j δ : Nat) : Nat :=
  ((List.range 12).find? fun c => g12sub (d12 i c) (d12 j c) == δ).getD 12

/-- The point of the line `L = 12 c + h` in group `i`. -/
def pt12 (L i : Nat) : Nat := g12add (d12 i (L / 12)) (L % 12)

/-- The line through the point `x` of group `i` and the point `y` of group `j`. -/
def line12 (i x j y : Nat) : Nat :=
  12 * d12col i j (g12sub x y) + g12sub x (d12 i (d12col i j (g12sub x y)))

/-- The three conditions of a `TD(5, 12)` on `pt12` and `line12`, decided entry by entry. -/
def td12Check : Bool :=
  (allBelow 144 fun L => allBelow 5 fun i => decide (pt12 L i < 12)) &&
  (allBelow 5 fun i => allBelow 5 fun j => i == j || allBelow 12 fun x => allBelow 12 fun y =>
    decide (line12 i x j y < 144) && pt12 (line12 i x j y) i == x &&
      pt12 (line12 i x j y) j == y) &&
  (allBelow 144 fun L => allBelow 5 fun i => allBelow 5 fun j =>
    i == j || line12 i (pt12 L i) j (pt12 L j) == L)

theorem td12_check : td12Check = true := by decide +kernel

theorem td12_parts :
    (∀ L, L < 144 → ∀ i, i < 5 → pt12 L i < 12) ∧
    (∀ i, i < 5 → ∀ j, j < 5 → i ≠ j → ∀ x, x < 12 → ∀ y, y < 12 →
      line12 i x j y < 144 ∧ pt12 (line12 i x j y) i = x ∧ pt12 (line12 i x j y) j = y) ∧
    (∀ L, L < 144 → ∀ i, i < 5 → ∀ j, j < 5 → i ≠ j → line12 i (pt12 L i) j (pt12 L j) = L) := by
  have h := td12_check
  simp only [td12Check, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun L hL i hi => ?_, fun i hi j hj hij x hx y hy => ?_, fun L hL i hi j hj hij => ?_⟩
  · have := allBelow_spec (allBelow_spec h1 L hL) i hi
    simpa using this
  · have h2' := allBelow_spec (allBelow_spec h2 i hi) j hj
    simp only [Bool.or_eq_true, beq_iff_eq] at h2'
    have h2'' := allBelow_spec (allBelow_spec (h2'.resolve_left hij) x hx) y hy
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2''
    exact ⟨h2''.1.1, h2''.1.2, h2''.2⟩
  · have h3' := allBelow_spec (allBelow_spec (allBelow_spec h3 L hL) i hi) j hj
    simp only [Bool.or_eq_true, beq_iff_eq] at h3'
    exact h3'.resolve_left hij

/-- **`TD(5, 12)`**, from the difference matrix. -/
def td12 : TD 5 12 where
  Line := Fin 144
  pt L i := pt12 L.val i
  line i x j y := ⟨line12 i x j y % 144, Nat.mod_lt _ (by decide)⟩
  pt_lt L i hi := td12_parts.1 L.val L.isLt i hi
  pt_line i j x y hi hj hij hx hy := by
    obtain ⟨hl, h1, h2⟩ := td12_parts.2.1 i hi j hj hij x hx y hy
    dsimp only
    rw [Nat.mod_eq_of_lt hl]
    exact ⟨h1, h2⟩
  line_pt L i j hi hj hij := by
    apply Fin.ext
    show line12 i (pt12 L.val i) j (pt12 L.val j) % 144 = L.val
    rw [td12_parts.2.2 L.val L.isLt i hi j hj hij]
    exact Nat.mod_eq_of_lt L.isLt

/-- `TD(5, 1)`: one point in each group, one line. -/
noncomputable def td1 : TD 5 1 := cyclicPlane 1 4 fun d _ _ => Nat.gcd_one_right d

/-- **`TD(5, u c)` for `c` coprime to `6`**: MacNeish's product with the cyclic plane over
`ℤ / c`, whose labels `0, 1, 2, 3` differ by units. -/
theorem td5_mul {u c : Nat} (D : TD 5 u) (hc : Nat.gcd c 6 = 1) : Nonempty (TD 5 (u * c)) := by
  haveI : NeZero c := ⟨by rintro rfl; simp at hc⟩
  refine ⟨D.prod (cyclicPlane c 4 fun d h0 h => ?_)⟩
  have hd : d ∣ 6 := by
    rcases (show d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl <;> decide
  exact Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.symm hc)

/-- The factors that `tdOK5` allows beside a part coprime to `6`: the orders `1`, `4`, `8`, `9`,
`12`, `27` of `td1`, `td4`, `td8`, `td9`, `td12`, `td27` and the products `36 = 4 · 9`,
`48 = 4 · 12`, `72 = 8 · 9`, `96 = 8 · 12`, `108 = 4 · 27` and `216 = 8 · 27`. -/
def td5Units : List Nat := [1, 4, 8, 9, 12, 27, 36, 48, 72, 96, 108, 216]

/-- **The test for `TD(5, g)`**: `g = u c` with `u` in `td5Units` and `c` coprime to `6`; then
`TD(5, g)` is MacNeish's product of a design of order `u` with the cyclic plane over `ℤ / c`. -/
def tdOK5 (g : Nat) : Bool := td5Units.any fun u => g % u == 0 && Nat.gcd (g / u) 6 == 1

theorem td5_of_tdOK5 {g : Nat} (h : tdOK5 g = true) : Nonempty (TD 5 g) := by
  simp only [tdOK5, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨u, hu, hd, hc⟩ := h
  rw [(Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd)).symm]
  simp only [td5Units, List.mem_cons] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hu
  · exact td5_mul td1 hc
  · exact td5_mul td4 hc
  · exact td5_mul td8 hc
  · exact td5_mul td9 hc
  · exact td5_mul td12 hc
  · exact td5_mul td27 hc
  · exact td5_mul (td4.prod td9) hc
  · exact td5_mul (td4.prod td12) hc
  · exact td5_mul (td8.prod td9) hc
  · exact td5_mul (td8.prod td12) hc
  · exact td5_mul (td4.prod td27) hc
  · exact td5_mul (td8.prod td27) hc
  · cases hu

/-! ### Four more fields, and their planes

`GF(16) = F₂[x]/(x⁴ - x - 1)`, `GF(7³) = F₇[x]/(x³ - 3)`, `GF(23²) = F₂₃[ω]/(ω² - 5)` and
`GF(29²) = F₂₉[ω]/(ω² - 2)`. The inverse tables are not trusted: each entry is checked. -/

def inv16Table : List Nat :=
  [0, 1, 9, 14, 13, 11, 7, 6, 15, 2, 12, 5, 10, 4, 3, 8]

def inv343Table : List Nat :=
  [0, 1, 4, 5, 2, 3, 6, 245, 135, 120, 211, 144, 205, 228, 294, 72, 92, 127, 88, 114, 109, 196,
    332, 320, 178, 342, 167, 159, 147, 240, 232, 57, 221, 79, 67, 49, 290, 285, 311, 272, 307,
    327, 98, 171, 194, 255, 188, 279, 264, 35, 110, 209, 219, 59, 123, 71, 166, 31, 179, 53, 277,
    183, 268, 262, 274, 323, 319, 34, 197, 282, 275, 55, 15, 301, 168, 318, 334, 314, 177, 33,
    333, 324, 169, 100, 176, 315, 101, 271, 18, 286, 252, 326, 16, 266, 185, 201, 154, 174, 42,
    229, 83, 86, 129, 235, 134, 157, 162, 260, 284, 20, 50, 191, 258, 310, 19, 291, 261, 330,
    198, 263, 9, 182, 339, 54, 322, 335, 306, 17, 312, 102, 165, 337, 184, 163, 104, 8, 273, 329,
    283, 292, 309, 280, 199, 187, 11, 195, 175, 28, 160, 304, 186, 257, 281, 331, 96, 226, 207,
    105, 231, 27, 148, 241, 106, 133, 247, 130, 56, 26, 74, 82, 251, 43, 206, 244, 97, 146, 84,
    78, 24, 58, 298, 203, 121, 61, 132, 94, 150, 143, 46, 218, 299, 111, 243, 227, 44, 145, 21,
    68, 118, 142, 213, 95, 239, 181, 254, 12, 172, 156, 288, 51, 278, 10, 256, 200, 305, 267,
    338, 253, 189, 52, 341, 32, 321, 308, 325, 302, 155, 193, 13, 99, 317, 158, 30, 336, 269,
    103, 259, 293, 303, 202, 29, 161, 287, 192, 173, 7, 265, 164, 270, 313, 316, 170, 90, 217,
    204, 45]
  ++ [212, 151, 112, 236, 107, 116, 63, 119, 48, 246, 93, 215, 62, 234, 248, 87, 39, 136, 64, 70,
    296, 60, 210, 47, 141, 152, 69, 138, 108, 37, 89, 242, 208, 300, 36, 115, 139, 237, 14, 328,
    276, 340, 180, 190, 289, 73, 225, 238, 149, 214, 126, 40, 223, 140, 113, 38, 128, 249, 77,
    85, 250, 230, 75, 66, 23, 222, 124, 65, 81, 224, 91, 41, 295, 137, 117, 153, 22, 80, 76, 125,
    233, 131, 216, 122, 297, 220, 25]

def inv529Table : List Nat :=
  [0, 1, 12, 8, 6, 14, 4, 10, 3, 18, 7, 21, 2, 16, 5, 20, 13, 19, 9, 17, 15, 11, 22, 322, 155,
    44, 409, 61, 190, 478, 284, 174, 320, 356, 517, 518, 357, 301, 171, 291, 465, 201, 54, 396,
    25, 144, 161, 259, 89, 443, 298, 415, 469, 350, 42, 157, 95, 244, 239, 112, 142, 27, 363,
    474, 436, 277, 454, 72, 270, 460, 242, 97, 67, 283, 523, 191, 134, 435, 489, 364, 386, 373,
    349, 500, 416, 119, 200, 512, 292, 48, 110, 241, 345, 131, 394, 56, 309, 71, 486, 278, 149,
    446, 219, 237, 246, 218, 451, 150, 297, 503, 90, 312, 59, 411, 122, 276, 488, 475, 135, 85,
    353, 140, 114, 185, 223, 340, 164, 181, 327, 214, 206, 93, 159, 360, 76, 118, 468, 501, 230,
    198, 121, 439, 60, 526, 45, 208, 153, 324, 273, 100, 107, 256, 343, 146, 229, 24, 509, 55,
    458, 132, 193, 46, 294, 211, 126, 372, 472, 365, 331, 317, 250, 38, 262, 267, 31, 233, 304,
    336, 348, 471, 387, 127, 226, 281, 437, 123, 330, 385, 473, 490, 28, 75, 419, 160, 300, 516,
    519, 321, 139, 432, 86, 41, 499, 470, 374, 337, 130, 506, 145, 400, 257, 163, 427, 224, 129,
    347, 375, 305, 105, 102, 316, 384, 366, 124, 213, 424, 182, 272, 405, 154, 138, 355, 520,
    175, 249, 383, 332, 103, 307, 58, 441, 91, 70, 456, 57, 314, 104, 335, 376, 234, 170, 515,
    358, 414, 502, 444]
  ++ [151, 210, 390, 47, 464, 513, 172, 286, 265, 264, 289, 173, 522, 479, 68, 369, 227, 148, 453,
    487, 115, 65, 99, 404, 325, 183, 484, 73, 30, 379, 263, 288, 287, 266, 380, 39, 88, 505, 162,
    342, 401, 108, 50, 391, 194, 37, 382, 318, 176, 217, 448, 238, 495, 96, 482, 461, 111, 494,
    245, 449, 220, 169, 303, 377, 32, 197, 23, 398, 147, 280, 370, 128, 339, 428, 186, 168, 236,
    450, 447, 247, 177, 205, 423, 328, 125, 389, 295, 152, 407, 92, 422, 215, 178, 82, 53, 511,
    466, 120, 413, 231, 33, 36, 252, 392, 133, 477, 524, 62, 79, 167, 222, 429, 483, 271, 326,
    425, 165, 81, 204, 216, 248, 319, 521, 285, 290, 514, 302, 235, 221, 187, 80, 180, 426, 341,
    258, 299, 359, 420, 94, 497, 43, 528, 323, 406, 209, 296, 445, 452, 279, 228, 399, 344, 507,
    26, 492, 113, 431, 354, 253, 51, 84, 434, 476, 192, 393, 459, 346, 338, 225, 371, 388, 212,
    329, 367, 438, 412, 199, 467, 417, 77, 64, 184, 430, 141, 493, 240, 462, 49, 255, 402, 101,
    334, 306, 315, 333, 106, 403, 274, 66, 481, 243, 496, 158, 421, 69, 311, 442, 504, 260, 40,
    352, 433, 136, 52, 203, 179, 166, 188, 63, 117, 418, 361, 29, 269, 485, 455, 310, 368, 282,
    480, 98, 275, 116, 78, 189, 525, 410, 440, 313, 308, 457, 395, 510, 202, 83, 137, 254, 109,
    463, 293, 207, 408, 527, 156, 498, 351]
  ++ [87, 261, 381, 251, 195, 34, 35, 196, 232, 378, 268, 74, 362, 491, 143, 508, 397]

def inv841Table : List Nat :=
  [0, 1, 15, 10, 22, 6, 5, 25, 11, 13, 3, 8, 17, 9, 27, 2, 20, 12, 21, 26, 16, 18, 4, 24, 23, 7,
    19, 14, 28, 435, 57, 407, 133, 79, 149, 674, 234, 205, 336, 631, 574, 315, 748, 398, 385,
    731, 294, 557, 616, 331, 230, 259, 689, 170, 66, 128, 434, 30, 638, 613, 449, 786, 218, 147,
    81, 699, 54, 743, 495, 586, 772, 550, 117, 144, 523, 765, 603, 520, 736, 33, 722, 64, 172,
    217, 809, 450, 634, 145, 220, 671, 309, 491, 357, 706, 395, 647, 344, 549, 800, 587, 413,
    627, 620, 428, 602, 795, 524, 323, 658, 388, 715, 368, 466, 300, 692, 215, 319, 72, 727, 276,
    645, 397, 828, 316, 544, 695, 494, 803, 55, 437, 364, 361, 462, 32, 792, 521, 668, 529, 293,
    825, 386, 660, 275, 752, 73, 87, 651, 63, 790, 34, 197, 563, 167, 303, 367, 760, 389, 590,
    246, 710, 711, 247, 599, 394, 777, 358, 306, 152, 568, 180, 53, 805, 82, 654, 493, 745, 545,
    214, 756, 301, 169, 818, 260, 262, 193, 582, 353, 329, 618, 629, 338, 372, 607, 184, 289,
    233, 835, 150, 308, 781, 221, 528, 734, 783, 635, 37, 535, 488, 425, 274, 729, 387, 762, 324,
    177, 115, 697, 83, 62, 724, 88, 200, 343, 775, 396, 750, 277, 416, 469, 538, 50, 612, 580,
    195, 36, 666, 784, 451, 573, 831, 337, 681, 619, 769, 414, 279, 158, 161, 272, 427, 768, 628,
    682, 330, 822, 558]
  ++ [448, 811, 639, 51, 182, 609, 183, 678, 373, 286, 519, 794, 766, 429, 393, 708, 248, 444, 209,
    142, 119, 226, 455, 245, 713, 390, 412, 771, 801, 496, 265, 352, 685, 194, 464, 370, 340,
    138, 46, 314, 830, 632, 452, 403, 113, 179, 702, 153, 504, 511, 166, 719, 198, 90, 380, 447,
    615, 823, 295, 41, 123, 327, 355, 116, 799, 773, 345, 107, 213, 694, 746, 317, 516, 187, 253,
    49, 641, 470, 487, 664, 38, 240, 190, 499, 292, 733, 669, 222, 96, 322, 764, 796, 667, 735,
    793, 604, 287, 186, 542, 318, 378, 92, 165, 565, 505, 131, 409, 432, 130, 510, 566, 154, 111,
    405, 291, 531, 191, 264, 585, 802, 744, 551, 356, 779, 310, 424, 663, 536, 471, 44, 140, 211,
    109, 156, 281, 459, 440, 270, 163, 94, 224, 121, 43, 486, 537, 642, 417, 299, 758, 369, 812,
    31, 738, 362, 439, 479, 282, 100, 244, 592, 227, 402, 572, 633, 785, 810, 614, 559, 381, 208,
    597, 249, 103, 269, 478, 460, 363, 741, 56, 29, 814, 129, 507, 410, 392, 601, 767, 621, 273,
    662, 489, 311, 256, 60, 85, 237, 298, 468, 643, 278, 626, 770, 588, 391, 431, 508, 132, 839,
    290, 501, 112, 571, 453, 228, 333, 384, 827, 749, 646, 776, 707, 600, 430, 411, 589, 714,
    761, 659, 730, 826, 399, 334, 207, 446, 560, 91, 514, 174, 126, 68, 285, 606, 679, 339, 579,
    465, 759, 716, 304, 360, 740, 438, 461, 739, 365, 305]
  ++ [705, 778, 492, 552, 328, 684, 583, 266, 77, 135, 725, 74, 106, 548, 774, 648, 201, 137, 578,
    371, 680, 630, 832, 206, 383, 400, 229, 821, 617, 683, 354, 553, 124, 176, 657, 763, 525, 97,
    71, 377, 515, 543, 747, 829, 575, 47, 255, 423, 490, 780, 672, 151, 704, 359, 366, 717, 168,
    691, 757, 467, 418, 238, 40, 556, 824, 732, 530, 500, 232, 676, 185, 518, 605, 374, 69, 99,
    458, 480, 157, 625, 415, 644, 751, 728, 661, 426, 622, 162, 477, 441, 104, 76, 351, 584, 497,
    192, 687, 261, 688, 819, 231, 59, 422, 312, 48, 540, 188, 242, 102, 443, 598, 709, 712, 591,
    456, 101, 251, 189, 533, 39, 297, 419, 86, 204, 834, 675, 58, 258, 820, 332, 401, 454, 593,
    120, 474, 95, 527, 670, 782, 146, 808, 787, 173, 755, 693, 546, 108, 483, 141, 596, 445, 382,
    335, 833, 235, 348, 136, 342, 649, 89, 562, 720, 35, 637, 581, 686, 263, 498, 532, 241, 252,
    541, 517, 288, 677, 608, 610, 52, 701, 569, 114, 656, 325, 125, 754, 216, 788, 65, 817, 690,
    302, 718, 564, 512, 93, 476, 271, 623, 159, 160, 624, 280, 481, 110, 503, 567, 703, 307, 673,
    836, 80, 807, 219, 522, 797, 118, 595, 210, 484, 45, 577, 341, 202, 349, 78, 838, 408, 509,
    506, 433, 815, 67, 376, 175, 326, 554, 42, 473, 225, 594, 143, 798, 696, 655, 178, 570, 404,
    502, 155, 482, 212, 547, 346, 75, 268, 442]
  ++ [250, 243, 457, 283, 70, 321, 526, 223, 475, 164, 513, 379, 561, 199, 650, 203, 236, 420, 61,
    653, 698, 806, 148, 837, 134, 350, 267, 105, 347, 726, 753, 320, 98, 284, 375, 127, 816, 171,
    789, 723, 652, 84, 421, 257, 406, 840, 436, 742, 804, 700, 181, 611, 640, 539, 254, 313, 576,
    139, 485, 472, 122, 555, 296, 239, 534, 665, 636, 196, 721, 791, 737, 463, 813]

def inv16Packed : Nat := pack 5 inv16Table
def inv343Packed : Nat := pack 9 inv343Table
def inv529Packed : Nat := pack 10 inv529Table
def inv841Packed : Nat := pack 10 inv841Table

theorem gf16_inv : ∀ x : Q4 2 1 1, x ≠ 0 → ∃ u, x * u = 1 :=
  exists_inv_of_check Q4.enum (by decide)
    (exists_inv_of_invCheck Q4.enum (fun c => (inv16Packed >>> (5 * c)) % 32) (by decide +kernel))

theorem gf343_inv : ∀ x : Q3 7 3 0, x ≠ 0 → ∃ u, x * u = 1 :=
  exists_inv_of_check Q3.enum (by decide)
    (exists_inv_of_invCheck Q3.enum (fun c => (inv343Packed >>> (9 * c)) % 512)
      (by decide +kernel))

theorem gf529_inv : ∀ x : Q2 23 5 0, x ≠ 0 → ∃ u, x * u = 1 :=
  exists_inv_of_check Q2.enum (by decide)
    (exists_inv_of_invCheck Q2.enum (fun c => (inv529Packed >>> (10 * c)) % 1024)
      (by decide +kernel))

theorem gf841_inv : ∀ x : Q2 29 2 0, x ≠ 0 → ∃ u, x * u = 1 :=
  exists_inv_of_check Q2.enum (by decide)
    (exists_inv_of_invCheck Q2.enum (fun c => (inv841Packed >>> (10 * c)) % 1024)
      (by decide +kernel))

/-- `TD(6, 16)`: the plane over `GF(16)`, with five labels. -/
noncomputable def td16 : TD 6 16 :=
  plane (Q4.enum (p := 2) (r₀ := 1) (r₁ := 1)) 5 Q4.enum.dec
    (units_of_field Q4.enum 5 (by decide) gf16_inv)

/-- `TD(m + 1, 343)` for `m ≤ 343`: the plane over `GF(7³)`. -/
noncomputable def td343 (m : Nat) (hm : m ≤ 343) : TD (m + 1) 343 :=
  plane (Q3.enum (p := 7) (r₀ := 3) (r₁ := 0)) m Q3.enum.dec
    (units_of_field Q3.enum m hm gf343_inv)

/-- `TD(m + 1, 529)` for `m ≤ 529`: the plane over `GF(23²)`. -/
noncomputable def td529 (m : Nat) (hm : m ≤ 529) : TD (m + 1) 529 :=
  plane (Q2.enum (p := 23) (c₀ := 5) (c₁ := 0)) m Q2.enum.dec
    (units_of_field Q2.enum m hm gf529_inv)

/-- `TD(m + 1, 841)` for `m ≤ 841`: the plane over `GF(29²)`. -/
noncomputable def td841 (m : Nat) (hm : m ≤ 841) : TD (m + 1) 841 :=
  plane (Q2.enum (p := 29) (c₀ := 2) (c₁ := 0)) m Q2.enum.dec
    (units_of_field Q2.enum m hm gf841_inv)

/-! ### Tests for transversal designs

`TD(k, q)` is MacNeish's product of planes over fields, whose orders are peeled off `q`
(`Spectrum677.peel`), and the cyclic plane over `ℤ / c` for the rest `c`, when `c` is coprime to
every number from `1` to `k - 2`. -/

/-- Divide out each `f` of the list that divides what is left. -/
def peel (fs : List Nat) (q : Nat) : Nat := fs.foldl (fun q f => if q % f == 0 then q / f else q) q

/-- **Peeling keeps transversal designs**: if `TD(k, f)` exists for each `f` of the list and
`TD(k, peel fs q)` exists, so does `TD(k, q)`. -/
theorem td_of_peel {k : Nat} : ∀ (fs : List Nat) (q : Nat), (∀ f ∈ fs, Nonempty (TD k f)) →
    Nonempty (TD k (peel fs q)) → Nonempty (TD k q)
  | [], _, _, h => h
  | f :: fs, q, hf, h => by
    have h' := td_of_peel fs _ (fun g hg => hf g (List.mem_cons_of_mem _ hg)) h
    by_cases hd : q % f = 0
    · simp only [hd, BEq.rfl, ite_true] at h'
      obtain ⟨D⟩ := h'
      obtain ⟨E⟩ := hf f (List.mem_cons_self ..)
      rw [← Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd)]
      exact ⟨D.prod E⟩
    · have hd' : (q % f == 0) = false := by simpa using hd
      simp only [hd', Bool.false_eq_true, ite_false] at h'
      exact h'

/-- **A number coprime to `P` is coprime to every divisor of a power of `P`.** -/
theorem gcd_eq_one_of_dvd_pow {q P d e : Nat} (hq : Nat.gcd q P = 1) (hd : d ∣ P ^ e) :
    Nat.gcd d q = 1 :=
  Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right hd (Nat.Coprime.pow_right e hq))

/-- **The cyclic plane `TD(m + 1, q)`** when `q` is coprime to `P` and every number from `1` to
`m - 1` divides a power of `P`. -/
theorem td_cyclic {m q P e : Nat} (hP : ∀ d, 0 < d → d < m → d ∣ P ^ e) (h1 : 1 < P)
    (hq : Nat.gcd q P = 1) : Nonempty (TD (m + 1) q) := by
  haveI : NeZero q := ⟨by rintro rfl; rw [Nat.gcd_zero_left] at hq; omega⟩
  exact ⟨cyclicPlane q m fun d h0 h => gcd_eq_one_of_dvd_pow hq (hP d h0 h)⟩

/-- The product of the primes up to `163`. -/
def P163 : Nat :=
  P79 * 83 * 89 * 97 * 101 * 103 * 107 * 109 * 113 * 127 * 131 * 137 * 139 * 149 * 151 * 157 *
    163

/-- Every `d` from `1` to `165` divides `P163 ^ 7`. -/
theorem dvd_P163_pow {d : Nat} (h0 : 0 < d) (h : d < 166) : d ∣ P163 ^ 7 := by
  have := allBelow_spec (p := fun d => d == 0 || P163 ^ 7 % d == 0) (by decide +kernel) d h
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  exact Nat.dvd_of_mod_eq_zero (this.resolve_left (by omega))

/-- The field orders peeled off by `tdOK` and `tdOK167`. -/
def fieldOrders : List Nat := [343, 529, 841]

/-- **The test for `TD(82, q)`**: the parts `343`, `529`, `841` peeled off, the rest coprime to
`P79`. -/
def tdOK (q : Nat) : Bool := Nat.gcd (peel fieldOrders q) P79 == 1

/-- **The test for `TD(167, q)`**: the same, the rest coprime to `P163`. -/
def tdOK167 (q : Nat) : Bool := Nat.gcd (peel fieldOrders q) P163 == 1

/-- **The test for `TD(6, n)`**: the part `16` peeled off, the rest coprime to `6`. -/
def tdOK6 (n : Nat) : Bool := Nat.gcd (peel [16] n) 6 == 1

theorem td_of_tdOK {q : Nat} (h : tdOK q = true) : Nonempty (TD 82 q) := by
  rw [tdOK, beq_iff_eq] at h
  refine td_of_peel fieldOrders q (fun f hf => ?_)
    (td_cyclic (m := 81) (e := 6) (fun d h0 hd => dvd_P79_pow h0 (by omega)) (by decide) h)
  simp only [fieldOrders, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨td343 81 (by decide)⟩
  · exact ⟨td529 81 (by decide)⟩
  · exact ⟨td841 81 (by decide)⟩

theorem td_of_tdOK167 {q : Nat} (h : tdOK167 q = true) : Nonempty (TD 167 q) := by
  rw [tdOK167, beq_iff_eq] at h
  refine td_of_peel fieldOrders q (fun f hf => ?_)
    (td_cyclic (m := 166) (e := 7) (fun d h0 hd => dvd_P163_pow h0 hd) (by decide) h)
  simp only [fieldOrders, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨td343 166 (by decide)⟩
  · exact ⟨td529 166 (by decide)⟩
  · exact ⟨td841 166 (by decide)⟩

theorem td_of_tdOK6 {n : Nat} (h : tdOK6 n = true) : Nonempty (TD 6 n) := by
  rw [tdOK6, beq_iff_eq] at h
  refine td_of_peel [16] n (fun f hf => ?_)
    (td_cyclic (m := 5) (e := 2) (fun d h0 hd => ?_) (by decide) h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    exact ⟨td16⟩
  · rcases (show d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 by omega) with rfl | rfl | rfl | rfl <;> decide
/-! ## Fourth powers

Over any commutative ring in which `Φ₁₀(ζ) = ζ⁴ - ζ³ + ζ² - ζ + 1` vanishes,
`x ◇ y = (1 - ζ) x + ζ y` satisfies Equation 677 and the idempotent law. In
`(ℤ / j)[ζ] / (Φ₁₀(ζ))`, which has `j⁴` elements, the class of `ζ` is such a root. -/

section Phi

variable {j : Nat} [NeZero j]

/-- The ring `(ℤ / j)[ζ] / (Φ₁₀(ζ))`, `Φ₁₀(ζ) = ζ⁴ - ζ³ + ζ² - ζ + 1`, in the basis
`1, ζ, ζ², ζ³`. -/
abbrev Phi4 (j : Nat) : Type := Fin j × Fin j × Fin j × Fin j

/-- Multiplication by `ζ`, using `ζ⁴ = ζ³ - ζ² + ζ - 1`:
`ζ (c₀ + c₁ ζ + c₂ ζ² + c₃ ζ³) = -c₃ + (c₀ + c₃) ζ + (c₁ - c₃) ζ² + (c₂ + c₃) ζ³`. -/
def zetaMul (z : Phi4 j) : Phi4 j :=
  (-z.2.2.2, z.1 + z.2.2.2, z.2.1 - z.2.2.2, z.2.2.1 + z.2.2.2)

/-- The **cyclotomic model** `x ◇ y = x + ζ (y - x) = (1 - ζ) x + ζ y`. -/
def phiOp (x y : Phi4 j) : Phi4 j :=
  let t := zetaMul (y.1 - x.1, y.2.1 - x.2.1, y.2.2.1 - x.2.2.1, y.2.2.2 - x.2.2.2)
  (x.1 + t.1, x.2.1 + t.2.1, x.2.2.1 + t.2.2.1, x.2.2.2 + t.2.2.2)

/-- **The cyclotomic model satisfies Equation 677.** With `a = 1 - ζ` and `b = ζ` the law is
`a b (1 + b²) = 1` and `a + a² b² + b³ = 0`, and both are `Φ₁₀(ζ) = 0`; coordinate by
coordinate it is a ring identity, which `grind` checks. -/
theorem phiOp_eq677 (x y : Phi4 j) : phiOp y (phiOp x (phiOp (phiOp y x) y)) = x := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [phiOp, zetaMul, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- The cyclotomic model is idempotent: `x ◇ x = x + ζ 0`. -/
theorem phiOp_idem (x : Phi4 j) : phiOp x x = x := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  simp only [phiOp, zetaMul, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

variable (j) in
/-- `Phi4 j` has `j * (j * (j * j))` elements, in base `j`. -/
def Enum.phi4 : Enum (Phi4 j) (j * (j * (j * j))) :=
  (Enum.fin j).prod ((Enum.fin j).prod ((Enum.fin j).prod (Enum.fin j)))

variable (j) in
/-- The cyclotomic model on `{0, …, j⁴ - 1}`. -/
def phiOpN (x y : Nat) : Nat :=
  (Enum.phi4 j).enc (phiOp ((Enum.phi4 j).dec x) ((Enum.phi4 j).dec y))

theorem isModel_phiOpN : IsModel (j * (j * (j * j))) (phiOpN j) :=
  (Enum.phi4 j).isModel phiOp fun x y => phiOp_eq677 x y

theorem phiOpN_idem : ∀ x, x < j * (j * (j * j)) → phiOpN j x x = x :=
  (Enum.phi4 j).idem phiOp phiOp_idem

end Phi

theorem pow_four_eq (j : Nat) : j ^ 4 = j * (j * (j * j)) := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]

/-- **Every fourth power `j⁴` is a pointed order**: `(ℤ / j)[ζ] / (Φ₁₀(ζ))` with
`x ◇ y = (1 - ζ) x + ζ y`, which moreover satisfies the idempotent law (`phiOpN_idem`). -/
theorem hasPtModel_pow_four (j : Nat) : HasPtModel (j ^ 4) := by
  rw [pow_four_eq]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact hasPtModel_zero
  haveI : NeZero j := ⟨Nat.pos_iff_ne_zero.mp hj⟩
  have h0 : 0 < j * (j * (j * j)) := Nat.mul_pos hj (Nat.mul_pos hj (Nat.mul_pos hj hj))
  exact ⟨phiOpN j, isModel_phiOpN, Or.inr ⟨0, h0, phiOpN_idem 0 h0⟩⟩

/-! ## Small models checked by evaluation

The nine-element model is given by a formula and checked pair by pair; the others below are
checked pair by pair from their tables, or, when translation invariant, at the `p` pairs
`(0, d)` that suffice. -/

/-- The nine-element seed: the field `F₃(ω)`, `ω² = ω + 1`, with `x ◇ y = x + ω y`; the element
`a + b ω` is `a + 3 b`, and `(a + b ω) ◇ (c + d ω) = (a + d) + (b + c + d) ω`. -/
def opGF9 (x y : Nat) : Nat := (x % 3 + y / 3) % 3 + 3 * ((x / 3 + y % 3 + y / 3) % 3)

theorem isModel_GF9 : IsModel 9 opGF9 := isModel_of_checkModel (by decide +kernel)

theorem hasPtModel_nine : HasPtModel 9 := ⟨_, isModel_GF9, Or.inr ⟨0, by decide, by decide⟩⟩

/-! ### Models with every element idempotent -/

/-- Idempotence on `{0, …, n - 1}`, decided point by point. -/
def checkIdem (n : Nat) (op : Nat → Nat → Nat) : Bool := allBelow n fun x => op x x == x

theorem isIdemModel_of_check {n : Nat} {op : Nat → Nat → Nat} (h₁ : checkModel n op = true)
    (h₂ : checkIdem n op = true) : IsIdemModel n op :=
  ⟨isModel_of_checkModel h₁, fun x hx => by simpa using allBelow_spec h₂ x hx⟩

theorem IsIdemModel.hasPtModel {n : Nat} {op : Nat → Nat → Nat} (h : IsIdemModel n op) :
    HasPtModel n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨op, h.toIsModel, Or.inl rfl⟩
  · exact ⟨op, h.toIsModel, Or.inr ⟨0, hn, h.idem 0 hn⟩⟩

/-- **The product of idempotent models is an idempotent model.** -/
theorem IsIdemModel.prod {m n : Nat} {op₁ op₂ : Nat → Nat → Nat} (h₁ : IsIdemModel m op₁)
    (h₂ : IsIdemModel n op₂) : IsIdemModel (m * n) (prodOp n op₁ op₂) :=
  ⟨h₁.toIsModel.prod h₂.toIsModel, prodOp_idem h₁.idem h₂.idem⟩

/-- The displacement table `f` of T79, the census magma `48fa6b96a24eaf1f…`:
`x ◇ y = x + f(y - x)` on `ℤ / 79`. -/
def t79Table : List Nat :=
  [0, 6, 10, 15, 54, 28, 2, 55, 48, 3, 60, 30, 72, 65, 5, 11, 1, 23, 29, 59, 21, 47, 53, 34,
   41, 46, 35, 4, 61, 36, 71, 63, 37, 40, 12, 17, 22, 27, 70, 13, 66, 9, 52, 57, 62, 67, 39,
   42, 16, 8, 43, 18, 75, 44, 33, 38, 45, 26, 32, 58, 20, 50, 56, 78, 68, 74, 14, 7, 49, 19,
   76, 31, 24, 77, 51, 25, 64, 69, 73]

/-- `t79Table`, seven bits an entry. -/
def t79Packed : Nat := pack 7 t79Table

/-- T79, on `{0, …, 78}`. -/
def opT79 (x y : Nat) : Nat := (x + (t79Packed >>> (7 * ((y + 79 - x) % 79))) % 128) % 79

/-- **T79**, translation invariant, with every element idempotent. -/
theorem isIdemModel_T79 : IsIdemModel 79 opT79 :=
  isIdemModel_of_check (by decide +kernel) (by decide +kernel)

/-- `A(5; 2, 4, 0)`: `x ◇ y = 2 x + 4 y` on `ℤ / 5`. -/
def opF5 (x y : Nat) : Nat := (2 * x + 4 * y) % 5

theorem isIdemModel_F5 : IsIdemModel 5 opF5 :=
  isIdemModel_of_check (by decide +kernel) (by decide +kernel)

/-- The cyclotomic models have every element idempotent. -/
theorem isIdemModel_phi (j : Nat) [NeZero j] : IsIdemModel (j * (j * (j * j))) (phiOpN j) :=
  ⟨isModel_phiOpN, phiOpN_idem⟩

/-- `A(5; 2, 4, 0) × F₂[ζ]/(Φ₁₀)`, with every element idempotent. -/
def op80 : Nat → Nat → Nat := prodOp 16 opF5 (phiOpN 2)

theorem isIdemModel_80 : IsIdemModel 80 op80 :=
  isIdemModel_F5.prod (isIdemModel_phi 2)

/-- `F₃[ζ]/(Φ₁₀)`, with every element idempotent. -/
theorem isIdemModel_81 : IsIdemModel 81 (phiOpN 3) := isIdemModel_phi 3

/-! ### Translation-invariant models

On `ℤ / p`, `x ◇ y = x + f (y - x)` commutes with the translations, so the law holds at every
pair `(x, y)` as soon as it holds at the pairs `(0, d)`: `p` checks instead of `p²`
(`Spectrum677.tiOp_eq677`). -/

section TI

variable {p : Nat} [NeZero p]

/-- The translation-invariant operation `x ◇ y = x + f (y - x)`, with `f` read off `F`. -/
def tiOp (F : Nat → Nat) (x y : Fin p) : Fin p := x + emb (F (y - x).val)

theorem tiOp_sub (F : Nat → Nat) (u v c : Fin p) : tiOp F u v = tiOp F (u - c) (v - c) + c := by
  unfold tiOp
  rw [show v - c - (u - c) = v - u by grind]
  grind

/-- **Equation 677 for a translation-invariant operation**, from its instances at `(0, d)`
read as `d ◇ (0 ◇ ((d ◇ 0) ◇ d)) = 0`. -/
theorem tiOp_eq677 (F : Nat → Nat)
    (h : ∀ d : Fin p, tiOp F d (tiOp F 0 (tiOp F (tiOp F d 0) d)) = 0) (x y : Fin p) :
    tiOp F y (tiOp F x (tiOp F (tiOp F y x) y)) = x := by
  have e1 : tiOp F y x = tiOp F (y - x) 0 + x := by
    have := tiOp_sub F y x x
    rwa [show x - x = (0 : Fin p) by grind] at this
  have e2 : tiOp F (tiOp F (y - x) 0 + x) y = tiOp F (tiOp F (y - x) 0) (y - x) + x := by
    have := tiOp_sub F (tiOp F (y - x) 0 + x) y x
    rwa [show tiOp F (y - x) 0 + x - x = tiOp F (y - x) 0 by grind] at this
  have e3 : tiOp F x (tiOp F (tiOp F (y - x) 0) (y - x) + x) =
      tiOp F 0 (tiOp F (tiOp F (y - x) 0) (y - x)) + x := by
    have := tiOp_sub F x (tiOp F (tiOp F (y - x) 0) (y - x) + x) x
    rwa [show x - x = (0 : Fin p) by grind,
      show tiOp F (tiOp F (y - x) 0) (y - x) + x - x = tiOp F (tiOp F (y - x) 0) (y - x) by
        grind] at this
  have e4 : tiOp F y (tiOp F 0 (tiOp F (tiOp F (y - x) 0) (y - x)) + x) =
      tiOp F (y - x) (tiOp F 0 (tiOp F (tiOp F (y - x) 0) (y - x))) + x := by
    have := tiOp_sub F y (tiOp F 0 (tiOp F (tiOp F (y - x) 0) (y - x)) + x) x
    rwa [show tiOp F 0 (tiOp F (tiOp F (y - x) 0) (y - x)) + x - x =
      tiOp F 0 (tiOp F (tiOp F (y - x) 0) (y - x)) by grind] at this
  rw [e1, e2, e3, e4, h (y - x)]
  grind

/-- The translation-invariant operation on `{0, …, p - 1}`. -/
def tiNat (p : Nat) [NeZero p] (F : Nat → Nat) (x y : Nat) : Nat :=
  (Enum.fin p).enc (tiOp F ((Enum.fin p).dec x) ((Enum.fin p).dec y))

/-- The `p` instances of the law that `tiOp_eq677` needs, decided one by one. -/
def tiCheck (p : Nat) [NeZero p] (F : Nat → Nat) : Bool :=
  allBelow p fun d =>
    (tiOp F (emb d) (tiOp F (0 : Fin p) (tiOp F (tiOp F (emb d) 0) (emb d)))).val == 0

/-- **A translation-invariant model** from its check; it has every element idempotent when
`f 0 = 0`. -/
theorem isIdemModel_ti {F : Nat → Nat} (h : tiCheck p F = true) (h0 : F 0 % p = 0) :
    IsIdemModel p (tiNat p F) := by
  refine ⟨(Enum.fin p).isModel (tiOp F) (tiOp_eq677 F fun d => ?_), fun x hx => ?_⟩
  · have := allBelow_spec h d.val d.isLt
    simp only [beq_iff_eq] at this
    have hd : (emb d.val : Fin p) = d := Fin.ext (Nat.mod_eq_of_lt d.isLt)
    rw [hd] at this
    exact Fin.ext this
  · show (tiOp F ((Enum.fin p).dec x) ((Enum.fin p).dec x)).val = x
    unfold tiOp
    rw [Fin.sub_self]
    have : (emb (F (0 : Fin p).val) : Fin p) = 0 := Fin.ext h0
    rw [this, Fin.add_zero]
    exact Nat.mod_eq_of_lt hx

end TI

def t29Table : List Nat :=
  [0, 27, 6, 9, 21, 19, 17, 15, 24, 11, 1, 4, 7, 3, 13, 16, 26, 22, 25, 28, 18, 5, 14, 12, 10, 8,
    20, 23, 2]

def tp83Table : List Nat :=
  [0, 47, 61, 58, 22, 28, 17, 80, 78, 8, 55, 19, 66, 23, 12, 1, 5, 52, 51, 40, 29, 74, 7, 2, 68,
    13, 60, 24, 71, 35, 82, 46, 63, 57, 41, 30, 32, 79, 43, 69, 54, 18, 36, 25, 76, 3, 75, 64,
    15, 62, 31, 73, 9, 81, 70, 59, 48, 37, 26, 34, 4, 45, 65, 56, 20, 67, 21, 10, 42, 6, 53, 49,
    38, 27, 16, 39, 77, 50, 14, 44, 33, 72, 11]

def tp167Table : List Nat :=
  [0, 80, 160, 73, 153, 54, 146, 59, 139, 52, 108, 45, 125, 107, 118, 162, 111, 50, 104, 17, 49,
    10, 90, 48, 83, 163, 47, 156, 69, 149, 157, 142, 55, 135, 100, 44, 41, 99, 34, 154, 98, 42,
    20, 97, 13, 152, 96, 86, 166, 79, 159, 150, 94, 38, 145, 93, 138, 51, 131, 36, 147, 37, 117,
    30, 110, 23, 103, 89, 33, 144, 88, 32, 82, 87, 31, 155, 68, 148, 141, 85, 29, 134, 84, 28,
    40, 120, 27, 113, 26, 106, 137, 81, 25, 92, 5, 24, 165, 78, 158, 71, 151, 22, 133, 77, 21,
    132, 76, 43, 123, 75, 19, 130, 109, 18, 102, 15, 95, 128, 72, 16, 127, 161, 74, 126, 67, 14,
    60, 140, 53, 124, 46, 12, 39, 119, 11, 122, 66, 105, 121, 65, 9, 91, 64, 8, 164, 63, 7, 70,
    62, 6, 143, 61, 136, 116, 129, 4, 115, 35, 3, 114, 58, 2, 101, 57, 1, 112, 56]

def tp227Table : List Nat :=
  [0, 128, 65, 157, 58, 49, 195, 215, 33, 17, 145, 46, 174, 82, 1, 147, 5, 212, 131, 162, 196,
    191, 34, 220, 99, 22, 150, 51, 179, 80, 208, 213, 132, 138, 39, 116, 68, 181, 100, 19, 126,
    84, 3, 56, 184, 214, 133, 114, 15, 143, 36, 182, 101, 201, 166, 85, 4, 32, 69, 61, 134, 53,
    218, 119, 20, 148, 102, 21, 167, 206, 107, 8, 70, 37, 165, 66, 194, 95, 223, 124, 103, 153,
    54, 87, 83, 211, 71, 13, 136, 42, 170, 120, 199, 185, 104, 23, 169, 158, 7, 187, 88, 216,
    117, 18, 146, 121, 40, 186, 204, 105, 6, 89, 35, 163, 73, 219, 93, 57, 203, 122, 151, 52,
    180, 25, 171, 90, 9, 155, 74, 168, 139, 197, 98, 226, 127, 188, 156, 26, 172, 86, 10, 115,
    75, 221, 45, 59, 205, 202, 43, 189, 108, 27, 173, 92, 11, 91, 76, 222, 141, 149, 50, 178, 44,
    190, 109, 28, 137, 38, 12, 67, 77, 96, 224, 125, 207, 154, 55, 183, 110, 29, 175, 14, 142,
    159, 78, 72, 200, 62, 2, 130, 31, 192, 60, 30, 176, 217, 118, 160, 79, 225, 144, 63, 209,
    106, 47, 135, 112, 164, 177, 193, 94, 161, 123, 24, 152, 64, 210, 129, 48, 111, 113, 140, 41,
    97, 16, 198, 81]

def rows69 (x : Nat) : Nat :=
  if x < 34 then
    if x < 17 then
      if x < 8 then
        if x < 4 then
          if x < 2 then
            if x < 1 then
              12780414085582445911894421660551139032774559560422000739252354825368175085156785923893919229060996799625443094993538814006500318199174605840630400
            else
              8028861439105377892644566426479584985147786465003192125116182486481423008410000684025011001944915785752907236261737235326774396736281934561313159
          else
            if x < 3 then
              11005662115864524604528049454200674531678372549402864944806903371682027668166071425915104454563872093041854249648739297907743559955826603613816961
            else
              11402096446629577968042082747742284670090648223154759277955327191466618368087263883208901486325384908154409839628385478193060895571840982596699013
        else
          if x < 6 then
            if x < 5 then
              4702965855236810729005730143869615235504749814350213278916399929132491407900642653186352575437682256326141440587253652163187038521462188733912963
            else
              1604035544632610637596735571582637986105008986147425968169975266437083328722850155529082760545698600796559479991314787170940847879177280168892420
          else
            if x < 7 then
              10234525704026572071124377885745003962262048175495397899625475607859130421495546540760721294638007289382177029807478990785410366802490532452631313
            else
              3753250721136225595464213705669319534150174718209258475697571609645625429724011667245531332609561300356713523196904927530589866728273127990722690
      else
        if x < 12 then
          if x < 10 then
            if x < 9 then
              6520992204137558748867681994476932983586902978098131391124823543150350092368148579929261161971824728373724231409520795795089973134966153556925326
            else
              8642973977086661739802987742589705359489923438891167148184318725058676372618473399077054795575179491889801860604854563585762028825357457913006859
          else
            if x < 11 then
              7684645110908818007776102984746010286283928919690821333061909537599838143103937023474810664475873614005767459083803949229690564060137713977559689
            else
              4145215080395311885766004908425860977919038797499089745455435190173355109316930365811746484479686497830033073449302790361063380244108310681247370
        else
          if x < 14 then
            if x < 13 then
              3588768381947432924545253164495456129531110106584667118070286633389109310566868819776427666095505605295062962527366314459281009198108972816075689
            else
              8446705638712979861200073819722947958875556113274874441195941073922846953780302035312650232298750866620565851330086214392275100949250203376439692
          else
            if x < 15 then
              867409213835568409219506754605553330947863819061323151049744506500582836134684976802039340780175133532255727945695928293038991590377752942333226
            else
              if x < 16 then
                7092899528155214837832984227564958742820129150063837609997917095775462644728553705963578821087766253407013704548434803063673648725285038508018707
              else
                9254618818129717384621913505900006581912639965623821021201738073268485031832322718057975868710379916041508287459286827770001050524293170291134223
    else
      if x < 25 then
        if x < 21 then
          if x < 19 then
            if x < 18 then
              2939217017712632562876756826605027097742429411830203204430936146397949624444475879252079625995730848697938974108223865214218508100039658486978322
            else
              5675046708741235964867779377241679196280972035380592992528850221580761923192153094885231570571624642970862237143143675092089946748801640407794182
          else
            if x < 20 then
              6919439720461974702734508518333377945163711696825047226625245067912328388860302429043936019501531965878674731281286957309603725767382451910298128
            else
              392399357050599325955304046021891323343655934473648675066405744623568385568644041474149726897559812620306780450596140822693536599512412985565590
        else
          if x < 23 then
            if x < 22 then
              7810565217333776609939331151987055518657663955216598687328019466086524501439811543378062819956771173590474455599022287753536145412578587666144276
            else
              1447053056495555080634878548021584288257619948720641835355956049926656035830950060306670406931726776253215038064875846061523200754102812342506389
          else
            if x < 24 then
              7246672174664889545297979149290057232029241524515752445637158991961665815418248450517455184304574735421916682222352436533348067934713816915221145
            else
              10010153558263559591830816871426072938323805480105728113088306258278300346715661269287947735838732854809897941704328296724336866274164937538556951
      else
        if x < 29 then
          if x < 27 then
            if x < 26 then
              658983243896898182745837563179402514880445980576846917135644238427956140861701560096658136198418987912116799661332209840478867344406747485657880
            else
              1196748624392747504577624804298223586392394528210768848404082454235286598290658554443961425714893640063471454498217970660598401872464493943100956
          else
            if x < 28 then
              10391713329343771155471258612280234121129139977996458972418511408946826607409075411566010365514397684262570438971167620363777387792150343736530586
            else
              9067021095682411151125501333596932051637870005182347580347832729300256609334860171647937079324256971828614188064799250061145366994222049901155099
        else
          if x < 31 then
            if x < 30 then
              11760030740798104110303567944248722608436529961931777496067739258687926982840693638730107087147522310510933393320381359261337801343168851020274219
            else
              1053849260045043924474401855989010364720255233182193073652065935976172340951488601710254437252989209587059367844641729318928517013030832815624093
          else
            if x < 32 then
              10766621077601241862124060560768897776301523259107706403510877727418927880814679929961740588780384362711962936574738157434947954295283187378969900
            else
              if x < 33 then
                5077681688852801222431536750531300123224779305044847800095641510236010541387880361199657826204502096050767950882105360069160264065308211045336610
              else
                5872087120970216655532869633181777811339661802759833685365953694716775052269356877312221234979652727002553713152468387625055243508882308881286432
  else
    if x < 51 then
      if x < 42 then
        if x < 38 then
          if x < 36 then
            if x < 35 then
              9568323328877727466280784671920507011059735506584488883765788605205375766236035797715970146182928670074526135001508714707464244755740284072285345
            else
              4313904669065083323749395423058433405293688026714529368704104826902639063984056205546857031502088439228658821970795120262507810369630322486057381
          else
            if x < 37 then
              11581819753639648708782581333686662290135729078195107596445416189367263617079247773004570646819921148039729810755530924865038409084232161399644067
            else
              9788178004831759389541723566462240925168641416258310693919794081484164193991035447786138064006320421582379530758834564704336773850206925975573924
        else
          if x < 40 then
            if x < 39 then
              3911693567817657299867635216721152617541750706994954783784166459473236155087919523596304857377416595815115517120415711019790472783454503827277224
            else
              5487750908889672475807195678059915873934569044592557099053980549119864726300056150483146852776022125487860182962071043959565017081185127359109414
          else
            if x < 41 then
              11187096515656923936256071348288818823523778766001605116906194762771954012547561572577695920156534024868014685951853639565559119577331654808002087
            else
              6683211079595140405758416976734339430755769445328304915838117059188126549709435107334851927256661814591867467098069697419779041580452356330821773
      else
        if x < 46 then
          if x < 44 then
            if x < 43 then
              4548688214620318034929547805667099950553541850070856782560785120151542545084323036056463473118601108783273118991960141395997832362434374297915016
            else
              6120664473921864539587867192787585291344113992350100819401383692613951803811943471065623876065465661459136743962659733109069816394923434440171550
          else
            if x < 45 then
              10546797760876152030381235646429190827001670064767773653438475741271672273926402487881695943577314152445573344420427085051507902325742805283971245
            else
              4880928848569765550994186236664197489168479918942377660319756658937909172965695365016474140751561938832885182285004908295734201384590924590400543
        else
          if x < 48 then
            if x < 47 then
              1984942479490364241644489302181839046479916117231169488106519192465982038002008582845611054392927290231890453409266013422454654236721403578827055
            else
              5332569976065512831913474372822368110068056583976842888788661846867433002903150373664947787253685441516194305828137514691658007505521605194287408
          else
            if x < 49 then
              1771514167129618328578371333642085455398852719413314666616858329365561674841028466395556848839090680134858378582725381707607151044638738839879726
            else
              if x < 50 then
                233552729526926020728585545241266659511392880198809921328135632677881205802801626389678552619638601330748565701090816240001905494909772819030579
              else
                8236202069938607548312737204074249765629387066600676511904063524580826150577211817611632137607769036423791032216720969564594669223315810776827057
    else
      if x < 60 then
        if x < 55 then
          if x < 53 then
            if x < 52 then
              2798611642890220383726802333446858304459930940762218748867519048356563512672766435287583205963984246412987536757122796234781298920037371677221170
            else
              6266425035117734562548482544675040230065926774848640136275164517624776739701937488781986676829358671900481766683823999352880037214287533359980342
          else
            if x < 54 then
              3176659520393703841247799511570274246373247434777666423917666259523537381704999702871330475850589326490996396623738873533833546106478176814469172
            else
              9404903299095559159942493610006018030255207777810806751439611870819274331839574585629897756501076263273054807951257053941488563046817050181800501
        else
          if x < 57 then
            if x < 56 then
              2573221500705751334558181563572063130246694371876470004435422498747649703785270787707356418581717610365530824357677012669576428814554648644079036
            else
              7477222514797267599831717066023104935402357483435511504810275686980335641002456482057238724209324746386617327269412580215544692224396168068927671
          else
            if x < 58 then
              2190457125082538474746276005495247348102582835249687309209971029037674396565252456069743739993353345173829719185160688526953752634537456261337787
            else
              if x < 59 then
                8794043283313870805465059644452422928227855935464623865321547522567895776648120667567381499249903923626110763017270274337224173008001997719881785
              else
                3347512923840796695721599895706596957129407039767370494008757179892894886345619067452004766163311193154781543232684788093102959406842094985284026
      else
        if x < 64 then
          if x < 62 then
            if x < 61 then
              2393603523970891551639031823131013143182626032347711159690189857878071867839832626516089894925258253057675619473859275126556267470139841743079352
            else
              13172145506637114791144898782119827762633508006128063453786296982839112564604953129151460458615022601650091713450230574305057287791531874597916221
          else
            if x < 63 then
              101371744440253784432019789500508942167707722212734326515395866253379539812708468965888930063585138530623181056094597034873273776308794960467262
            else
              12970998224698893179441726239766348859177732482566350098943327426606860051387777611570140675091971407292358100958898683047022440507841406692756671
        else
          if x < 66 then
            if x < 65 then
              12396269239541656255534350555293481878193599373259321372169103161069097184937492533175651347047042336578515860060052602170587117238823431976164544
            else
              12193598179799141883438793190223403437307968469441534512513516001948346707661076506870697982227180781950090047111918625587860459550483298136966977
          else
            if x < 67 then
              12589931543204778910797998195768948395907502532143697045231879688412566632244842537469014422775588095418020305973446806510954108595387025133405890
            else
              if x < 68 then
                13361943397449347033119226983154369167374745550939173475396086799611156387964669962185959011825767711510263111362134018868350994171875229501218243
              else
                11902446312539406253305273943906771302466719203438614268397745925075025659532063165022592046676645214261482067059336578640197593589625307395625284

def rows76 (x : Nat) : Nat :=
  if x < 38 then
    if x < 19 then
      if x < 9 then
        if x < 4 then
          if x < 2 then
            if x < 1 then
              891086009660654554268932772289942107646293520458582247540028115563481363907003979998089619389931591171664853661869937812071122572575789992343684798222319026560
            else
              5750410747175632848732326563019930719315773424675897630369529019345643522581674060121047449059531374902716982905806329700088213615101481657591698661245271982212
          else
            if x < 3 then
              3104921784862924511661129149827524924177872431284934192272353849891696711302898346617675673650469659956837339247295612480989060524294774574414149818235100364801
            else
              2778589349809683530726214196721592209701036248480322679992325757460419908646660571990728433868706997617672269879122995854088031586105948408733410728990002381314
        else
          if x < 6 then
            if x < 5 then
              6973331120002291700699807801872908251776264090717318067670778376255862643079923252152679675442543864312774698605317958679038726426095114007041446925720050745603
            else
              1034975571207127566816219493064560605842562237997007456368988110130570481313196057328816965236836946208064509146599824634189187477138598364556804634832295289902
          else
            if x < 7 then
              2573744741209782377323522112827454161753422386664822849575957913895132527925921779686520023766942919415974886544141238028763686325388775038493506394746476501063
            else
              if x < 8 then
                6482161048587031712222018604089358096747527787986277724505497293938187870748026888440388315649448021789160814847914451306658282999411877530324424828258983516461
              else
                2330937148236532354082813260446476662680774168232367737222192338519893663059585067236157724947248505344107896582551740431853717811069841442227688919030722955824
      else
        if x < 14 then
          if x < 11 then
            if x < 10 then
              3987980532357628446628154418933162130533338321708477595274414684854861181469811722412691949967406802264858286286499890379471053518483869301155925696392108262211
            else
              5430217275923018281790489802052637827885010189110094625668713825918220789000314240181642855446117445783898253405910510525848700760410455663351181530297139219079
          else
            if x < 12 then
              5178130062500649137215240942592484901339121890669014243335566812881351158519219652646648382087529171126549655418696141957777760281525853598348656616291170388870
            else
              if x < 13 then
                3865746745182637207008017735425998209810328620449941123694210660777001521255225178714618277175463186521867119549462722460270377889888654318992629279319908803755
              else
                234549930078459986504800475455609373029826803701158953742963930189117856782267587388722788367779165857448505705267902437316672656176621337606688463558844536383
        else
          if x < 16 then
            if x < 15 then
              5529736241374417657596606237669190535317367157796010063152302497190326128436024811543401855089415177815757111834395984459367533010259478087331240927079733121971
            else
              2451633625165546456422630998994619755942261646060423124714040276227557741344017526818259473232027999741419565695850666973732467290741158640676864132331873411483
          else
            if x < 17 then
              3221570639030643117382186797448303151085054777137431644943907634867088282798675992697467428392237779091229886141926479755046978373435112430866821995342762119233
            else
              if x < 18 then
                1350088275433851738302996014316970961049491724673708313481816705102123942697792839500328159812490438474467287037907920171245852390986076683983866085728334355385
              else
                4222856637696825301555381738252921128788543624653646824280728673178918320425966695531957190467292311400543724383426305728037013235089146287688519838607291571896
    else
      if x < 28 then
        if x < 23 then
          if x < 21 then
            if x < 20 then
              2905896527118267167854015907503655265062105761790311100632030294098457508757537046606807484450947860223177527031101142588966974738664976588022050210149699146944
            else
              1577455540993580491174572028480886440545331606687929450862556131824818928137656636774305494050701886795508522465897569837002691598520338713057732690163870599053
          else
            if x < 22 then
              5277676222862772302683003782818224900197896953526770550587059284980382171743630514384632386850614430593611342579473367755200559348298948960733581011995924537352
            else
              4289640983069975568481538419451327809085077020437746468308107181030435706822805827857455186299769582900513076534107164634235207534174001260717824655353348394185
        else
          if x < 25 then
            if x < 24 then
              5078288614923405564115734039012955754689166941293439508665761229609573108315664767047305369253100299970552859870091158375733222038417228513703512420844007625002
            else
              4878486176431008294935476569633239581245725953759726352360272525056905088828751672883533387038725111696759926786874326263328319055283825196392049374224695613081
          else
            if x < 26 then
              4630353639547760946509051121882026308777022632828304177020073288140531060675240375979207339786721408771384674284401598854394330131055988168509277285638903943998
            else
              if x < 27 then
                3666775593575962789142068423128720500918460957746213300685477973299492501578316710658357757608987297598445798178996191687134614912615422094531037609778830331831
              else
                4115482344182324063948857065340356790515068430077817898512465965266492444751325566414510612333101944031785624586900141413267474753099633740688864110196888050208
      else
        if x < 33 then
          if x < 30 then
            if x < 29 then
              4519826020760878748165403088147510449963411403099612114792120737892230443982828645513442864603905521973328994442334996289920831949028184241058771031312304399137
            else
              2664415412222320873339879200755130487284234646271309079620391790477292980325989616876609660682351462893364717661216559370068637219020577428666416471500234311994
          else
            if x < 31 then
              552007944537636864856960702454999792130037826359894440364035351162321523610729285834449942589632411692523381091684652857826707578272839006735071449312893256617
            else
              if x < 32 then
                5945258679955702613763842185591564048806137519661540744052651018932429308066165935737289099669444255161262890673808323494608613718575570986830512664299304034577
              else
                6052244657636575836375417993536719084533716472365331504877554002765438043353257917172612389659177938743514420910067409599193546547323083319983832487682640792389
        else
          if x < 35 then
            if x < 34 then
              6594577497549793375316144922107566429351158510935185332785422362593007565564830425103254459763298100868984684767105088654996791147805650140680510740050538321168
            else
              5620810821616984280014846727542409608955323714606045118827099518428493034598054635767986579654591746962462086705678088340427572134279410436519109919450807263768
          else
            if x < 36 then
              4951369401212026781486002859909957413676873223831515682464273849378853150634437701220363041827001199160566878051274958507906222647829769759630723110785454791496
            else
              if x < 37 then
                3318366681579602933850793759377075001544434407589063877496746974226477418281044573987079939195236171059873742903489174664992644587668864060650333914591965335066
              else
                137426008745409210699965663894733433968440457836834033722890034687244979967423172068324541342593321794376377856537525265487561753055384581757799903138343626161
  else
    if x < 57 then
      if x < 47 then
        if x < 42 then
          if x < 40 then
            if x < 39 then
              1118454431128052242601895032079530560883862205337643228914633868238569518358537943957319931519229751423871361229856561374513670664676922283162632988676366048450
            else
              4773792624807273962189771513684569113983141193775600567941266741098027407531771552120514362271587429311058190790337710909258605621930702328418184355408400881546
          else
            if x < 41 then
              3761455568216652286010102190024845941697512087857774770655696243927072596819253465875077394567121756229014751231465241326791681396840920059764296048005351654665
            else
              1450344230369639477276662831778186923929726773096201446392903044016302331430865417283871876657431373023837193260322628815907231162110496315385280814912605983172
        else
          if x < 44 then
            if x < 43 then
              6185404509190240345808116213205441338773031796222247053703196315333130862031132842708716902094093768565760202261774906472185522101737057551703714047211531634196
            else
              1665779629265394576783972462156513248076974372466707900356768955618753431879281042309919172787555043460544256167997438117729506685248454676803951947475017030950
          else
            if x < 45 then
              1801474749882382200304873126191524830793481681463897438200042321791652996656910331278933647039193688883463674362099610482956869777150405915754128154363628954510
            else
              if x < 46 then
                1888215636573608408767030764601503268158160127364438549365909791961002744540588595502051476141539391071753502854977214210761296309528544707895101379692194749085
              else
                5831873726849701858017820943322196333809862571344937244566600380221586024778173158952968671626364060986653071747891822604568565132738961026001664129476646636819
      else
        if x < 52 then
          if x < 49 then
            if x < 48 then
              3545194850390955635158739830041412621321542618477343382877721008246678166834761348467715695042724108878412000926179419439589696836911610605182073201303749091112
            else
              31068631652655863760603940185220222323240376735466326302946171519268152607236282315681260831596989497827850054422997008100890151322972372441691161243102153163
          else
            if x < 50 then
              1989953981254459300250495081857067642737396166126979375543356533916144291949012309337069179407055350858685571368619393866421578221452468945833161082729044398646
            else
              if x < 51 then
                6268694378331686479176330611296763893114474591587006429671714036424188236403288194496060937794160424874444268832404025755043328613768998551714026735292113445003
              else
                6370620438847818563286631369869294417294957307806199797553659291378140598142731372239557770179258399095493974811681338345405876683914419486884602412924876185546
        else
          if x < 54 then
            if x < 53 then
              2975341801026762730215003721866529269995267112098220769959590089479625903669052983451345082216418446959429377324801741852058258306915347760618754856604618805924
            else
              660048119025881228730040849016712315046091995147100811717867719418762245860330637975206026755362236156856683174681297221744393114028671792910814914625399235899
          else
            if x < 55 then
              793984793058765916094878699008025371186583839878051383029150656978283282484107616792966471819210676485004030864149793444864950515881780122480439480199812941885
            else
              if x < 56 then
                1245306369011838700467533981461280317594636990880769426631551230766014908770422453929624770203797944001813540319126274896783724336876140270143876046911544827415
              else
                369963128732758898608846411985576532640137190272903367379302430574097353790312789688477371671175713201405717925421674670956364214280808670830098877064541505174
    else
      if x < 66 then
        if x < 61 then
          if x < 59 then
            if x < 58 then
              2241552233483257970685335868747100578704936524628108362684060834689518730316963005325346073149449545738286049795636969408872843336976790767189319462440816859590
            else
              4400666054585587576331177291699295519403305958723155619997329085901811816313179317541944213621398147308788504916370747179222537349979702873656614551874964652724
          else
            if x < 60 then
              3447947974351027546173035997815342662747188263927208658987771065782355998648836677843771603102027896847285236416625998077855457191549312022753488036900991946403
            else
              2128323227303793916825289269567486095867655268445257209394700239019052199937159872917789737306778568328289815495946373490093317643507820674106737553929893749406
        else
          if x < 63 then
            if x < 62 then
              7965314228860976595711412970847361785809465674022757406453707452297996677197969440996082302203624093353788244502773596346383096435307317308766449430875527601573
            else
              7415319140946031638477854780208796091230383164088895664727811359104831719211146407554578362094112525499788480316629148301242241540738734093661795546044584527650
          else
            if x < 64 then
              7311475927570523520457707876264527367730509538168361112601002516151574030974537533317538163352087283492206739462165708580208565701774546615445385367823317599399
            else
              if x < 65 then
                8078650217315365720535106578010442589659592792542285843790813749652233152303224213672409751066508817687597775285483801749564050515124678560510472100031843013637
              else
                7863220055160353846255050159251606481937392135311158097508106225975030192388449502081811350162051720121873222050287688678197933015239495930825675927867648954140
      else
        if x < 71 then
          if x < 68 then
            if x < 67 then
              6758819076782464997865666183285689277589779994152428687131200023623342171163043106039739407920484159455593722239990938150544942993566370346268924569846146144012
            else
              7634101362318925504864508621009184043908982668289029354334351794201592088683419462822362843966819703566041996473768027863914602290381976343969497885901725467695
          else
            if x < 69 then
              7197388261792190156499711106296768223298765015521393161709179708384175382216992122491053624040966056515718003587642998956555353595109437656454208136004147660220
            else
              if x < 70 then
                7521663116157849656268697260254770635782523596984319027063909588691953728524924873035888469457157087301657717871652022926569427268383850025450591554422451308687
              else
                6864399146326567275592827833245694768317814351165405374610381071199356423237038247569425134401397794393423931836353808812899351518136542316991442265664137877663
        else
          if x < 73 then
            if x < 72 then
              7089244603641904216603243620034228465321885247746470480404007675455936593368521335342127047493851661298530972810826277739446257513608794153130280758812571343922
            else
              7751245272580714638236356708195137475879176224057469325883604787026185953866722711542333463786845649317924622099437051056146357040156992309057211076977753904565
          else
            if x < 74 then
              8131845853212015016928558382418954920442626437457600892888025470715056406696710916190489194105368991208808259744246892513843162163340242295212252746115154071698
            else
              if x < 75 then
                503319079421885310041788037470792288098736459016434345060848030136113546946752768983204886084550268138572128087251778754025715601140182064886681505900116937772
              else
                8299121353171581346644562117513889706389199941709366423527394836276001147463660906751736205474557964917020485047108195227073213386108218272759000306345921105301

/-- **T29**, the census magma `9f34fd7dead4e1ea…`: `x ◇ y = x + f (y - x)` on `ℤ / 29`. -/
theorem isIdemModel_T29 : IsIdemModel 29 (tiNat 29 (fun d => t29Table.getD d 0)) :=
  isIdemModel_ti (by decide +kernel) (by decide)

/-- **The two-piece model on `ℤ / 83`**: `f d = 47 d` on the nonzero squares, `72 d` on the
non-squares. -/
theorem isIdemModel_TP83 : IsIdemModel 83 (tiNat 83 (fun d => tp83Table.getD d 0)) :=
  isIdemModel_ti (by decide +kernel) (by decide)

/-- **The two-piece model on `ℤ / 167`**: `f d = 80 d` on the nonzero squares, `111 d` on the
non-squares. -/
theorem isIdemModel_TP167 : IsIdemModel 167 (tiNat 167 (fun d => tp167Table.getD d 0)) :=
  isIdemModel_ti (by decide +kernel) (by decide)

/-- **The two-piece model on `ℤ / 227`**: `f d = 128 d` on the nonzero squares, `146 d` on the
non-squares. -/
theorem isIdemModel_TP227 : IsIdemModel 227 (tiNat 227 (fun d => tp227Table.getD d 0)) :=
  isIdemModel_ti (by decide +kernel) (by decide)

/-- The census magma `ae850597310ca1e4…` of order `69`, relabelled so that its one idempotent
is `0`; row `x` is `rows69 x`, seven bits an entry. -/
def op69 (x y : Nat) : Nat := (rows69 x >>> (7 * y)) % 128

theorem isModel_69 : IsModel 69 op69 := isModel_of_checkModel (by decide +kernel)

/-- An idempotent census magma of order `76`, relabelled so that its submagma of `5` elements is
`{0, …, 4}`; row `x` is `rows76 x`, seven bits an entry. -/
def op76 (x y : Nat) : Nat := (rows76 x >>> (7 * y)) % 128

theorem isIdemModel_76 : IsIdemModel 76 op76 :=
  isIdemModel_of_check (by decide +kernel) (by decide +kernel)

theorem op76_sub : ∀ a b, a < 5 → b < 5 → op76 a b < 5 := by
  have := allBelow_spec (n := 5) (p := fun a => allBelow 5 fun b => decide (op76 a b < 5))
    (by decide +kernel)
  intro a b ha hb
  simpa using allBelow_spec (this a ha) b hb

/-! ## The Paley pencil

Fix `l`, a residue `q` modulo `l` and a set `Q` of residues, and a model on `k + 1` points with
`0` idempotent, the **seed**. The **Paley pencil** is the set `{e} ∪ (ℤ / l × ℤ / k)`: the
vertex `e` and, over each base point `x`, the line `{e} ∪ ({x} × ℤ / k)`, a copy of the seed
with `e` at `0`. Two points of one line multiply in the seed along that line; two points of
different lines multiply by

    (x, s) ◇ (y, t) = ((1 - q) x + q y,  t)        if y - x ∈ Q,
                    = ((1 - q) x + q y,  -s - t)   otherwise.

When `q` is a root of the tenth cyclotomic polynomial `Φ₁₀` modulo `l`, the multipliers `-q`,
`-(1 - q + q²)` and `(1 - q)(1 + q²)` keep nonzero residues nonzero, and `Q` is preserved by
the first and reversed by the other two, the pencil satisfies Equation 677
(`Spectrum677.isModel_paleyOp`). For a prime `l ≡ 11 (mod 20)` and two of the four roots `q` of
`Φ₁₀`, `Q` can be taken to be the quadratic residues; here it is whatever set passes the check.
This is the recipe in the comments of census magmas of orders `11 k + 1`. -/

section Paley

variable {l k : Nat} [NeZero l] [NeZero k]

/-- **The product between two lines**: the base multiplies as `(1 - q) x + q y`, the fibre by
`t` or `-s - t` according to the class of the base difference. -/
def offMul (q : Fin l) (Q : Fin l → Bool) (a b : Fin l × Fin k) : Fin l × Fin k :=
  ((1 - q) * a.1 + q * b.1, if Q (b.1 - a.1) then b.2 else -a.2 - b.2)

omit [NeZero k] in
theorem offMul_fst (q : Fin l) (Q : Fin l → Bool) (a b : Fin l × Fin k) :
    (offMul q Q a b).1 = (1 - q) * a.1 + q * b.1 := rfl

omit [NeZero k] in
theorem offMul_snd_true (q : Fin l) (Q : Fin l → Bool) {a b : Fin l × Fin k}
    (h : Q (b.1 - a.1) = true) : (offMul q Q a b).2 = b.2 := by
  simp [offMul, h]

omit [NeZero k] in
theorem offMul_snd_false (q : Fin l) (Q : Fin l → Bool) {a b : Fin l × Fin k}
    (h : Q (b.1 - a.1) = false) : (offMul q Q a b).2 = -a.2 - b.2 := by
  simp [offMul, h]

/-- The conditions on `(l, q, Q)` under which the Paley pencil satisfies Equation 677. -/
structure PaleyOK (l : Nat) [NeZero l] (q : Fin l) (Q : Fin l → Bool) : Prop where
  phi : q * q * q * q - q * q * q + q * q - q + 1 = 0
  nz : ∀ d : Fin l, d ≠ 0 → -q * d ≠ 0 ∧ -(1 - q + q * q) * d ≠ 0 ∧
    (1 - q) * (1 + q * q) * d ≠ 0
  cls : ∀ d : Fin l, d ≠ 0 → Q (-q * d) = Q d ∧ Q (-(1 - q + q * q) * d) = !Q d ∧
    Q ((1 - q) * (1 + q * q) * d) = !Q d

/-- **The word of Equation 677 between two lines.** For pairs `a = (x, i)` and `b = (y, j)`
with `x ≠ y`, the word `b ◇ (a ◇ ((b ◇ a) ◇ b))` computed with `offMul` returns `a`, and each
of its four products is between pairs with different bases. With `d = x - y` the base
differences are `d`, `-q d`, `-(1 - q + q²) d` and `(1 - q)(1 + q²) d`; the fibre coordinates are
`i, j, -i - j, i` when `d ∈ Q` and `-j - i, i, i, i` when not. -/
theorem offMul_word {q : Fin l} {Q : Fin l → Bool} (hP : PaleyOK l q Q) {a b : Fin l × Fin k}
    (hab : a.1 ≠ b.1) :
    (offMul q Q b a).1 ≠ b.1 ∧ a.1 ≠ (offMul q Q (offMul q Q b a) b).1 ∧
      b.1 ≠ (offMul q Q a (offMul q Q (offMul q Q b a) b)).1 ∧
      offMul q Q b (offMul q Q a (offMul q Q (offMul q Q b a) b)) = a := by
  have hΦ := hP.phi
  have hd : a.1 - b.1 ≠ 0 := fun h => hab (by grind)
  obtain ⟨n1, n2, n3⟩ := hP.nz _ hd
  obtain ⟨q1, q2, q3⟩ := hP.cls _ hd
  have h1 : b.1 - (offMul q Q b a).1 = -q * (a.1 - b.1) := by rw [offMul_fst]; grind
  have h2 : (offMul q Q (offMul q Q b a) b).1 - a.1 = -(1 - q + q * q) * (a.1 - b.1) := by
    simp only [offMul_fst]; grind
  have h3 : (offMul q Q a (offMul q Q (offMul q Q b a) b)).1 - b.1 =
      (1 - q) * (1 + q * q) * (a.1 - b.1) := by
    simp only [offMul_fst]; grind
  have h4 : (offMul q Q b (offMul q Q a (offMul q Q (offMul q Q b a) b))).1 = a.1 := by
    simp only [offMul_fst]; grind
  refine ⟨fun h => n1 (by rw [← h1, h]; grind), fun h => n2 (by rw [← h2, ← h]; grind),
    fun h => n3 (by rw [← h3, ← h]; grind), ?_⟩
  apply Prod.ext h4
  cases hQd : Q (a.1 - b.1)
  · have k1 : (offMul q Q b a).2 = -b.2 - a.2 := offMul_snd_false q Q hQd
    have k2 : (offMul q Q (offMul q Q b a) b).2 = a.2 := by
      rw [offMul_snd_false q Q (by rw [h1, q1, hQd]), k1]; grind
    have k3 : (offMul q Q a (offMul q Q (offMul q Q b a) b)).2 = a.2 := by
      rw [offMul_snd_true q Q (by rw [h2, q2, hQd]; rfl), k2]
    rw [offMul_snd_true q Q (by rw [h3, q3, hQd]; rfl), k3]
  · have k2 : (offMul q Q (offMul q Q b a) b).2 = b.2 :=
      offMul_snd_true q Q (by rw [h1, q1, hQd])
    have k3 : (offMul q Q a (offMul q Q (offMul q Q b a) b)).2 = -a.2 - b.2 := by
      rw [offMul_snd_false q Q (by rw [h2, q2, hQd]; rfl), k2]
    rw [offMul_snd_false q Q (by rw [h3, q3, hQd]; rfl), k3]; grind

/-- The point of the line over `x` with seed index `r`: the vertex for `r = 0`, and the point
`r - 1` of the fibre otherwise. -/
def onLine (x : Fin l) (r : Nat) : Option (Fin l × Fin k) :=
  if r = 0 then none else some (x, emb (r - 1))

/-- The seed index of a point: `0` for the vertex, `t + 1` for the point `t` of a fibre. -/
def lineIdx : Option (Fin l × Fin k) → Nat
  | none => 0
  | some p => p.2.val + 1

/-- The point `u` lies on the line over `x`. -/
def OnLine (x : Fin l) (u : Option (Fin l × Fin k)) : Prop := ∀ p, u = some p → p.1 = x

omit [NeZero l] in
theorem onLine_onLine (x : Fin l) (r : Nat) : OnLine x (onLine (k := k) x r) := by
  intro p hp
  unfold onLine at hp
  split at hp
  · cases hp
  · cases hp; rfl

omit [NeZero l] in
theorem lineIdx_onLine (x : Fin l) {r : Nat} (hr : r < k + 1) :
    lineIdx (onLine (k := k) x r) = r := by
  unfold onLine
  split
  · rename_i h; rw [h]; rfl
  · show (emb (r - 1) : Fin k).val + 1 = r
    show (r - 1) % k + 1 = r
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

omit [NeZero l] in
theorem onLine_lineIdx {x : Fin l} {u : Option (Fin l × Fin k)} (hu : OnLine x u) :
    onLine x (lineIdx u) = u := by
  rcases u with _ | ⟨y, t⟩
  · rfl
  · have hy : y = x := hu (y, t) rfl
    subst hy
    show (if t.val + 1 = 0 then none else some (y, emb (t.val + 1 - 1))) = some (y, t)
    rw [ite_of_neg (by omega), Nat.add_sub_cancel]
    exact congrArg some (Prod.ext rfl (Fin.ext (Nat.mod_eq_of_lt t.isLt)))

omit [NeZero l] [NeZero k] in
theorem lineIdx_lt (u : Option (Fin l × Fin k)) : lineIdx u < k + 1 := by
  rcases u with _ | ⟨y, t⟩
  · exact Nat.succ_pos k
  · exact Nat.succ_lt_succ t.isLt

/-- **Transport from a model.** If an operation on `α` agrees on `V` with a model on
`{0, …, n - 1}` through an encoding, it satisfies Equation 677 on `V`. -/
theorem eq677_of_transport {α : Type} (V : α → Prop) {n : Nat} (enc : α → Nat) (dec : Nat → α)
    (henc : ∀ a, V a → enc a < n) (hde : ∀ a, V a → dec (enc a) = a)
    (hed : ∀ k, k < n → enc (dec k) = k) {op : Nat → Nat → Nat} (hop : IsModel n op)
    (f : α → α → α) (hf : ∀ a b, V a → V b → f a b = dec (op (enc a) (enc b)))
    (hV : ∀ k, k < n → V (dec k)) :
    ∀ x y, V x → V y → f y (f x (f (f y x) y)) = x := by
  intro x y hx hy
  have ex := henc x hx
  have ey := henc y hy
  have l1 := hop.lt _ _ ey ex
  have l2 := hop.lt _ _ l1 ey
  have l3 := hop.lt _ _ ex l2
  rw [hf y x hy hx, hf _ y (hV _ l1) hy, hed _ l1, hf x _ hx (hV _ l2), hed _ l2,
    hf y _ hy (hV _ l3), hed _ l3, hop.eq _ _ ex ey, hde x hx]

variable (q : Fin l) (Q : Fin l → Bool) (S : Nat → Nat → Nat)

/-- **The Paley pencil**, on `{e} ∪ (ℤ / l × ℤ / k)` stored as `Option (Fin l × Fin k)`. -/
def pmul : Option (Fin l × Fin k) → Option (Fin l × Fin k) → Option (Fin l × Fin k)
  | none, none => none
  | none, some b => onLine b.1 (S 0 (b.2.val + 1))
  | some a, none => onLine a.1 (S (a.2.val + 1) 0)
  | some a, some b =>
    if a.1 = b.1 then onLine a.1 (S (a.2.val + 1) (b.2.val + 1)) else some (offMul q Q a b)

variable {q Q S}

/-- **On a line, the pencil multiplies as the seed.** -/
theorem pmul_line (hS0 : S 0 0 = 0) {x : Fin l} {u v : Option (Fin l × Fin k)}
    (hu : OnLine x u) (hv : OnLine x v) :
    pmul q Q S u v = onLine x (S (lineIdx u) (lineIdx v)) := by
  rcases u with _ | ⟨y, s⟩ <;> rcases v with _ | ⟨z, t⟩
  · show none = onLine x (S 0 0)
    rw [hS0]; rfl
  · have := hv (z, t) rfl
    subst this; rfl
  · have := hu (y, s) rfl
    subst this; rfl
  · have h1 : y = x := hu (y, s) rfl
    have h2 : z = x := hv (z, t) rfl
    show (if y = z then onLine y (S (s.val + 1) (t.val + 1)) else some (offMul q Q (y, s) (z, t))) =
      onLine x (S (s.val + 1) (t.val + 1))
    rw [ite_of_pos (h1.trans h2.symm), h1]

/-- **The Paley pencil satisfies Equation 677.** -/
theorem pmul_eq677 (hP : PaleyOK l q Q) (hS : IsModel (k + 1) S) (hS0 : S 0 0 = 0)
    (u v : Option (Fin l × Fin k)) :
    pmul q Q S v (pmul q Q S u (pmul q Q S (pmul q Q S v u) v)) = u := by
  -- on a common line, transport from the seed
  have line : ∀ x : Fin l, OnLine x u → OnLine x v →
      pmul q Q S v (pmul q Q S u (pmul q Q S (pmul q Q S v u) v)) = u := fun x hu hv =>
    eq677_of_transport (OnLine x) lineIdx (onLine x) (fun a _ => lineIdx_lt a)
      (fun _ h => onLine_lineIdx h) (fun _ h => lineIdx_onLine x h) hS (pmul q Q S)
      (fun _ _ ha hb => pmul_line hS0 ha hb) (fun r _ => onLine_onLine x r) u v hu hv
  rcases u with _ | ⟨a⟩
  · rcases v with _ | ⟨b⟩
    · exact line 0 (fun _ h => by cases h) (fun _ h => by cases h)
    · exact line b.1 (fun _ h => by cases h) (fun p h => by cases h; rfl)
  · rcases v with _ | ⟨b⟩
    · exact line a.1 (fun p h => by cases h; rfl) (fun _ h => by cases h)
    · by_cases hab : a.1 = b.1
      · exact line a.1 (fun p h => by cases h; rfl) (fun p h => by cases h; exact hab.symm)
      · obtain ⟨n1, n2, n3, hw⟩ := offMul_word (k := k) hP hab
        have e1 : pmul q Q S (some b) (some a) = some (offMul q Q b a) := by
          show (if b.1 = a.1 then _ else _) = _
          rw [ite_of_neg (Ne.symm hab)]
        have e2 : pmul q Q S (some (offMul q Q b a)) (some b) =
            some (offMul q Q (offMul q Q b a) b) := by
          show (if (offMul q Q b a).1 = b.1 then _ else _) = _
          rw [ite_of_neg n1]
        have e3 : pmul q Q S (some a) (some (offMul q Q (offMul q Q b a) b)) =
            some (offMul q Q a (offMul q Q (offMul q Q b a) b)) := by
          show (if a.1 = (offMul q Q (offMul q Q b a) b).1 then _ else _) = _
          rw [ite_of_neg n2]
        have e4 : pmul q Q S (some b) (some (offMul q Q a (offMul q Q (offMul q Q b a) b))) =
            some (offMul q Q b (offMul q Q a (offMul q Q (offMul q Q b a) b))) := by
          show (if b.1 = (offMul q Q a (offMul q Q (offMul q Q b a) b)).1 then _ else _) = _
          rw [ite_of_neg n3]
        rw [e1, e2, e3, e4, hw]

variable (l k)

/-- The pencil has `l k + 1` points: the vertex is `0`, and `(x, t)` is `x k + t + 1`. -/
def pencilEnum : Enum (Option (Fin l × Fin k)) (l * k + 1) where
  enc u := match u with
    | none => 0
    | some p => p.1.val * k + p.2.val + 1
  dec n := if n = 0 then none else some ((emb ((n - 1) / k) : Fin l), (emb ((n - 1) % k) : Fin k))
  enc_lt u := by
    rcases u with _ | ⟨x, t⟩
    · exact Nat.succ_pos _
    · exact Nat.succ_lt_succ (mul_add_lt x.isLt t.isLt)
  dec_enc u := by
    rcases u with _ | ⟨x, t⟩
    · rfl
    · show (if x.val * k + t.val + 1 = 0 then none else
        some ((emb ((x.val * k + t.val + 1 - 1) / k) : Fin l),
          (emb ((x.val * k + t.val + 1 - 1) % k) : Fin k))) = _
      rw [ite_of_neg (by omega), Nat.add_sub_cancel, mul_add_div t.isLt, mul_add_mod t.isLt]
      exact congrArg some (Prod.ext (Fin.ext (Nat.mod_eq_of_lt x.isLt))
        (Fin.ext (Nat.mod_eq_of_lt t.isLt)))
  enc_dec n hn := by
    by_cases h0 : n = 0
    · subst h0; rfl
    · have hk := Nat.pos_of_neZero k
      show (match (if n = 0 then none else
          some ((emb ((n - 1) / k) : Fin l), (emb ((n - 1) % k) : Fin k)) :
            Option (Fin l × Fin k)) with
        | none => 0
        | some p => p.1.val * k + p.2.val + 1) = n
      rw [ite_of_neg h0]
      show ((n - 1) / k % l) * k + (n - 1) % k % k + 1 = n
      rw [Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hk).2 (by rw [Nat.mul_comm] at hn ⊢; omega)),
        Nat.mod_mod, Nat.div_add_mod' (n - 1) k]
      omega

variable {l k}

variable (l k q Q S) in
/-- **The Paley pencil on `{0, …, l k}`.** -/
def paleyOp : Nat → Nat → Nat := fun a b =>
  (pencilEnum l k).enc (pmul q Q S ((pencilEnum l k).dec a) ((pencilEnum l k).dec b))

theorem isModel_paleyOp (hP : PaleyOK l q Q) (hS : IsModel (k + 1) S) (hS0 : S 0 0 = 0) :
    IsModel (l * k + 1) (paleyOp l k q Q S) :=
  (pencilEnum l k).isModel (pmul q Q S) fun x y => pmul_eq677 hP hS hS0 x y

/-- The vertex is idempotent. -/
theorem paleyOp_zero : paleyOp l k q Q S 0 0 = 0 := rfl

end Paley

/-! ### The Paley pencil at `11`

At an odd prime `l` the conditions on `q` and on the quadratic residues `Q` hold exactly when
`l ≡ 11 (mod 20)`, for two of the four roots of `Φ₁₀`. The certificate needs one: `l = 11`
with `q = 2`. The class test is Euler's criterion, `d ^ ((l - 1) / 2) = 1`; nothing about it is
trusted, the conditions being checked as they stand. -/

/-- The quadratic residues modulo `11`, by Euler's criterion. -/
def Q11 (d : Fin 11) : Bool := d.val ^ 5 % 11 == 1

theorem paleyOK_11 : PaleyOK 11 2 Q11 := ⟨by decide, by decide +kernel, by decide +kernel⟩

/-- **A Paley pencil turns a pointed model of size `k + 1` into one of size `l k + 1`.** -/
theorem hasPtModel_paley {l : Nat} [NeZero l] {q : Fin l} {Q : Fin l → Bool} (hP : PaleyOK l q Q)
    {k : Nat}
    (h : HasPtModel (k + 1)) : HasPtModel (l * k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.mul_zero]; exact hasPtModel_one
  haveI : NeZero k := ⟨by omega⟩
  obtain ⟨S, hS, hS0⟩ := exists_idem_zero h (Nat.succ_pos k)
  exact ⟨_, isModel_paleyOp hP hS hS0, Or.inr ⟨0, Nat.succ_pos _, paleyOp_zero⟩⟩

/-- **A Paley pencil over an idempotent seed is idempotent**: two equal points lie on a line,
where the pencil multiplies as the seed. -/
theorem paleyOp_idem {l k : Nat} [NeZero l] [NeZero k] {q : Fin l} {Q : Fin l → Bool}
    {S : Nat → Nat → Nat} (hS0 : S 0 0 = 0) (hSi : ∀ r, r < k + 1 → S r r = r) {a : Nat}
    (ha : a < l * k + 1) : paleyOp l k q Q S a a = a := by
  unfold paleyOp
  obtain ⟨x, hx⟩ : ∃ x, OnLine x ((pencilEnum l k).dec a) := by
    rcases h : (pencilEnum l k).dec a with _ | ⟨y, t⟩
    · exact ⟨0, fun _ h' => by cases h'⟩
    · exact ⟨y, fun p h' => by cases h'; rfl⟩
  rw [pmul_line hS0 hx hx, hSi _ (lineIdx_lt _), onLine_lineIdx hx]
  exact (pencilEnum l k).enc_dec a ha

/-- **The block model of order `166 = 11 · 15 + 1`**: the Paley pencil over `F₂[ζ]/(Φ₁₀)`. -/
def op166 : Nat → Nat → Nat := paleyOp 11 15 2 Q11 (phiOpN 2)

theorem isIdemModel_166 : IsIdemModel 166 op166 :=
  ⟨isModel_paleyOp paleyOK_11 (isIdemModel_phi 2).toIsModel
    ((isIdemModel_phi 2).idem 0 (by decide)),
    fun _ ha => paleyOp_idem ((isIdemModel_phi 2).idem 0 (by decide))
      (fun r hr => (isIdemModel_phi 2).idem r hr) ha⟩

/-! ## Truncated transversal designs

Take a `TD(K + 3, q)`, cut each of the groups `0, 1, 2` down to an interval of points
`[lo j, hi j)` and keep the other `K` groups whole (`Spectrum677.Cut`). The kept points form a
group-divisible design (`Spectrum677.Cut.gdd`): its groups are the kept parts of the groups,
and the block through two kept points of different groups is the set of kept points of the
line through them, which number `K` plus the number of cut groups whose point the line keeps
(`Spectrum677.Cut.bsize`). The kept points are numbered with the cut groups first, in order,
and then the whole groups (`Spectrum677.Cut.encPt`); a block is named by the points of its line
in groups `0` and `1`, which determine the line. -/

/-- A **truncated transversal design**: a `TD(K + 3, q)` and the intervals `[lo j, hi j)` kept
of the cut groups `j < 3`. -/
structure Cut (K q : Nat) where
  D : TD (K + 3) q
  lo : Nat → Nat
  hi : Nat → Nat

namespace Cut

variable {K q : Nat} (T : Cut K q)

/-- The interval kept of group `g`: `[glo g, ghi g)`. -/
def glo (g : Nat) : Nat := if g < 3 then T.lo g else 0

def ghi (g : Nat) : Nat := if g < 3 then T.hi g else q

/-- A point `(g, c)` is kept. -/
def Kept (P : Nat × Nat) : Prop := P.1 < K + 3 ∧ T.glo P.1 ≤ P.2 ∧ P.2 < T.ghi P.1

/-- Whether the line `L` keeps its point in the cut group `j`. -/
def keeps (L : T.D.Line) (j : Nat) : Bool := decide (T.lo j ≤ T.D.pt L j ∧ T.D.pt L j < T.hi j)

/-- The number of cut groups whose point the line `L` keeps. -/
def nopt (L : T.D.Line) : Nat :=
  (if T.keeps L 0 then 1 else 0) + (if T.keeps L 1 then 1 else 0) + (if T.keeps L 2 then 1 else 0)

/-- The number of kept points of the line `L`. -/
def bsize (L : T.D.Line) : Nat := K + T.nopt L

/-- The index in the block of `L` of its point in group `g`: the kept points of the cut groups
come first, in order, and then the whole groups. -/
def loc (L : T.D.Line) (g : Nat) : Nat :=
  if g = 0 then 0
  else if g = 1 then (if T.keeps L 0 then 1 else 0)
  else if g = 2 then (if T.keeps L 0 then 1 else 0) + (if T.keeps L 1 then 1 else 0)
  else T.nopt L + (g - 3)

/-- The group of the point with index `l` in the block of `L`. -/
def glob (L : T.D.Line) (l : Nat) : Nat :=
  if l < T.nopt L then
    (if l = 0 then (if T.keeps L 0 then 0 else if T.keeps L 1 then 1 else 2)
    else if l = 1 then (if T.keeps L 0 && T.keeps L 1 then 1 else 2) else 2)
  else l - T.nopt L + 3

/-- What a truncation needs: the intervals lie inside the groups. -/
structure Valid : Prop where
  lo_le : ∀ j, j < 3 → T.lo j ≤ T.hi j
  hi_le : ∀ j, j < 3 → T.hi j ≤ q

variable {T}

/-- The point of the line `L` in group `g`. -/
abbrev P (L : T.D.Line) (g : Nat) : Nat × Nat := (g, T.D.pt L g)

theorem glo_le_ghi (hT : T.Valid) (g : Nat) : T.glo g ≤ T.ghi g := by
  unfold glo ghi
  split
  · exact hT.lo_le g ‹_›
  · exact Nat.zero_le q

theorem ghi_le (hT : T.Valid) (g : Nat) : T.ghi g ≤ q := by
  unfold ghi
  split
  · exact hT.hi_le g ‹_›
  · exact Nat.le_refl q

/-- The point of `L` in group `g` is kept exactly when `L` keeps it. -/
theorem kept_P_iff (L : T.D.Line) (g : Nat) :
    T.Kept (P L g) ↔ g < K + 3 ∧ (g < 3 → T.keeps L g = true) := by
  unfold Kept keeps glo ghi
  constructor
  · rintro ⟨hg, h1, h2⟩
    refine ⟨hg, fun h3 => ?_⟩
    simp only [h3, ite_true] at h1 h2
    simp only [decide_eq_true_eq]
    exact ⟨h1, h2⟩
  · rintro ⟨hg, h⟩
    refine ⟨hg, ?_⟩
    by_cases h3 : g < 3
    · have := h h3
      simp only [decide_eq_true_eq] at this
      simp only [h3, ite_true]
      exact this
    · simp only [h3, ite_false]
      exact ⟨Nat.zero_le _, T.D.pt_lt L g hg⟩

theorem nopt_le (L : T.D.Line) : T.nopt L ≤ 3 := by
  unfold nopt
  split <;> split <;> split <;> omega

theorem loc_of_ge {L : T.D.Line} {g : Nat} (h : 3 ≤ g) : T.loc L g = T.nopt L + (g - 3) := by
  unfold loc
  rw [ite_of_neg (by omega), ite_of_neg (by omega), ite_of_neg (by omega)]

theorem glob_of_ge {L : T.D.Line} {l : Nat} (h : T.nopt L ≤ l) :
    T.glob L l = l - T.nopt L + 3 := by
  unfold glob
  rw [ite_of_neg (by omega)]

/-- A kept point of a line has an index in its block. -/
theorem loc_spec {L : T.D.Line} {g : Nat} (hg : g < K + 3) (hk : g < 3 → T.keeps L g = true) :
    T.loc L g < T.bsize L ∧ T.glob L (T.loc L g) = g := by
  by_cases h3 : g < 3
  · have hk' := hk h3
    unfold bsize
    rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl <;>
    · unfold loc glob nopt
      cases e0 : T.keeps L 0 <;> cases e1 : T.keeps L 1 <;> cases e2 : T.keeps L 2 <;>
        simp_all <;> omega
  · rw [loc_of_ge (by omega), glob_of_ge (by omega)]
    unfold bsize
    omega

/-- Every index of a block is a kept point of its line. -/
theorem glob_spec {L : T.D.Line} {l : Nat} (hl : l < T.bsize L) :
    (T.glob L l < K + 3 ∧ (T.glob L l < 3 → T.keeps L (T.glob L l) = true)) ∧
      T.loc L (T.glob L l) = l := by
  unfold bsize at hl
  by_cases hn : l < T.nopt L
  · have h3 := nopt_le (T := T) L
    rcases (show l = 0 ∨ l = 1 ∨ l = 2 by omega) with rfl | rfl | rfl <;>
    · unfold loc glob nopt at *
      cases e0 : T.keeps L 0 <;> cases e1 : T.keeps L 1 <;> cases e2 : T.keeps L 2 <;>
        simp_all <;> omega
  · rw [glob_of_ge (by omega), loc_of_ge (by omega)]
    refine ⟨⟨by omega, fun h => absurd h (by omega)⟩, by omega⟩

/-! ### Numbering the kept points -/

variable (T)

/-- The sizes of the three cut groups, and their sum. -/
def n0 : Nat := T.hi 0 - T.lo 0
def n1 : Nat := T.hi 1 - T.lo 1
def n2 : Nat := T.hi 2 - T.lo 2
def S : Nat := T.n0 + T.n1 + T.n2

/-- The kept points, numbered: the cut groups first, then the whole groups. -/
def encPt (P : Nat × Nat) : Nat :=
  if P.1 = 0 then P.2 - T.lo 0
  else if P.1 = 1 then T.n0 + (P.2 - T.lo 1)
  else if P.1 = 2 then T.n0 + T.n1 + (P.2 - T.lo 2)
  else T.S + ((P.1 - 3) * q + P.2)

def decPt (k : Nat) : Nat × Nat :=
  if k < T.n0 then (0, T.lo 0 + k)
  else if k < T.n0 + T.n1 then (1, T.lo 1 + (k - T.n0))
  else if k < T.S then (2, T.lo 2 + (k - T.n0 - T.n1))
  else (3 + (k - T.S) / q, (k - T.S) % q)

variable {T}

theorem kept_iff {g c : Nat} : T.Kept (g, c) ↔ g < K + 3 ∧ T.glo g ≤ c ∧ c < T.ghi g :=
  Iff.rfl

theorem glo_of_lt {g : Nat} (h : g < 3) : T.glo g = T.lo g := ite_of_pos h
theorem ghi_of_lt {g : Nat} (h : g < 3) : T.ghi g = T.hi g := ite_of_pos h
theorem glo_of_ge {g : Nat} (h : ¬ g < 3) : T.glo g = 0 := ite_of_neg h
theorem ghi_of_ge {g : Nat} (h : ¬ g < 3) : T.ghi g = q := ite_of_neg h

theorem encPt_lt (hT : T.Valid) {P : Nat × Nat} (h : T.Kept P) : T.encPt P < T.S + K * q := by
  obtain ⟨g, c⟩ := P
  obtain ⟨hg, h1, h2⟩ := kept_iff.1 h
  have l0 := hT.lo_le 0 (by omega)
  have l1 := hT.lo_le 1 (by omega)
  have l2 := hT.lo_le 2 (by omega)
  unfold encPt S n0 n1 n2
  dsimp only
  by_cases a0 : g = 0
  · subst a0; rw [glo_of_lt (by omega)] at h1; rw [ghi_of_lt (by omega)] at h2; simp; omega
  by_cases a1 : g = 1
  · subst a1; rw [glo_of_lt (by omega)] at h1; rw [ghi_of_lt (by omega)] at h2; simp; omega
  by_cases a2 : g = 2
  · subst a2; rw [glo_of_lt (by omega)] at h1; rw [ghi_of_lt (by omega)] at h2; simp; omega
  rw [ghi_of_ge (by omega)] at h2
  rw [ite_of_neg a0, ite_of_neg a1, ite_of_neg a2]
  have := mul_add_lt (show g - 3 < K by omega) h2
  omega

theorem encPt_zero {c : Nat} : T.encPt (0, c) = c - T.lo 0 := ite_of_pos rfl
theorem encPt_one {c : Nat} : T.encPt (1, c) = T.n0 + (c - T.lo 1) := by
  unfold encPt; rw [ite_of_neg (by omega), ite_of_pos rfl]
theorem encPt_two {c : Nat} : T.encPt (2, c) = T.n0 + T.n1 + (c - T.lo 2) := by
  unfold encPt; rw [ite_of_neg (by omega), ite_of_neg (by omega), ite_of_pos rfl]
theorem encPt_of_ge {g c : Nat} (h : 3 ≤ g) : T.encPt (g, c) = T.S + ((g - 3) * q + c) := by
  unfold encPt
  dsimp only
  rw [ite_of_neg (by omega), ite_of_neg (by omega), ite_of_neg (by omega)]

theorem decPt_of_lt0 {k : Nat} (h : k < T.n0) : T.decPt k = (0, T.lo 0 + k) := ite_of_pos h
theorem decPt_of_lt1 {k : Nat} (h0 : ¬ k < T.n0) (h : k < T.n0 + T.n1) :
    T.decPt k = (1, T.lo 1 + (k - T.n0)) := by
  unfold decPt; rw [ite_of_neg h0, ite_of_pos h]
theorem decPt_of_lt2 {k : Nat} (h0 : ¬ k < T.n0) (h1 : ¬ k < T.n0 + T.n1) (h : k < T.S) :
    T.decPt k = (2, T.lo 2 + (k - T.n0 - T.n1)) := by
  unfold decPt; rw [ite_of_neg h0, ite_of_neg h1, ite_of_pos h]
theorem decPt_of_ge {k : Nat} (h : ¬ k < T.S) :
    T.decPt k = (3 + (k - T.S) / q, (k - T.S) % q) := by
  have eS : T.S = T.n0 + T.n1 + T.n2 := rfl
  unfold decPt; rw [ite_of_neg (by omega), ite_of_neg (by omega), ite_of_neg h]

theorem decPt_encPt (hT : T.Valid) {P : Nat × Nat} (h : T.Kept P) : T.decPt (T.encPt P) = P := by
  obtain ⟨g, c⟩ := P
  obtain ⟨hg, h1, h2⟩ := kept_iff.1 h
  have l0 := hT.lo_le 0 (by omega)
  have l1 := hT.lo_le 1 (by omega)
  have l2 := hT.lo_le 2 (by omega)
  have e0 : T.n0 = T.hi 0 - T.lo 0 := rfl
  have e1 : T.n1 = T.hi 1 - T.lo 1 := rfl
  have e2 : T.n2 = T.hi 2 - T.lo 2 := rfl
  have eS : T.S = T.n0 + T.n1 + T.n2 := rfl
  by_cases a0 : g = 0
  · subst a0
    rw [glo_of_lt (by omega)] at h1
    rw [ghi_of_lt (by omega)] at h2
    rw [encPt_zero, decPt_of_lt0 (by omega)]
    congr 1; omega
  by_cases a1 : g = 1
  · subst a1
    rw [glo_of_lt (by omega)] at h1
    rw [ghi_of_lt (by omega)] at h2
    rw [encPt_one, decPt_of_lt1 (by omega) (by omega)]
    congr 1; omega
  by_cases a2 : g = 2
  · subst a2
    rw [glo_of_lt (by omega)] at h1
    rw [ghi_of_lt (by omega)] at h2
    rw [encPt_two, decPt_of_lt2 (by omega) (by omega) (by omega)]
    congr 1; omega
  rw [ghi_of_ge (by omega)] at h2
  rw [encPt_of_ge (by omega), decPt_of_ge (by omega), Nat.add_sub_cancel_left,
    mul_add_div h2, mul_add_mod h2]
  congr 1; omega

theorem kept_decPt (hT : T.Valid) {k : Nat} (h : k < T.S + K * q) : T.Kept (T.decPt k) := by
  have l0 := hT.lo_le 0 (by omega)
  have l1 := hT.lo_le 1 (by omega)
  have l2 := hT.lo_le 2 (by omega)
  have e0 : T.n0 = T.hi 0 - T.lo 0 := rfl
  have e1 : T.n1 = T.hi 1 - T.lo 1 := rfl
  have e2 : T.n2 = T.hi 2 - T.lo 2 := rfl
  have eS : T.S = T.n0 + T.n1 + T.n2 := rfl
  unfold decPt
  by_cases b0 : k < T.n0
  · rw [ite_of_pos b0, kept_iff, glo_of_lt (by omega), ghi_of_lt (by omega)]; omega
  rw [ite_of_neg b0]
  by_cases b1 : k < T.n0 + T.n1
  · rw [ite_of_pos b1, kept_iff, glo_of_lt (by omega), ghi_of_lt (by omega)]; omega
  rw [ite_of_neg b1]
  by_cases b2 : k < T.S
  · rw [ite_of_pos b2, kept_iff, glo_of_lt (by omega), ghi_of_lt (by omega)]; omega
  rw [ite_of_neg b2]
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hd : (k - T.S) / q < K := (Nat.div_lt_iff_lt_mul hq).2 (by omega)
  have h3 : ¬ 3 + (k - T.S) / q < 3 := Nat.not_lt.mpr (Nat.le_add_right 3 _)
  rw [kept_iff, glo_of_ge h3, ghi_of_ge h3]
  exact ⟨by omega, Nat.zero_le _, Nat.mod_lt _ hq⟩

theorem encPt_decPt (hT : T.Valid) {k : Nat} (h : k < T.S + K * q) :
    T.encPt (T.decPt k) = k := by
  have l0 := hT.lo_le 0 (by omega)
  have l1 := hT.lo_le 1 (by omega)
  have l2 := hT.lo_le 2 (by omega)
  have e0 : T.n0 = T.hi 0 - T.lo 0 := rfl
  have e1 : T.n1 = T.hi 1 - T.lo 1 := rfl
  have e2 : T.n2 = T.hi 2 - T.lo 2 := rfl
  have eS : T.S = T.n0 + T.n1 + T.n2 := rfl
  by_cases b0 : k < T.n0
  · rw [decPt_of_lt0 b0, encPt_zero]; omega
  by_cases b1 : k < T.n0 + T.n1
  · rw [decPt_of_lt1 b0 b1, encPt_one]; omega
  by_cases b2 : k < T.S
  · rw [decPt_of_lt2 b0 b1 b2, encPt_two]; omega
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; omega)
  rw [decPt_of_ge b2, encPt_of_ge (Nat.le_add_right 3 _), Nat.add_sub_cancel_left,
    Nat.div_add_mod' (k - T.S) q]
  omega

/-! ### The design of kept points -/

variable (T)

/-- A line, named by its points in groups `0` and `1`. -/
def code (L : T.D.Line) : Nat := T.D.pt L 0 * q + T.D.pt L 1

/-- The line a name stands for. -/
def lineOf (b : Nat) : T.D.Line := T.D.line 0 (b / q) 1 (b % q)

variable {T}

theorem lineOf_code (L : T.D.Line) : T.lineOf (T.code L) = L := by
  have h1 := T.D.pt_lt L 1 (by omega)
  unfold lineOf code
  rw [mul_add_div h1, mul_add_mod h1]
  exact T.D.line_pt L 0 1 (by omega) (by omega) (by omega)

variable (T)

/-- **The group-divisible design of the kept points.** -/
def gdd : GDD Nat where
  n := T.S + K * q
  grp x := (T.decPt x).1
  gsz g := T.ghi g - T.glo g
  gpt g i := T.encPt (g, T.glo g + i)
  gidx x := (T.decPt x).2 - T.glo (T.decPt x).1
  blk x y := T.code (T.D.line (T.decPt x).1 (T.decPt x).2 (T.decPt y).1 (T.decPt y).2)
  sz b := T.bsize (T.lineOf b)
  pt b l := T.encPt (P (T.lineOf b) (T.glob (T.lineOf b) l))
  idx b x := T.loc (T.lineOf b) (T.decPt x).1

variable {T}

/-- The line through two kept points of different groups, and their indices on it. -/
theorem cross_line (hT : T.Valid) {x y : Nat} (h : T.gdd.Cross x y) :
    T.lineOf (T.gdd.blk x y) =
        T.D.line (T.decPt x).1 (T.decPt x).2 (T.decPt y).1 (T.decPt y).2 ∧
      T.D.pt (T.lineOf (T.gdd.blk x y)) (T.decPt x).1 = (T.decPt x).2 ∧
      T.D.pt (T.lineOf (T.gdd.blk x y)) (T.decPt y).1 = (T.decPt y).2 ∧
      T.Kept (T.decPt x) ∧ T.Kept (T.decPt y) := by
  obtain ⟨hx, hy, hne⟩ := h
  have kx := kept_decPt hT hx
  have ky := kept_decPt hT hy
  have e : T.lineOf (T.gdd.blk x y) =
      T.D.line (T.decPt x).1 (T.decPt x).2 (T.decPt y).1 (T.decPt y).2 := lineOf_code _
  obtain ⟨l1, l2⟩ := T.D.pt_line _ _ _ _ kx.1 ky.1 hne
    (Nat.lt_of_lt_of_le kx.2.2 (ghi_le hT _)) (Nat.lt_of_lt_of_le ky.2.2 (ghi_le hT _))
  exact ⟨e, by rw [e, l1], by rw [e, l2], kx, ky⟩

/-- **The kept points form a group-divisible design.** -/
theorem gdd_valid (hT : T.Valid) : T.gdd.Valid := by
  have keptP : ∀ (L : T.D.Line) (l : Nat), l < T.bsize L → T.Kept (P L (T.glob L l)) :=
    fun L l hl => (kept_P_iff L _).2 (glob_spec hl).1
  -- the index of a kept point of a line
  have idxK : ∀ (L : T.D.Line) (x : Nat), x < T.S + K * q → T.Kept (T.decPt x) →
      T.D.pt L (T.decPt x).1 = (T.decPt x).2 →
      T.loc L (T.decPt x).1 < T.bsize L ∧
        T.encPt (P L (T.glob L (T.loc L (T.decPt x).1))) = x := by
    intro L x hx kx hpt
    have kP : T.Kept (P L (T.decPt x).1) := by
      show T.Kept ((T.decPt x).1, T.D.pt L (T.decPt x).1)
      rw [hpt]
      exact kx
    obtain ⟨h1, h2⟩ := loc_spec ((kept_P_iff L _).1 kP).1 ((kept_P_iff L _).1 kP).2
    refine ⟨h1, ?_⟩
    show T.encPt (T.glob L (T.loc L (T.decPt x).1),
      T.D.pt L (T.glob L (T.loc L (T.decPt x).1))) = x
    rw [h2, hpt]
    exact encPt_decPt hT hx
  have keptG : ∀ x i, x < T.gdd.n → i < T.gdd.gsz (T.gdd.grp x) →
      T.Kept ((T.decPt x).1, T.glo (T.decPt x).1 + i) := by
    intro x i hx hi
    have kx := kept_decPt hT hx
    change i < T.ghi (T.decPt x).1 - T.glo (T.decPt x).1 at hi
    have := glo_le_ghi hT (T.decPt x).1
    exact kept_iff.2 ⟨kx.1, by omega, by omega⟩
  refine
    { gidx_lt := ?_, gpt_gidx := ?_, gpt_lt := ?_, grp_gpt := ?_, gidx_gpt := ?_,
      idx_lt := ?_, pt_idx := ?_, idx_lt' := ?_, pt_idx' := ?_, pt_lt := ?_, idx_pt := ?_,
      cross_pt := ?_, blk_pt := ?_ }
  · intro x hx
    have := kept_decPt hT hx
    show (T.decPt x).2 - T.glo (T.decPt x).1 < T.ghi (T.decPt x).1 - T.glo (T.decPt x).1
    obtain ⟨-, h1, h2⟩ := this
    omega
  · intro x hx
    have := kept_decPt hT hx
    show T.encPt ((T.decPt x).1, T.glo (T.decPt x).1 + ((T.decPt x).2 - T.glo (T.decPt x).1)) = x
    obtain ⟨-, h1, -⟩ := this
    rw [show T.glo (T.decPt x).1 + ((T.decPt x).2 - T.glo (T.decPt x).1) = (T.decPt x).2 by
      omega]
    exact encPt_decPt hT hx
  · intro x i hx hi
    exact encPt_lt hT (keptG x i hx hi)
  · intro x i hx hi
    show (T.decPt (T.encPt ((T.decPt x).1, T.glo (T.decPt x).1 + i))).1 = (T.decPt x).1
    rw [decPt_encPt hT (keptG x i hx hi)]
  · intro x i hx hi
    show (T.decPt (T.encPt ((T.decPt x).1, T.glo (T.decPt x).1 + i))).2 -
      T.glo (T.decPt (T.encPt ((T.decPt x).1, T.glo (T.decPt x).1 + i))).1 = i
    rw [decPt_encPt hT (keptG x i hx hi)]
    dsimp only
    omega
  · intro x y h
    obtain ⟨-, e1, -, kx, -⟩ := cross_line hT h
    exact (idxK _ x h.1 kx e1).1
  · intro x y h
    obtain ⟨-, e1, -, kx, -⟩ := cross_line hT h
    exact (idxK _ x h.1 kx e1).2
  · intro x y h
    obtain ⟨-, -, e2, -, ky⟩ := cross_line hT h
    exact (idxK _ y h.2.1 ky e2).1
  · intro x y h
    obtain ⟨-, -, e2, -, ky⟩ := cross_line hT h
    exact (idxK _ y h.2.1 ky e2).2
  · intro x y i _ hi
    exact encPt_lt hT (keptP _ i hi)
  · intro x y i _ hi
    show T.loc _ (T.decPt (T.encPt (P _ (T.glob _ i)))).1 = i
    rw [decPt_encPt hT (keptP _ i hi)]
    exact (glob_spec hi).2
  · intro x y i j _ hi hj hij
    show (T.decPt (T.encPt (P _ (T.glob _ i)))).1 ≠ (T.decPt (T.encPt (P _ (T.glob _ j)))).1
    rw [decPt_encPt hT (keptP _ i hi), decPt_encPt hT (keptP _ j hj)]
    intro e
    apply hij
    rw [← (glob_spec hi).2, ← (glob_spec hj).2]
    exact congrArg _ e
  · intro x y i j _ hi hj hij
    show T.code (T.D.line (T.decPt (T.encPt (P _ (T.glob _ i)))).1
      (T.decPt (T.encPt (P _ (T.glob _ i)))).2 (T.decPt (T.encPt (P _ (T.glob _ j)))).1
      (T.decPt (T.encPt (P _ (T.glob _ j)))).2) = T.gdd.blk x y
    rw [decPt_encPt hT (keptP _ i hi), decPt_encPt hT (keptP _ j hj)]
    have hg : T.glob (T.lineOf (T.gdd.blk x y)) i ≠ T.glob (T.lineOf (T.gdd.blk x y)) j := by
      intro e
      apply hij
      rw [← (glob_spec hi).2, ← (glob_spec hj).2]
      exact congrArg _ e
    dsimp only [P]
    rw [T.D.line_pt _ _ _ (glob_spec hi).1.1 (glob_spec hj).1.1 hg]
    have : T.code (T.lineOf (T.gdd.blk x y)) = T.gdd.blk x y := by
      show T.code (T.lineOf (T.code _)) = T.code _
      rw [lineOf_code]
    exact this

/-- The point `x < hi 0 - lo 0`, when `lo 0 = 0`, is the point `x` of group `0`. -/
theorem gdd_grp_lt0 {x : Nat} (h : x < T.n0) : T.gdd.grp x = 0 := by
  show (T.decPt x).1 = 0
  rw [decPt_of_lt0 h]

/-- Group `0` with `lo 0 = 0` is numbered first: its point `i` is `i`. -/
theorem gdd_gpt0 (h0 : T.lo 0 = 0) {i : Nat} : T.gdd.gpt 0 i = i := by
  show T.encPt (0, T.glo 0 + i) = i
  rw [encPt_zero, glo_of_lt (by omega), h0]
  omega

end Cut

/-! ## Designs developed from base blocks

A design invariant under translations is determined by a few **base blocks**: the others are
their translates (`Spectrum677.Dev`). The points are `W` **fixed points** `0, …, W - 1`, which no
translation moves, and `R` **orbits** of `ℤ / N`: the point `W + N r + a`, for `r < R` and
`a < N`, is the point `a` of the orbit `r`, and the translation by `t` moves it to the point
`a + t` of the same orbit (`Spectrum677.Dev.shift`). The groups are the fixed points, all
together, and in the orbit `r` the classes of `a` modulo `Mo r`, a divisor of `N`
(`Spectrum677.Dev.grp`): each point alone when `Mo r = N`, the whole orbit when `Mo r = 1`.

An ordered pair of points of different groups has a **key** (`Spectrum677.Dev.key`) that the
translations do not change: the fixed point and the orbit of the other point, or the two
orbits and the difference of the positions. Equal keys come from translates
(`Spectrum677.Dev.translate_of_key_eq`). So the translates of the base blocks put every pair of
points of different groups in exactly one block when the keys of the ordered pairs of entries
of the base blocks are distinct and are every key there is. `Spectrum677.Dev.check` certifies
this by evaluation: it sets one bit per key, failing on a key met twice, and then reads off the
key of every pair of points of different groups up to translation. The design is then
`Spectrum677.Dev.gdd` (`Spectrum677.Dev.gdd_valid`); a block is named `i N + t`, the `i`-th base
block translated by `t`. -/

/-- The bits of a list of numbers, as one number, or `none` if a number repeats. -/
noncomputable def bitsOf : List Nat → Nat → Option Nat :=
  List.rec (motive := fun _ => Nat → Option Nat) (fun B => some B)
    (fun k _ ih B => if B.testBit k then none else ih (B ||| 1 <<< k))

theorem testBit_or_shift (B k j : Nat) :
    (B ||| 1 <<< k).testBit j = (B.testBit j || decide (j = k)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : j = k
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **What `bitsOf` certifies**: the list has no repetition, misses the bits it started from,
and its bits are those of the result. -/
theorem bitsOf_spec : ∀ (l : List Nat) (B₀ B : Nat), bitsOf l B₀ = some B →
    l.Nodup ∧ (∀ k ∈ l, B₀.testBit k = false) ∧
      ∀ k, B.testBit k = true → B₀.testBit k = true ∨ k ∈ l
  | [], B₀, B, h => by
    have : B₀ = B := Option.some.inj h
    subst this
    exact ⟨List.nodup_nil, fun k hk => by simp at hk, fun k hk => Or.inl hk⟩
  | k :: l, B₀, B, h => by
    change (if B₀.testBit k then none else bitsOf l (B₀ ||| 1 <<< k)) = some B at h
    by_cases hb : B₀.testBit k = true
    · rw [ite_of_pos hb] at h
      cases h
    rw [ite_of_neg hb] at h
    obtain ⟨hn, hf, hs⟩ := bitsOf_spec l _ _ h
    refine ⟨List.nodup_cons.2 ⟨fun hk => ?_, hn⟩, fun j hj => ?_, fun j hj => ?_⟩
    · have := hf k hk
      rw [testBit_or_shift] at this
      simp at this
    · rcases List.mem_cons.1 hj with rfl | hj
      · simpa using hb
      · have := hf j hj
        rw [testBit_or_shift] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.1
    · rcases hs j hj with h1 | h1
      · rw [testBit_or_shift] at h1
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
        rcases h1 with h1 | rfl
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- The quotient and remainder of `a R + b` by `R`, for `b < R`. -/
theorem eq_of_mul_add_eq {R a b a' b' : Nat} (hb : b < R) (hb' : b' < R)
    (h : a * R + b = a' * R + b') : a = a' ∧ b = b' := by
  have h1 : (a * R + b) / R = a := mul_add_div hb
  have h2 : (a' * R + b') / R = a' := mul_add_div hb'
  have ha : a = a' := by rw [← h1, ← h2, h]
  subst ha
  exact ⟨rfl, by omega⟩

/-- A map with no repeated value on a list is one to one there. -/
theorem inj_of_nodup_map {α : Type} {f : α → Nat} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, h, a, b, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · rw [ha'] at he
      exact absurd (he ▸ List.mem_map_of_mem hb') h.1
    · rw [hb'] at he
      exact absurd (he.symm ▸ List.mem_map_of_mem ha') h.1
    · exact inj_of_nodup_map h.2 ha' hb' he

theorem getD_mem {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- In a list without repetitions, an entry's first index is its index. -/
theorem idxOf_getD : ∀ {l : List Nat}, l.Nodup → ∀ {i : Nat}, i < l.length →
    l.idxOf (l.getD i 0) = i
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | a :: l, hl, 0, _ => by rw [List.getD_cons_zero, List.idxOf_cons_self]
  | a :: l, hl, i + 1, h => by
    rw [List.getD_cons_succ, List.idxOf_cons]
    have hm : l.getD i 0 ∈ l := getD_mem (by simpa using h)
    have hne : (a == l.getD i 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      exact (List.nodup_cons.1 hl).1 (e ▸ hm)
    rw [hne, idxOf_getD (List.nodup_cons.1 hl).2 (by simpa using h)]
    rfl

/-- The data of a developed design: `W` fixed points, `R` orbits of `ℤ / N`, the moduli of the
groups in each orbit, and the base blocks, as lists of points. -/
structure Dev where
  W : Nat
  R : Nat
  N : Nat
  Mo : Nat → Nat
  base : List (List Nat)

namespace Dev

variable (E : Dev)

/-- The orbit and the position of a point outside the fixed points. -/
def orb (c : Nat) : Nat := (c - E.W) / E.N
def pos (c : Nat) : Nat := (c - E.W) % E.N

/-- The point `a` of the orbit `r`. -/
def ptOf (r a : Nat) : Nat := E.W + (r * E.N + a)

/-- **Translation by `t`.** -/
def shift (t c : Nat) : Nat := if c < E.W then c else E.ptOf (E.orb c) ((E.pos c + t) % E.N)

/-- **The group of a point**: `0` for the fixed points, and `1 + r N + (a mod Mo r)` for the
point `a` of the orbit `r`. -/
def grp (c : Nat) : Nat := if c < E.W then 0 else 1 + (E.orb c * E.N + E.pos c % E.Mo (E.orb c))

/-- **The key of an ordered pair of points**: the fixed point and the orbit of the other point,
in one of two ranges by the order of the pair, or the two orbits and the difference of the
positions, above `2 W R`. -/
def key (x y : Nat) : Nat :=
  if x < E.W then x * E.R + E.orb y
  else if y < E.W then E.W * E.R + (y * E.R + E.orb x)
  else 2 * E.W * E.R + ((E.orb x * E.R + E.orb y) * E.N + (E.pos y + E.N - E.pos x) % E.N)

/-- The entry `j` of the base block `i`. -/
def entry (i j : Nat) : Nat := (E.base.getD i []).getD j 0

/-- The ordered pairs of distinct places `(i, j₁, j₂)` of the base blocks. -/
def triples : List (Nat × Nat × Nat) :=
  (List.range E.base.length).flatMap fun i =>
    (List.range (E.base.getD i []).length).flatMap fun j₁ =>
      (List.range (E.base.getD i []).length).filterMap fun j₂ =>
        if j₁ = j₂ then none else some (i, j₁, j₂)

/-- The key of the entries at an ordered pair of places. -/
def tkey (p : Nat × Nat × Nat) : Nat := E.key (E.entry p.1 p.2.1) (E.entry p.1 p.2.2)

/-- **The check.** The parameters make sense, the entries are points and lie in distinct groups
within a block, the keys of the ordered pairs of places do not repeat, and every pair of points
of different groups, translated so that its first point outside the fixed points is the point
`0` of its orbit, has its key among them. -/
noncomputable def check : Bool :=
  decide (0 < E.N) && allBelow E.R (fun r => decide (0 < E.Mo r) && E.N % E.Mo r == 0) &&
    E.base.all (fun L => decide L.Nodup && L.all fun c => decide (c < E.W + E.R * E.N)) &&
    E.triples.all (fun p => E.grp (E.entry p.1 p.2.1) != E.grp (E.entry p.1 p.2.2)) &&
    match bitsOf (E.triples.map E.tkey) 0 with
    | none => false
    | some B =>
      allBelow E.W (fun h => allBelow E.R fun s =>
        B.testBit (E.key h (E.ptOf s 0)) && B.testBit (E.key (E.ptOf s 0) h)) &&
      allBelow E.R (fun r => allBelow E.R fun s => allBelow E.N fun d =>
        E.grp (E.ptOf r 0) == E.grp (E.ptOf s d) || B.testBit (E.key (E.ptOf r 0) (E.ptOf s d)))

/-- The place of the key `k` among the ordered pairs of places. -/
def findKey (k : Nat) : Nat × Nat × Nat :=
  (E.triples.find? fun p => E.tkey p == k).getD (0, 0, 0)

/-- The translation taking `c` to `c'`, two points of one orbit. -/
def tr (c c' : Nat) : Nat := (E.pos c' + E.N - E.pos c) % E.N

/-- The base block of a block. -/
def blockOf (b : Nat) : List Nat := E.base.getD (b / E.N) []

/-- **The developed design.** -/
def gdd : GDD Nat where
  n := E.W + E.R * E.N
  grp := E.grp
  gsz g := if g = 0 then E.W else E.N / E.Mo ((g - 1) / E.N)
  gpt g i := if g = 0 then i else E.ptOf ((g - 1) / E.N) ((g - 1) % E.N + E.Mo ((g - 1) / E.N) * i)
  gidx c := if c < E.W then c else E.pos c / E.Mo (E.orb c)
  blk x y :=
    (E.findKey (E.key x y)).1 * E.N +
      (if x < E.W then E.tr (E.entry (E.findKey (E.key x y)).1 (E.findKey (E.key x y)).2.2) y
      else E.tr (E.entry (E.findKey (E.key x y)).1 (E.findKey (E.key x y)).2.1) x)
  sz b := (E.blockOf b).length
  pt b l := E.shift (b % E.N) ((E.blockOf b).getD l 0)
  idx b c := (E.blockOf b).idxOf (E.shift (E.N - b % E.N) c)

/-! ### Arithmetic of points -/

variable {E}

/-- What the check guarantees of the parameters. -/
structure Params (E : Dev) : Prop where
  hN : 0 < E.N
  hM : ∀ r, r < E.R → 0 < E.Mo r ∧ E.Mo r ∣ E.N

theorem orb_mk {r a : Nat} (ha : a < E.N) : E.orb (E.ptOf r a) = r := by
  unfold orb ptOf
  rw [Nat.add_sub_cancel_left, mul_add_div ha]

theorem pos_mk {r a : Nat} (ha : a < E.N) : E.pos (E.ptOf r a) = a := by
  unfold pos ptOf
  rw [Nat.add_sub_cancel_left, mul_add_mod ha]

theorem mk_ge {r a : Nat} : ¬E.ptOf r a < E.W := by
  unfold ptOf
  omega

theorem mk_lt {r a : Nat} (hr : r < E.R) (ha : a < E.N) : E.ptOf r a < E.W + E.R * E.N := by
  unfold ptOf
  have := mul_add_lt hr ha
  omega

theorem pos_lt (hp : E.Params) (c : Nat) : E.pos c < E.N := Nat.mod_lt _ hp.hN

theorem orb_lt {c : Nat} (hp : E.Params) (hc : c < E.W + E.R * E.N) (hw : ¬c < E.W) :
    E.orb c < E.R := by
  unfold orb
  exact (Nat.div_lt_iff_lt_mul hp.hN).2 (by omega)

theorem mk_orb_pos (hp : E.Params) {c : Nat} (hc : ¬c < E.W) : E.ptOf (E.orb c) (E.pos c) = c := by
  unfold ptOf orb pos
  have := Nat.div_add_mod' (c - E.W) E.N
  have := hp.hN
  omega

theorem shift_fix {t c : Nat} (hc : c < E.W) : E.shift t c = c := ite_of_pos hc

theorem shift_norm (hp : E.Params) {c : Nat} (hc : ¬c < E.W) :
    E.shift (E.N - E.pos c) c = E.ptOf (E.orb c) 0 := by
  unfold shift
  rw [ite_of_neg hc, show E.pos c + (E.N - E.pos c) = E.N by have := pos_lt hp c; omega,
    Nat.mod_self]

theorem shift_lt (hp : E.Params) {t c : Nat} (hc : c < E.W + E.R * E.N) :
    E.shift t c < E.W + E.R * E.N := by
  by_cases h : c < E.W
  · rw [shift_fix h]; exact hc
  · unfold shift
    rw [ite_of_neg h]
    exact mk_lt (orb_lt hp hc h) (Nat.mod_lt _ hp.hN)

/-- Translating back. -/
theorem shift_shift (hp : E.Params) {t c : Nat} (ht : t ≤ E.N) :
    E.shift (E.N - t) (E.shift t c) = c := by
  by_cases h : c < E.W
  · rw [shift_fix h, shift_fix h]
  · unfold shift
    rw [ite_of_neg h, ite_of_neg mk_ge, orb_mk (Nat.mod_lt _ hp.hN), pos_mk (Nat.mod_lt _ hp.hN),
      Nat.mod_add_mod, show E.pos c + t + (E.N - t) = E.pos c + E.N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (pos_lt hp c)]
    exact mk_orb_pos hp h

theorem shift_fix_iff {t c : Nat} : E.shift t c < E.W ↔ c < E.W := by
  by_cases h : c < E.W
  · rw [shift_fix h]
  · unfold shift
    rw [ite_of_neg h]
    exact ⟨fun h' => absurd h' mk_ge, fun h' => absurd h' h⟩

theorem orb_shift (hp : E.Params) {t c : Nat} (hc : ¬c < E.W) : E.orb (E.shift t c) = E.orb c := by
  unfold shift
  rw [ite_of_neg hc, orb_mk (Nat.mod_lt _ hp.hN)]

theorem pos_shift (hp : E.Params) {t c : Nat} (hc : ¬c < E.W) :
    E.pos (E.shift t c) = (E.pos c + t) % E.N := by
  unfold shift
  rw [ite_of_neg hc, pos_mk (Nat.mod_lt _ hp.hN)]

/-- `a + c ≡ b + c` cancels modulo `d`. -/
theorem mod_cancel_add {a b c d : Nat} (h : (a + c) % d = (b + c) % d) : a % d = b % d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.mod_zero] at h ⊢
    omega
  have e := Nat.add_mod_eq_add_mod_right (d - c % d) h
  have hc : c + (d - c % d) = d * (c / d + 1) := by
    have := Nat.div_add_mod' c d
    have := Nat.mod_lt c hd
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    omega
  rwa [Nat.add_assoc, Nat.add_assoc, hc, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
    at e

/-- Differences modulo `N`: `u - v ≡ u' - v'` when `u + v' ≡ u' + v`. -/
theorem diff_mod {N u v u' v' : Nat} (hv : v ≤ N) (hv' : v' ≤ N)
    (h : (u + v') % N = (u' + v) % N) : (u + N - v) % N = (u' + N - v') % N := by
  apply mod_cancel_add (c := v + v')
  rw [show u + N - v + (v + v') = u + v' + N by omega,
    show u' + N - v' + (v + v') = u' + v + N by omega, Nat.add_mod_right, Nat.add_mod_right, h]

theorem two_mul_le (a b : Nat) : 2 * a * b = a * b + a * b := by
  rw [Nat.mul_assoc 2, Nat.two_mul]

/-- **Translations keep groups apart and together.** -/
theorem grp_shift_eq_iff (hp : E.Params) {t x y : Nat} (hx : x < E.W + E.R * E.N)
    (hy : y < E.W + E.R * E.N) : E.grp (E.shift t x) = E.grp (E.shift t y) ↔ E.grp x = E.grp y := by
  unfold grp
  by_cases h1 : x < E.W <;> by_cases h2 : y < E.W
  · rw [ite_of_pos (shift_fix_iff.2 h1), ite_of_pos (shift_fix_iff.2 h2), ite_of_pos h1,
      ite_of_pos h2]
  · rw [ite_of_pos (shift_fix_iff.2 h1), ite_of_neg (mt shift_fix_iff.1 h2), ite_of_pos h1,
      ite_of_neg h2]
    omega
  · rw [ite_of_neg (mt shift_fix_iff.1 h1), ite_of_pos (shift_fix_iff.2 h2), ite_of_neg h1,
      ite_of_pos h2]
    omega
  · rw [ite_of_neg (mt shift_fix_iff.1 h1), ite_of_neg (mt shift_fix_iff.1 h2), ite_of_neg h1,
      ite_of_neg h2, orb_shift hp h1,
      orb_shift hp h2, pos_shift hp h1, pos_shift hp h2]
    have px := pos_lt hp x
    have py := pos_lt hp y
    have ox := orb_lt hp hx h1
    have oy := orb_lt hp hy h2
    constructor
    · intro h
      have e1 : E.orb x * E.N + (E.pos x + t) % E.N % E.Mo (E.orb x) =
          E.orb y * E.N + (E.pos y + t) % E.N % E.Mo (E.orb y) := by omega
      have m1 := Nat.mod_lt ((E.pos x + t) % E.N) (hp.hM _ ox).1
      have m2 := Nat.mod_lt ((E.pos y + t) % E.N) (hp.hM _ oy).1
      have l1 : E.Mo (E.orb x) ≤ E.N := Nat.le_of_dvd hp.hN (hp.hM _ ox).2
      have l2 : E.Mo (E.orb y) ≤ E.N := Nat.le_of_dvd hp.hN (hp.hM _ oy).2
      have ho : E.orb x = E.orb y := (eq_of_mul_add_eq (by omega) (by omega) e1).1
      have hm := (eq_of_mul_add_eq (by omega) (by omega) e1).2
      rw [ho] at hm ⊢
      rw [Nat.mod_mod_of_dvd _ (hp.hM _ oy).2, Nat.mod_mod_of_dvd _ (hp.hM _ oy).2] at hm
      have := mod_cancel_add hm
      omega
    · intro h
      have e1 : E.orb x * E.N + E.pos x % E.Mo (E.orb x) =
          E.orb y * E.N + E.pos y % E.Mo (E.orb y) := by omega
      have m1 := Nat.mod_lt (E.pos x) (hp.hM _ ox).1
      have m2 := Nat.mod_lt (E.pos y) (hp.hM _ oy).1
      have l1 : E.Mo (E.orb x) ≤ E.N := Nat.le_of_dvd hp.hN (hp.hM _ ox).2
      have l2 : E.Mo (E.orb y) ≤ E.N := Nat.le_of_dvd hp.hN (hp.hM _ oy).2
      have ho : E.orb x = E.orb y := (eq_of_mul_add_eq (by omega) (by omega) e1).1
      have hm := (eq_of_mul_add_eq (by omega) (by omega) e1).2
      rw [ho] at hm ⊢
      rw [Nat.mod_mod_of_dvd _ (hp.hM _ oy).2, Nat.mod_mod_of_dvd _ (hp.hM _ oy).2,
        Nat.add_mod_eq_add_mod_right t hm]

/-- **Keys do not change under translation**, for two points of different groups. -/
theorem key_shift (hp : E.Params) {t x y : Nat} (hxy : ¬(x < E.W ∧ y < E.W)) :
    E.key (E.shift t x) (E.shift t y) = E.key x y := by
  unfold key
  by_cases h1 : x < E.W
  · have h2 : ¬y < E.W := fun h => hxy ⟨h1, h⟩
    rw [ite_of_pos (shift_fix_iff.2 h1), ite_of_pos h1, shift_fix h1, orb_shift hp h2]
  · rw [ite_of_neg (mt shift_fix_iff.1 h1), ite_of_neg h1]
    by_cases h2 : y < E.W
    · rw [ite_of_pos (shift_fix_iff.2 h2), ite_of_pos h2, shift_fix h2, orb_shift hp h1]
    · rw [ite_of_neg (mt shift_fix_iff.1 h2), ite_of_neg h2, orb_shift hp h1, orb_shift hp h2,
        pos_shift hp h1, pos_shift hp h2]
      congr 2
      apply diff_mod (Nat.le_of_lt (Nat.mod_lt _ hp.hN)) (Nat.le_of_lt (pos_lt hp x))
      rw [Nat.mod_add_mod, Nat.add_mod_mod]
      congr 1
      omega

/-- **Equal keys come from translates.** Two ordered pairs of points of different groups with
the same key are translates of each other, by `tr` of their points outside the fixed points. -/
theorem translate_of_key_eq (hp : E.Params) {x y x' y' : Nat}
    (hx : x < E.W + E.R * E.N) (hy : y < E.W + E.R * E.N)
    (hx' : x' < E.W + E.R * E.N) (hy' : y' < E.W + E.R * E.N)
    (hxy : ¬(x < E.W ∧ y < E.W)) (hxy' : ¬(x' < E.W ∧ y' < E.W))
    (he : E.key x y = E.key x' y') :
    (x' < E.W ↔ x < E.W) ∧ (y' < E.W ↔ y < E.W) ∧
      (x' < E.W → x' = x ∧ y' = E.shift (E.tr y y') y) ∧
      (¬x' < E.W → x' = E.shift (E.tr x x') x ∧ y' = E.shift (E.tr x x') y) := by
  have hN := hp.hN
  have bnd1 : ∀ h s, h < E.W → s < E.R → h * E.R + s < E.W * E.R := fun h s hh hs =>
    mul_add_lt hh hs
  unfold key at he
  -- the point of an orbit as a translate
  have tr_spec : ∀ c c', ¬c < E.W → ¬c' < E.W → E.orb c = E.orb c' →
      E.shift (E.tr c c') c = c' := by
    intro c c' hc hc' ho
    unfold shift tr
    rw [ite_of_neg hc, Nat.add_mod_mod, show E.pos c + (E.pos c' + E.N - E.pos c) =
      E.pos c' + E.N by have := pos_lt hp c; omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (pos_lt hp c'), ho]
    exact mk_orb_pos hp hc'
  by_cases h1 : x < E.W
  · have h2 : ¬y < E.W := fun h => hxy ⟨h1, h⟩
    rw [ite_of_pos h1] at he
    have hs := orb_lt hp hy h2
    have hk : E.key x y < E.W * E.R := by unfold key; rw [ite_of_pos h1]; exact bnd1 _ _ h1 hs
    by_cases h1' : x' < E.W
    · have h2' : ¬y' < E.W := fun h => hxy' ⟨h1', h⟩
      rw [ite_of_pos h1'] at he
      obtain ⟨e1, e2⟩ := eq_of_mul_add_eq hs (orb_lt hp hy' h2') he
      refine ⟨iff_of_true h1' h1, iff_of_false h2' h2, fun _ => ⟨e1.symm, ?_⟩,
        fun h => absurd h1' h⟩
      exact (tr_spec y y' h2 h2' e2).symm
    · exfalso
      rw [ite_of_neg h1'] at he
      have hlt : x * E.R + E.orb y < E.W * E.R := bnd1 _ _ h1 hs
      have := two_mul_le E.W E.R
      split at he <;> omega
  · rw [ite_of_neg h1] at he
    by_cases h2 : y < E.W
    · rw [ite_of_pos h2] at he
      have hr := orb_lt hp hx h1
      have hb : y * E.R + E.orb x < E.W * E.R := bnd1 _ _ h2 hr
      by_cases h1' : x' < E.W
      · exfalso
        rw [ite_of_pos h1'] at he
        have := bnd1 _ _ h1' (orb_lt hp hy' (fun h => hxy' ⟨h1', h⟩))
        omega
      · rw [ite_of_neg h1'] at he
        by_cases h2' : y' < E.W
        · rw [ite_of_pos h2'] at he
          obtain ⟨e1, e2⟩ := eq_of_mul_add_eq (a := y) (a' := y') hr (orb_lt hp hx' h1') (by omega)
          refine ⟨iff_of_false h1' h1, iff_of_true h2' h2, fun h => absurd h h1', fun _ => ?_⟩
          exact ⟨(tr_spec x x' h1 h1' e2).symm, by rw [shift_fix h2]; exact e1.symm⟩
        · exfalso
          rw [ite_of_neg h2'] at he
          have := two_mul_le E.W E.R
          have := Nat.zero_le ((E.orb x' * E.R + E.orb y') * E.N +
            (E.pos y' + E.N - E.pos x') % E.N)
          omega
    · rw [ite_of_neg h2] at he
      have hr := orb_lt hp hx h1
      have hs := orb_lt hp hy h2
      by_cases h1' : x' < E.W
      · exfalso
        rw [ite_of_pos h1'] at he
        have := bnd1 _ _ h1' (orb_lt hp hy' (fun h => hxy' ⟨h1', h⟩))
        have := two_mul_le E.W E.R
        omega
      rw [ite_of_neg h1'] at he
      by_cases h2' : y' < E.W
      · exfalso
        rw [ite_of_pos h2'] at he
        have := bnd1 _ _ h2' (orb_lt hp hx' h1')
        have := two_mul_le E.W E.R
        omega
      rw [ite_of_neg h2'] at he
      have hr' := orb_lt hp hx' h1'
      have hs' := orb_lt hp hy' h2'
      have e0 : (E.orb x * E.R + E.orb y) * E.N + (E.pos y + E.N - E.pos x) % E.N =
          (E.orb x' * E.R + E.orb y') * E.N + (E.pos y' + E.N - E.pos x') % E.N := by omega
      obtain ⟨e1, e2⟩ := eq_of_mul_add_eq (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) e0
      obtain ⟨e3, e4⟩ := eq_of_mul_add_eq hs hs' e1
      refine ⟨iff_of_false h1' h1, iff_of_false h2' h2, fun h => absurd h h1', fun _ => ?_⟩
      refine ⟨(tr_spec x x' h1 h1' e3).symm, ?_⟩
      unfold shift tr
      rw [ite_of_neg h2, Nat.add_mod_mod, e4]
      have px := pos_lt hp x
      have py := pos_lt hp y
      have px' := pos_lt hp x'
      have py' := pos_lt hp y'
      -- `b + (a' - a) ≡ b'`
      have : (E.pos y + (E.pos x' + E.N - E.pos x)) % E.N = E.pos y' := by
        have h3 := Nat.add_mod_eq_add_mod_right (E.pos x') e2
        rw [show E.pos y + E.N - E.pos x + E.pos x' = E.pos y + (E.pos x' + E.N - E.pos x) by omega,
          show E.pos y' + E.N - E.pos x' + E.pos x' = E.pos y' + E.N by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt py'] at h3
        exact h3
      rw [this]
      exact (mk_orb_pos hp h2').symm

/-- A translation of a point outside the fixed points determines its amount. -/
theorem shift_inj (hp : E.Params) {t t' c : Nat} (hc : ¬c < E.W) (ht : t < E.N) (ht' : t' < E.N)
    (h : E.shift t c = E.shift t' c) : t = t' := by
  have := congrArg E.pos h
  rw [pos_shift hp hc, pos_shift hp hc, Nat.add_comm (E.pos c), Nat.add_comm (E.pos c)] at this
  have := mod_cancel_add this
  rwa [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at this

theorem tr_lt (hp : E.Params) (c c' : Nat) : E.tr c c' < E.N := Nat.mod_lt _ hp.hN

theorem mem_triples {i j₁ j₂ : Nat} :
    (i, j₁, j₂) ∈ E.triples ↔ i < E.base.length ∧ j₁ < (E.base.getD i []).length ∧
      j₂ < (E.base.getD i []).length ∧ j₁ ≠ j₂ := by
  unfold triples
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨i', hi', j₁', hj₁', j₂', hj₂', h⟩
    split at h
    · cases h
    · cases h
      exact ⟨hi', hj₁', hj₂', ‹_›⟩
  · rintro ⟨hi, h1, h2, h12⟩
    exact ⟨i, hi, j₁, h1, j₂, h2, by rw [ite_of_neg h12]⟩

/-- What the check certifies, unpacked. -/
structure Checked (E : Dev) : Prop where
  params : E.Params
  blocks : ∀ L ∈ E.base, L.Nodup ∧ ∀ c ∈ L, c < E.W + E.R * E.N
  cross : ∀ p ∈ E.triples, E.grp (E.entry p.1 p.2.1) ≠ E.grp (E.entry p.1 p.2.2)
  nodup : (E.triples.map E.tkey).Nodup
  cover : ∀ x y, x < E.W + E.R * E.N → y < E.W + E.R * E.N → E.grp x ≠ E.grp y →
    E.key x y ∈ E.triples.map E.tkey

theorem checked_of_check (h : E.check = true) : E.Checked := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hN, hM⟩, hb⟩, hc⟩, hk⟩ := h
  have hp : E.Params := ⟨hN, fun r hr => by
    have := allBelow_spec hM r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1, Nat.dvd_of_mod_eq_zero this.2⟩⟩
  split at hk
  · cases hk
  rename_i B hB
  obtain ⟨hnd, -, hbits⟩ := bitsOf_spec _ 0 B hB
  have mem : ∀ k, B.testBit k = true → k ∈ E.triples.map E.tkey := fun k hk' =>
    (hbits k hk').resolve_left (by simp)
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hk1, hk2⟩ := hk
  refine ⟨hp, fun L hL => ?_, fun p hp' => hc p hp', hnd, ?_⟩
  · exact hb L hL
  intro x y hx hy hxy
  -- translate the pair so that its first point outside the fixed points is the point `0`
  by_cases h1 : x < E.W
  · have h2 : ¬y < E.W := fun h => hxy (by unfold grp; rw [ite_of_pos h1, ite_of_pos h])
    have hs := orb_lt hp hy h2
    have := allBelow_spec (allBelow_spec hk1 x h1) _ hs
    simp only [Bool.and_eq_true] at this
    have e := key_shift hp (t := E.N - E.pos y) (x := x) (y := y) (fun h => h2 h.2)
    rw [shift_fix h1, shift_norm hp h2] at e
    rw [← e]
    exact mem _ this.1
  · have hr := orb_lt hp hx h1
    by_cases h2 : y < E.W
    · have := allBelow_spec (allBelow_spec hk1 y h2) _ hr
      simp only [Bool.and_eq_true] at this
      have e := key_shift hp (t := E.N - E.pos x) (x := x) (y := y) (fun h => h1 h.1)
      rw [shift_fix h2, shift_norm hp h1] at e
      rw [← e]
      exact mem _ this.2
    · have hs := orb_lt hp hy h2
      have hd := Nat.mod_lt (E.pos y + (E.N - E.pos x)) hp.hN
      have := allBelow_spec (allBelow_spec (allBelow_spec hk2 _ hr) _ hs) _ hd
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      have ex : E.shift (E.N - E.pos x) x = E.ptOf (E.orb x) 0 := shift_norm hp h1
      have ey : E.shift (E.N - E.pos x) y =
          E.ptOf (E.orb y) ((E.pos y + (E.N - E.pos x)) % E.N) := ite_of_neg h2
      have e := key_shift hp (t := E.N - E.pos x) (x := x) (y := y) (fun h => h1 h.1)
      rw [ex, ey] at e
      rw [← e]
      refine mem _ (this.resolve_left fun h => hxy ?_)
      rw [← ex, ← ey] at h
      exact (grp_shift_eq_iff hp hx hy).1 h

theorem getD_mem_base {i : Nat} (hi : i < E.base.length) : E.base.getD i [] ∈ E.base := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

variable (E) in
/-- The block through two points of different groups, unpacked. -/
theorem blk_spec (hc : E.Checked) {x y : Nat} (h : E.gdd.Cross x y) :
    ∃ i j₁ j₂ t, (i, j₁, j₂) ∈ E.triples ∧ t < E.N ∧ E.gdd.blk x y = i * E.N + t ∧
      x = E.shift t (E.entry i j₁) ∧ y = E.shift t (E.entry i j₂) := by
  obtain ⟨hx, hy, hxy⟩ := h
  have hp := hc.params
  have hk := hc.cover x y hx hy hxy
  obtain ⟨p, hpm, hpk⟩ := List.mem_map.1 hk
  have hf : (E.triples.find? fun p => E.tkey p == E.key x y).isSome := by
    rw [List.find?_isSome]
    exact ⟨p, hpm, by simp [hpk]⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hf
  have hqm := List.mem_of_find?_eq_some hq
  have hqk : E.tkey q = E.key x y := by simpa using List.find?_some hq
  have hfk : E.findKey (E.key x y) = q := by unfold findKey; rw [hq]; rfl
  obtain ⟨i, j₁, j₂⟩ := q
  have hm := mem_triples.1 hqm
  have hL := hc.blocks _ (getD_mem_base hm.1)
  have he1 : E.entry i j₁ < E.W + E.R * E.N := hL.2 _ (getD_mem hm.2.1)
  have he2 : E.entry i j₂ < E.W + E.R * E.N := hL.2 _ (getD_mem hm.2.2.1)
  have hcr : E.grp (E.entry i j₁) ≠ E.grp (E.entry i j₂) := hc.cross _ hqm
  have nf : ∀ {u v : Nat}, E.grp u ≠ E.grp v → ¬(u < E.W ∧ v < E.W) := fun h h' => h (by
    unfold grp; rw [ite_of_pos h'.1, ite_of_pos h'.2])
  obtain ⟨i1, i2, f1, f2⟩ := translate_of_key_eq hp he1 he2 hx hy (nf hcr) (nf hxy) hqk
  refine ⟨i, j₁, j₂, if x < E.W then E.tr (E.entry i j₂) y else E.tr (E.entry i j₁) x, hqm, ?_,
    ?_, ?_, ?_⟩
  · split <;> exact tr_lt hp _ _
  · show (E.findKey (E.key x y)).1 * E.N + _ = _
    rw [hfk]
  · by_cases h1 : x < E.W
    · rw [ite_of_pos h1, (f1 h1).1, shift_fix (i1.1 h1)]
    · rw [ite_of_neg h1]
      exact (f2 h1).1
  · by_cases h1 : x < E.W
    · rw [ite_of_pos h1]
      exact (f1 h1).2
    · rw [ite_of_neg h1]
      exact (f2 h1).2

/-- **A developed design passing the check is a group-divisible design.** -/
theorem gdd_valid (hc : E.Checked) : E.gdd.Valid := by
  have hp := hc.params
  have hN := hp.hN
  -- the base block of a block `i N + t`
  have bo : ∀ i t, t < E.N → E.blockOf (i * E.N + t) = E.base.getD i [] ∧
      (i * E.N + t) % E.N = t := fun i t ht => by
    unfold blockOf
    rw [mul_add_div ht, mul_add_mod ht]
    exact ⟨rfl, rfl⟩
  have memb : ∀ i, i < E.base.length → E.base.getD i [] ∈ E.base := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have nf : ∀ {u v : Nat}, E.grp u ≠ E.grp v → ¬(u < E.W ∧ v < E.W) := fun h h' => h (by
    unfold grp; rw [ite_of_pos h'.1, ite_of_pos h'.2])
  -- the index of a translated entry
  have idxE : ∀ i j t, i < E.base.length → j < (E.base.getD i []).length → t < E.N →
      E.gdd.idx (i * E.N + t) (E.shift t (E.entry i j)) = j := by
    intro i j t hi hj ht
    show (E.blockOf (i * E.N + t)).idxOf (E.shift (E.N - (i * E.N + t) % E.N)
      (E.shift t (E.entry i j))) = j
    rw [(bo i t ht).1, (bo i t ht).2, shift_shift hp (Nat.le_of_lt ht)]
    exact idxOf_getD (hc.blocks _ (memb i hi)).1 hj
  have ptE : ∀ i j t, t < E.N → E.gdd.pt (i * E.N + t) j = E.shift t (E.entry i j) := by
    intro i j t ht
    show E.shift ((i * E.N + t) % E.N) ((E.blockOf (i * E.N + t)).getD j 0) = _
    rw [(bo i t ht).1, (bo i t ht).2]
    rfl
  have szE : ∀ i t, t < E.N → E.gdd.sz (i * E.N + t) = (E.base.getD i []).length := by
    intro i t ht
    show (E.blockOf (i * E.N + t)).length = _
    rw [(bo i t ht).1]
  -- the groups
  have gM : ∀ c, c < E.W + E.R * E.N → ¬c < E.W →
      0 < E.Mo (E.orb c) ∧ E.Mo (E.orb c) ∣ E.N ∧ E.Mo (E.orb c) ≤ E.N := fun c hc' hw =>
    ⟨(hp.hM _ (orb_lt hp hc' hw)).1, (hp.hM _ (orb_lt hp hc' hw)).2,
      Nat.le_of_dvd hN (hp.hM _ (orb_lt hp hc' hw)).2⟩
  have grpO : ∀ c, c < E.W + E.R * E.N → ¬c < E.W →
      E.grp c ≠ 0 ∧ (E.grp c - 1) / E.N = E.orb c ∧
        (E.grp c - 1) % E.N = E.pos c % E.Mo (E.orb c) :=
    fun c hc' hw => by
      obtain ⟨m0, -, mN⟩ := gM c hc' hw
      have := Nat.mod_lt (E.pos c) m0
      unfold grp
      rw [ite_of_neg hw, Nat.add_sub_cancel_left, mul_add_div (by omega), mul_add_mod (by omega)]
      exact ⟨by omega, rfl, rfl⟩
  refine
    { gidx_lt := ?_, gpt_gidx := ?_, gpt_lt := ?_, grp_gpt := ?_, gidx_gpt := ?_,
      idx_lt := ?_, pt_idx := ?_, idx_lt' := ?_, pt_idx' := ?_, pt_lt := ?_, idx_pt := ?_,
      cross_pt := ?_, blk_pt := ?_ }
  · intro x hx
    change (if x < E.W then x else E.pos x / E.Mo (E.orb x)) <
      (if E.grp x = 0 then E.W else E.N / E.Mo ((E.grp x - 1) / E.N))
    by_cases hw : x < E.W
    · rw [ite_of_pos hw, ite_of_pos (by unfold grp; rw [ite_of_pos hw])]
      exact hw
    · obtain ⟨g0, g1, -⟩ := grpO x hx hw
      obtain ⟨m0, md, -⟩ := gM x hx hw
      rw [ite_of_neg hw, ite_of_neg g0, g1]
      exact Nat.div_lt_div_of_lt_of_dvd md (pos_lt hp x)
  · intro x hx
    change (if E.grp x = 0 then (if x < E.W then x else E.pos x / E.Mo (E.orb x)) else
      E.ptOf ((E.grp x - 1) / E.N) ((E.grp x - 1) % E.N +
        E.Mo ((E.grp x - 1) / E.N) * (if x < E.W then x else E.pos x / E.Mo (E.orb x)))) = x
    by_cases hw : x < E.W
    · rw [ite_of_pos (by unfold grp; rw [ite_of_pos hw]), ite_of_pos hw]
    · obtain ⟨g0, g1, g2⟩ := grpO x hx hw
      rw [ite_of_neg g0, ite_of_neg hw, g1, g2, Nat.mod_add_div]
      exact mk_orb_pos hp hw
  · intro x i hx hi
    change i < (if E.grp x = 0 then E.W else E.N / E.Mo ((E.grp x - 1) / E.N)) at hi
    change (if E.grp x = 0 then i else E.ptOf ((E.grp x - 1) / E.N) ((E.grp x - 1) % E.N +
      E.Mo ((E.grp x - 1) / E.N) * i)) < E.W + E.R * E.N
    by_cases hw : x < E.W
    · have g0 : E.grp x = 0 := by unfold grp; rw [ite_of_pos hw]
      rw [ite_of_pos g0] at hi ⊢
      omega
    · obtain ⟨g0, g1, g2⟩ := grpO x hx hw
      obtain ⟨m0, md, -⟩ := gM x hx hw
      rw [ite_of_neg g0, g1] at hi
      rw [ite_of_neg g0, g1, g2]
      refine mk_lt (orb_lt hp hx hw) ?_
      obtain ⟨k, hk⟩ := md
      have hk' : E.N / E.Mo (E.orb x) = k := by rw [hk, Nat.mul_div_cancel_left _ m0]
      rw [hk'] at hi
      have := Nat.mod_lt (E.pos x) m0
      have : E.Mo (E.orb x) * i + E.Mo (E.orb x) ≤ E.Mo (E.orb x) * k := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
      omega
  · intro x i hx hi
    change i < (if E.grp x = 0 then E.W else E.N / E.Mo ((E.grp x - 1) / E.N)) at hi
    change E.grp (if E.grp x = 0 then i else E.ptOf ((E.grp x - 1) / E.N) ((E.grp x - 1) % E.N +
      E.Mo ((E.grp x - 1) / E.N) * i)) = E.grp x
    by_cases hw : x < E.W
    · have g0 : E.grp x = 0 := by unfold grp; rw [ite_of_pos hw]
      rw [ite_of_pos g0] at hi ⊢
      rw [g0]
      unfold grp
      rw [ite_of_pos (by omega)]
    · obtain ⟨g0, g1, g2⟩ := grpO x hx hw
      obtain ⟨m0, md, -⟩ := gM x hx hw
      rw [ite_of_neg g0, g1] at hi
      rw [ite_of_neg g0, g1, g2]
      obtain ⟨k, hk⟩ := md
      have hk' : E.N / E.Mo (E.orb x) = k := by rw [hk, Nat.mul_div_cancel_left _ m0]
      rw [hk'] at hi
      have hm := Nat.mod_lt (E.pos x) m0
      have hlt : E.pos x % E.Mo (E.orb x) + E.Mo (E.orb x) * i < E.N := by
        have : E.Mo (E.orb x) * i + E.Mo (E.orb x) ≤ E.Mo (E.orb x) * k := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
        omega
      conv => rhs; unfold grp
      unfold grp
      rw [ite_of_neg mk_ge, ite_of_neg hw, orb_mk hlt, pos_mk hlt, Nat.add_mul_mod_self_left,
        Nat.mod_mod]
  · intro x i hx hi
    change i < (if E.grp x = 0 then E.W else E.N / E.Mo ((E.grp x - 1) / E.N)) at hi
    change (if (if E.grp x = 0 then i else E.ptOf ((E.grp x - 1) / E.N) ((E.grp x - 1) % E.N +
      E.Mo ((E.grp x - 1) / E.N) * i)) < E.W then
        (if E.grp x = 0 then i else E.ptOf ((E.grp x - 1) / E.N) ((E.grp x - 1) % E.N +
          E.Mo ((E.grp x - 1) / E.N) * i)) else
        E.pos (if E.grp x = 0 then i else E.ptOf ((E.grp x - 1) / E.N) ((E.grp x - 1) % E.N +
          E.Mo ((E.grp x - 1) / E.N) * i)) /
        E.Mo (E.orb (if E.grp x = 0 then i else E.ptOf ((E.grp x - 1) / E.N)
          ((E.grp x - 1) % E.N + E.Mo ((E.grp x - 1) / E.N) * i)))) = i
    by_cases hw : x < E.W
    · have g0 : E.grp x = 0 := by unfold grp; rw [ite_of_pos hw]
      rw [ite_of_pos g0] at hi ⊢
      rw [ite_of_pos hi]
    · obtain ⟨g0, g1, g2⟩ := grpO x hx hw
      obtain ⟨m0, md, -⟩ := gM x hx hw
      rw [ite_of_neg g0, g1] at hi
      rw [ite_of_neg g0, g1, g2]
      obtain ⟨k, hk⟩ := md
      have hk' : E.N / E.Mo (E.orb x) = k := by rw [hk, Nat.mul_div_cancel_left _ m0]
      rw [hk'] at hi
      have hm := Nat.mod_lt (E.pos x) m0
      have hlt : E.pos x % E.Mo (E.orb x) + E.Mo (E.orb x) * i < E.N := by
        have : E.Mo (E.orb x) * i + E.Mo (E.orb x) ≤ E.Mo (E.orb x) * k := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
        omega
      rw [ite_of_neg mk_ge, orb_mk hlt, pos_mk hlt, Nat.add_mul_div_left _ _ m0,
        Nat.div_eq_of_lt hm, Nat.zero_add]
  -- the blocks
  · intro x y h
    obtain ⟨i, j₁, j₂, t, hm, ht, hb, ex, -⟩ := blk_spec E hc h
    have hm' := mem_triples.1 hm
    rw [hb, ex, idxE i j₁ t hm'.1 hm'.2.1 ht, szE i t ht]
    exact hm'.2.1
  · intro x y h
    obtain ⟨i, j₁, j₂, t, hm, ht, hb, ex, -⟩ := blk_spec E hc h
    have hm' := mem_triples.1 hm
    rw [hb, ex, idxE i j₁ t hm'.1 hm'.2.1 ht, ptE i j₁ t ht]
  · intro x y h
    obtain ⟨i, j₁, j₂, t, hm, ht, hb, -, ey⟩ := blk_spec E hc h
    have hm' := mem_triples.1 hm
    rw [hb, ey, idxE i j₂ t hm'.1 hm'.2.2.1 ht, szE i t ht]
    exact hm'.2.2.1
  · intro x y h
    obtain ⟨i, j₁, j₂, t, hm, ht, hb, -, ey⟩ := blk_spec E hc h
    have hm' := mem_triples.1 hm
    rw [hb, ey, idxE i j₂ t hm'.1 hm'.2.2.1 ht, ptE i j₂ t ht]
  · intro x y l h hl
    obtain ⟨i, j₁, j₂, t, hm, ht, hb, -, -⟩ := blk_spec E hc h
    have hm' := mem_triples.1 hm
    rw [hb, szE i t ht] at hl
    rw [hb, ptE i l t ht]
    exact shift_lt hp ((hc.blocks _ (memb i hm'.1)).2 _ (getD_mem hl))
  · intro x y l h hl
    obtain ⟨i, j₁, j₂, t, hm, ht, hb, -, -⟩ := blk_spec E hc h
    have hm' := mem_triples.1 hm
    rw [hb, szE i t ht] at hl
    rw [hb, ptE i l t ht, idxE i l t hm'.1 hl ht]
  · intro x y l₁ l₂ h hl₁ hl₂ hne
    obtain ⟨i, j₁, j₂, t, hm, ht, hb, -, -⟩ := blk_spec E hc h
    have hm' := mem_triples.1 hm
    rw [hb, szE i t ht] at hl₁ hl₂
    rw [hb, ptE i l₁ t ht, ptE i l₂ t ht]
    show E.grp _ ≠ E.grp _
    have hL := (hc.blocks _ (memb i hm'.1)).2
    have v1 : E.entry i l₁ < E.W + E.R * E.N := hL _ (getD_mem hl₁)
    have v2 : E.entry i l₂ < E.W + E.R * E.N := hL _ (getD_mem hl₂)
    rw [Ne, grp_shift_eq_iff hp v1 v2]
    exact hc.cross (i, l₁, l₂) (mem_triples.2 ⟨hm'.1, hl₁, hl₂, hne⟩)
  · intro x y l₁ l₂ h hl₁ hl₂ hne
    obtain ⟨i, j₁, j₂, t, hm, ht, hb, -, -⟩ := blk_spec E hc h
    have hm' := mem_triples.1 hm
    rw [hb, szE i t ht] at hl₁ hl₂
    rw [hb, ptE i l₁ t ht, ptE i l₂ t ht]
    have hL := (hc.blocks _ (memb i hm'.1)).2
    have v1 : E.entry i l₁ < E.W + E.R * E.N := hL _ (getD_mem hl₁)
    have v2 : E.entry i l₂ < E.W + E.R * E.N := hL _ (getD_mem hl₂)
    have hmem := mem_triples.2 ⟨hm'.1, hl₁, hl₂, hne⟩
    have hcr := hc.cross _ hmem
    have hcr' : E.gdd.Cross (E.shift t (E.entry i l₁)) (E.shift t (E.entry i l₂)) :=
      ⟨shift_lt hp v1, shift_lt hp v2, fun e => hcr ((grp_shift_eq_iff hp v1 v2).1 e)⟩
    obtain ⟨i', k₁, k₂, t', hm₂, ht', hb', ex', ey'⟩ := blk_spec E hc hcr'
    have hm₂' := mem_triples.1 hm₂
    have hcr₂ := hc.cross _ hm₂
    -- the two places have the same key, so they are the same place
    have hk : E.tkey (i', k₁, k₂) = E.tkey (i, l₁, l₂) := by
      show E.key (E.entry i' k₁) (E.entry i' k₂) = E.key (E.entry i l₁) (E.entry i l₂)
      rw [← key_shift hp (t := t') (nf hcr₂), ← ex', ← ey', key_shift hp (nf hcr)]
    have heq := inj_of_nodup_map hc.nodup hm₂ hmem hk
    simp only [Prod.mk.injEq] at heq
    obtain ⟨e1, e2, e3⟩ := heq
    rw [e1, e2] at ex'
    rw [e1, e3] at ey'
    rw [hb', e1]
    congr 1
    by_cases h1 : E.entry i l₁ < E.W
    · have h2 : ¬E.entry i l₂ < E.W := fun h' => nf hcr ⟨h1, h'⟩
      exact shift_inj hp h2 ht' ht ey'.symm
    · exact shift_inj hp h1 ht' ht ex'.symm

end Dev

/-! ## Inflating a design by a constant weight

Wilson's fundamental construction with a constant weight `w` (`Spectrum677.GDD.inflate`): every
point `p` of a design `D` becomes the `w` points `p w, …, p w + w - 1`, and every block `b` of `k`
points is replaced by the blocks of a design `F k` on `k w` points whose groups are the runs
`i w, …, i w + w - 1` of `w` points, the `i`-th run standing for the `i`-th point of `b`. The
result is a design whose groups are the inflated groups of `D`
(`Spectrum677.GDD.inflate_valid`). -/

namespace GDD

variable {A B : Type}

/-- **The inflation of `D` by the weight `w`**, with the design `F k` on the blocks of `k`
points. A block is a block of `D` and a block of `F` on it. -/
def inflate (D : GDD A) (w : Nat) (F : Nat → GDD B) : GDD (A × B) where
  n := D.n * w
  grp x := D.grp (x / w)
  gsz g := D.gsz g * w
  gpt g i := D.gpt g (i / w) * w + i % w
  gidx x := D.gidx (x / w) * w + x % w
  blk x y := (D.blk (x / w) (y / w), (F (D.sz (D.blk (x / w) (y / w)))).blk
    (D.idx (D.blk (x / w) (y / w)) (x / w) * w + x % w)
    (D.idx (D.blk (x / w) (y / w)) (y / w) * w + y % w))
  sz bb := (F (D.sz bb.1)).sz bb.2
  pt bb l := D.pt bb.1 ((F (D.sz bb.1)).pt bb.2 l / w) * w + (F (D.sz bb.1)).pt bb.2 l % w
  idx bb x := (F (D.sz bb.1)).idx bb.2 (D.idx bb.1 (x / w) * w + x % w)

/-- What the inflation needs of the designs on the blocks: on a block of `k` points, a design on
`k w` points whose groups are the runs of `w` points. -/
def BlockDesigns (D : GDD A) (w : Nat) (F : Nat → GDD B) : Prop :=
  ∀ x y, D.Cross x y → (F (D.sz (D.blk x y))).Valid ∧
    (F (D.sz (D.blk x y))).n = D.sz (D.blk x y) * w ∧
    ∀ e e', e < D.sz (D.blk x y) * w → e' < D.sz (D.blk x y) * w →
      ((F (D.sz (D.blk x y))).grp e = (F (D.sz (D.blk x y))).grp e' ↔ e / w = e' / w)

section
variable {D : GDD A} {w : Nat} {F : Nat → GDD B}
theorem inflate_grp {x : Nat} : (D.inflate w F).grp x = D.grp (x / w) := rfl
theorem inflate_blk {x y : Nat} : (D.inflate w F).blk x y = (D.blk (x / w) (y / w),
    (F (D.sz (D.blk (x / w) (y / w)))).blk (D.idx (D.blk (x / w) (y / w)) (x / w) * w + x % w)
      (D.idx (D.blk (x / w) (y / w)) (y / w) * w + y % w)) := rfl
theorem inflate_sz {bb : A × B} : (D.inflate w F).sz bb = (F (D.sz bb.1)).sz bb.2 := rfl
theorem inflate_pt {bb : A × B} {l : Nat} : (D.inflate w F).pt bb l =
    D.pt bb.1 ((F (D.sz bb.1)).pt bb.2 l / w) * w + (F (D.sz bb.1)).pt bb.2 l % w := rfl
theorem inflate_idx {bb : A × B} {x : Nat} : (D.inflate w F).idx bb x =
    (F (D.sz bb.1)).idx bb.2 (D.idx bb.1 (x / w) * w + x % w) := rfl
end

/-- **The inflation is a design.** -/
theorem inflate_valid {D : GDD A} {w : Nat} {F : Nat → GDD B} (hD : D.Valid) (hw : 0 < w)
    (hF : BlockDesigns D w F) : (D.inflate w F).Valid := by
  have dv : ∀ {x : Nat}, x < D.n * w → x / w < D.n := fun h => (Nat.div_lt_iff_lt_mul hw).2 h
  have md : ∀ {x : Nat}, x % w < w := fun {x} => Nat.mod_lt x hw
  -- a cross pair of the inflation, read in `D` and in the design on its block
  have cross : ∀ {x y : Nat}, (D.inflate w F).Cross x y →
      D.Cross (x / w) (y / w) ∧
        (F (D.sz (D.blk (x / w) (y / w)))).Cross
          (D.idx (D.blk (x / w) (y / w)) (x / w) * w + x % w)
          (D.idx (D.blk (x / w) (y / w)) (y / w) * w + y % w) := by
    intro x y h
    obtain ⟨hx, hy, hg⟩ := h
    have hc : D.Cross (x / w) (y / w) := ⟨dv hx, dv hy, hg⟩
    obtain ⟨fv, fn, fg⟩ := hF _ _ hc
    have l1 := hD.idx_lt _ _ hc
    have l2 := hD.idx_lt' _ _ hc
    refine ⟨hc, ?_, ?_, ?_⟩
    · rw [fn]; exact mul_add_lt l1 md
    · rw [fn]; exact mul_add_lt l2 md
    · rw [Ne, fg _ _ (mul_add_lt l1 md) (mul_add_lt l2 md), mul_add_div md, mul_add_div md]
      intro e
      apply hg
      rw [inflate_grp, inflate_grp]
      have := congrArg (D.pt (D.blk (x / w) (y / w))) e
      rw [hD.pt_idx _ _ hc, hD.pt_idx' _ _ hc] at this
      rw [this]
  refine
    { gidx_lt := ?_, gpt_gidx := ?_, gpt_lt := ?_, grp_gpt := ?_, gidx_gpt := ?_,
      idx_lt := ?_, pt_idx := ?_, idx_lt' := ?_, pt_idx' := ?_, pt_lt := ?_, idx_pt := ?_,
      cross_pt := ?_, blk_pt := ?_ }
  · intro x hx
    exact mul_add_lt (hD.gidx_lt _ (dv hx)) md
  · intro x hx
    show D.gpt (D.grp (x / w)) ((D.gidx (x / w) * w + x % w) / w) * w +
      (D.gidx (x / w) * w + x % w) % w = x
    rw [mul_add_div md, mul_add_mod md, hD.gpt_gidx _ (dv hx)]
    exact Nat.div_add_mod' x w
  · intro x i hx hi
    have hi' : i / w < D.gsz (D.grp (x / w)) := (Nat.div_lt_iff_lt_mul hw).2 hi
    exact mul_add_lt (hD.gpt_lt _ _ (dv hx) hi') md
  · intro x i hx hi
    have hi' : i / w < D.gsz (D.grp (x / w)) := (Nat.div_lt_iff_lt_mul hw).2 hi
    show D.grp ((D.gpt (D.grp (x / w)) (i / w) * w + i % w) / w) = D.grp (x / w)
    rw [mul_add_div md, hD.grp_gpt _ _ (dv hx) hi']
  · intro x i hx hi
    have hi' : i / w < D.gsz (D.grp (x / w)) := (Nat.div_lt_iff_lt_mul hw).2 hi
    show D.gidx ((D.gpt (D.grp (x / w)) (i / w) * w + i % w) / w) * w +
      (D.gpt (D.grp (x / w)) (i / w) * w + i % w) % w = i
    rw [mul_add_div md, mul_add_mod md, hD.gidx_gpt _ _ (dv hx) hi']
    exact Nat.div_add_mod' i w
  · intro x y h
    obtain ⟨hc, hc'⟩ := cross h
    simp only [inflate_blk, inflate_sz, inflate_idx]
    exact (hF _ _ hc).1.idx_lt _ _ hc'
  · intro x y h
    obtain ⟨hc, hc'⟩ := cross h
    simp only [inflate_blk, inflate_pt, inflate_idx]
    rw [(hF _ _ hc).1.pt_idx _ _ hc', mul_add_div md, mul_add_mod md, hD.pt_idx _ _ hc]
    exact Nat.div_add_mod' x w
  · intro x y h
    obtain ⟨hc, hc'⟩ := cross h
    simp only [inflate_blk, inflate_sz, inflate_idx]
    exact (hF _ _ hc).1.idx_lt' _ _ hc'
  · intro x y h
    obtain ⟨hc, hc'⟩ := cross h
    simp only [inflate_blk, inflate_pt, inflate_idx]
    rw [(hF _ _ hc).1.pt_idx' _ _ hc', mul_add_div md, mul_add_mod md, hD.pt_idx' _ _ hc]
    exact Nat.div_add_mod' y w
  · intro x y l h hl
    obtain ⟨hc, hc'⟩ := cross h
    simp only [inflate_blk, inflate_sz, inflate_pt] at hl ⊢
    obtain ⟨fv, fn, -⟩ := hF _ _ hc
    have he := fv.pt_lt _ _ l hc' hl
    rw [fn] at he
    have := hD.pt_lt _ _ _ hc ((Nat.div_lt_iff_lt_mul hw).2 he)
    exact mul_add_lt this md
  · intro x y l h hl
    obtain ⟨hc, hc'⟩ := cross h
    simp only [inflate_blk, inflate_sz, inflate_pt, inflate_idx] at hl ⊢
    obtain ⟨fv, fn, -⟩ := hF _ _ hc
    have he := fv.pt_lt _ _ l hc' hl
    rw [fn] at he
    have hj := (Nat.div_lt_iff_lt_mul hw).2 he
    rw [mul_add_div md, mul_add_mod md, hD.idx_pt _ _ _ hc hj, Nat.div_add_mod']
    exact fv.idx_pt _ _ l hc' hl
  · intro x y l₁ l₂ h hl₁ hl₂ hne
    obtain ⟨hc, hc'⟩ := cross h
    simp only [inflate_blk, inflate_sz, inflate_pt] at hl₁ hl₂ ⊢
    obtain ⟨fv, fn, fg⟩ := hF _ _ hc
    have he₁ := fv.pt_lt _ _ l₁ hc' hl₁
    have he₂ := fv.pt_lt _ _ l₂ hc' hl₂
    rw [fn] at he₁ he₂
    have hj₁ := (Nat.div_lt_iff_lt_mul hw).2 he₁
    have hj₂ := (Nat.div_lt_iff_lt_mul hw).2 he₂
    have hg := fv.cross_pt _ _ _ _ hc' hl₁ hl₂ hne
    rw [Ne, fg _ _ he₁ he₂] at hg
    simp only [inflate_grp]
    rw [mul_add_div md, mul_add_div md]
    exact hD.cross_pt _ _ _ _ hc hj₁ hj₂ hg
  · intro x y l₁ l₂ h hl₁ hl₂ hne
    obtain ⟨hc, hc'⟩ := cross h
    simp only [inflate_blk, inflate_sz, inflate_pt] at hl₁ hl₂ ⊢
    obtain ⟨fv, fn, fg⟩ := hF _ _ hc
    have he₁ := fv.pt_lt _ _ l₁ hc' hl₁
    have he₂ := fv.pt_lt _ _ l₂ hc' hl₂
    rw [fn] at he₁ he₂
    have hj₁ := (Nat.div_lt_iff_lt_mul hw).2 he₁
    have hj₂ := (Nat.div_lt_iff_lt_mul hw).2 he₂
    have hg := fv.cross_pt _ _ _ _ hc' hl₁ hl₂ hne
    rw [Ne, fg _ _ he₁ he₂] at hg
    have hb := hD.blk_pt _ _ _ _ hc hj₁ hj₂ hg
    simp only [mul_add_div md, mul_add_mod md]
    rw [hb, hD.idx_pt _ _ _ hc hj₁, hD.idx_pt _ _ _ hc hj₂, Nat.div_add_mod', Nat.div_add_mod',
      fv.blk_pt _ _ _ _ hc' hl₁ hl₂ hne]

/-- The inflation has `D.n * w` points. -/
theorem inflate_n {D : GDD A} {w : Nat} {F : Nat → GDD B} : (D.inflate w F).n = D.n * w := rfl

end GDD

/-! ## The constructions

Each construction of the certificate glues models along one of the designs above
(`Spectrum677.GDD.isModel_glue`). -/

/-- An operation agreeing with a model is a model. -/
theorem IsModel.congr {n : Nat} {f g : Nat → Nat → Nat} (h : IsModel n f)
    (he : ∀ a b, a < n → b < n → g a b = f a b) : IsModel n g := by
  refine ⟨fun a b ha hb => by rw [he a b ha hb]; exact h.lt a b ha hb, fun a b ha hb => ?_⟩
  have l1 := h.lt _ _ hb ha
  have l2 := h.lt _ _ l1 hb
  have l3 := h.lt _ _ ha l2
  rw [he _ _ hb ha, he _ _ l1 hb, he _ _ ha l2, he _ _ hb l3]
  exact h.eq a b ha hb

/-- Every operation is a model on no points. -/
theorem isModel_zero (op : Nat → Nat → Nat) : IsModel 0 op :=
  ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- An operation with `0` idempotent is a model on one point. -/
theorem isModel_one {op : Nat → Nat → Nat} (h : op 0 0 = 0) : IsModel 1 op := by
  refine ⟨fun x y hx hy => ?_, fun x y hx hy => ?_⟩
  · rw [show x = 0 by omega, show y = 0 by omega, h]; omega
  · rw [show x = 0 by omega, show y = 0 by omega, h, h, h, h]

/-- The trivial model on one point. -/
def triv : Nat → Nat → Nat := fun _ _ => 0

theorem isIdemModel_triv : IsIdemModel 1 triv :=
  ⟨isModel_one rfl, fun x hx => by show 0 = x; omega⟩

namespace GDD

variable {B : Type} {D : GDD B}

/-- **The glued model is pointed** when a new point or a point of a group is idempotent in its
model. -/
theorem hasPtModel_glue {m : Nat} {emod : Nat → Nat → Nat} {gmod bmod : Nat → Nat → Nat → Nat}
    (hok : D.GlueOK m emod gmod bmod)
    (hpt : m + D.n = 0 ∨ (∃ e, e < m ∧ emod e e = e) ∨
      ∃ x, x < D.n ∧ ∃ i, i < m + D.gsz (D.grp x) ∧ gmod (D.grp x) i i = i) :
    HasPtModel (m + D.n) := by
  refine ⟨_, isModel_glue hok, ?_⟩
  rcases hpt with h | ⟨e, he, hee⟩ | ⟨x, hx, i, hi, hii⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, by omega, glue_idem_e he hee⟩
  · exact Or.inr ⟨_, (gemb_spec hok.valid hx hi).1, glue_idem_g hok hx hi hii⟩

end GDD

/-! ### Truncations with lower ends `0` -/

/-- The truncation of a `TD(K + 3, q)` keeping the first `a`, `b` and `c` points of the groups
`0`, `1` and `2`. -/
def cut3 {K q : Nat} (D : TD (K + 3) q) (a b c : Nat) : Cut K q :=
  ⟨D, fun _ => 0, fun j => if j = 0 then a else if j = 1 then b else c⟩

namespace Cut

variable {K q : Nat}

theorem cut3_valid (D : TD (K + 3) q) {a b c : Nat} (ha : a ≤ q) (hb : b ≤ q) (hc : c ≤ q) :
    (cut3 D a b c).Valid := by
  refine ⟨fun _ _ => Nat.zero_le _, fun j _ => ?_⟩
  show (if j = 0 then a else if j = 1 then b else c) ≤ q
  split
  · exact ha
  · split
    · exact hb
    · exact hc

theorem cut3_S (D : TD (K + 3) q) (a b c : Nat) : (cut3 D a b c).S = a + b + c := by
  show (a - 0) + (b - 0) + (c - 0) = a + b + c
  omega

/-- The sizes of the groups of a truncation `cut3`. -/
theorem cut3_gsz (D : TD (K + 3) q) (a b c g : Nat) :
    (cut3 D a b c).ghi g - (cut3 D a b c).glo g =
      if g = 0 then a else if g = 1 then b else if g = 2 then c else q := by
  unfold ghi glo
  by_cases h3 : g < 3
  · rw [ite_of_pos h3, ite_of_pos h3]
    show (if g = 0 then a else if g = 1 then b else c) - 0 = _
    rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl <;> simp
  · rw [ite_of_neg h3, ite_of_neg h3, Nat.sub_zero, ite_of_neg (by omega), ite_of_neg (by omega),
      ite_of_neg (by omega)]

/-- Whether a line of `cut3` keeps its point in the cut group `j`. -/
theorem cut3_keeps (D : TD (K + 3) q) (a b c : Nat) (L : D.Line) :
    (cut3 D a b c).keeps L 0 = decide (D.pt L 0 < a) ∧
      (cut3 D a b c).keeps L 1 = decide (D.pt L 1 < b) ∧
      (cut3 D a b c).keeps L 2 = decide (D.pt L 2 < c) := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold keeps <;> simp [cut3]

/-- The kept points of a line of `cut3` number between `K` and `K + 3`; between `K` and `K + 2`
when `c = 0`, and between `K + 1` and `K + 3` when `c = q`. -/
theorem cut3_bsize (D : TD (K + 3) q) (a b c : Nat) (L : D.Line) :
    K ≤ (cut3 D a b c).bsize L ∧ (cut3 D a b c).bsize L ≤ K + 3 ∧
      (c = 0 → (cut3 D a b c).bsize L ≤ K + 2) ∧ (c = q → K + 1 ≤ (cut3 D a b c).bsize L) := by
  obtain ⟨-, -, k2⟩ := cut3_keeps D a b c L
  have h3 := nopt_le (T := cut3 D a b c) L
  unfold bsize
  refine ⟨by omega, by omega, fun hc => ?_, fun hc => ?_⟩
  · have : (cut3 D a b c).keeps L 2 = false := by rw [k2, hc]; simp
    unfold nopt
    rw [this]
    split <;> split <;> simp <;> omega
  · have : (cut3 D a b c).keeps L 2 = true := by
      rw [k2, hc]; simpa using D.pt_lt L 2 (by omega)
    unfold nopt
    rw [this]
    split <;> split <;> simp <;> omega

/-- Every line of `cut3 D q q q` keeps all its `K + 3` points. -/
theorem cut3_bsize_whole (D : TD (K + 3) q) (L : D.Line) : (cut3 D q q q).bsize L = K + 3 := by
  obtain ⟨k0, k1, k2⟩ := cut3_keeps D q q q L
  have t0 : (cut3 D q q q).keeps L 0 = true := by rw [k0]; simpa using D.pt_lt L 0 (by omega)
  have t1 : (cut3 D q q q).keeps L 1 = true := by rw [k1]; simpa using D.pt_lt L 1 (by omega)
  have t2 : (cut3 D q q q).keeps L 2 = true := by rw [k2]; simpa using D.pt_lt L 2 (by omega)
  unfold bsize nopt
  rw [t0, t1, t2]
  rfl

/-- The truncation `cut3 D q q q` keeps everything: its point `e` is in group `e / q`. -/
theorem cut3_whole_grp (D : TD (K + 3) q) {e : Nat} (he : e < (cut3 D q q q).gdd.n) :
    (cut3 D q q q).gdd.grp e = e / q := by
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · change e < (cut3 D 0 0 0).S + K * 0 at he
      rw [cut3_S] at he
      omega
    · exact h
  change (decPt (cut3 D q q q) e).1 = e / q
  have e0 : (cut3 D q q q).n0 = q := by show q - 0 = q; omega
  have e1 : (cut3 D q q q).n1 = q := by show q - 0 = q; omega
  have eS : (cut3 D q q q).S = 3 * q := by rw [cut3_S]; omega
  by_cases b0 : e < q
  · rw [decPt_of_lt0 (by omega), Nat.div_eq_of_lt b0]
  by_cases b1 : e < 2 * q
  · rw [decPt_of_lt1 (by omega) (by omega)]
    show 1 = e / q
    have := Nat.div_add_mod' e q
    have := Nat.mod_lt e hq
    have : e / q < 2 := (Nat.div_lt_iff_lt_mul hq).2 (by omega)
    have : 1 ≤ e / q := (Nat.le_div_iff_mul_le hq).2 (by omega)
    omega
  by_cases b2 : e < 3 * q
  · rw [decPt_of_lt2 (by omega) (by omega) (by omega)]
    show 2 = e / q
    have : e / q < 3 := (Nat.div_lt_iff_lt_mul hq).2 (by omega)
    have : 2 ≤ e / q := (Nat.le_div_iff_mul_le hq).2 (by omega)
    omega
  rw [decPt_of_ge (by omega), eS]
  show 3 + (e - 3 * q) / q = e / q
  rw [show e = (e - 3 * q) + q * 3 by omega, Nat.add_mul_div_left _ _ hq,
    show e - 3 * q + q * 3 - 3 * q = e - 3 * q by omega]
  omega

theorem cut3_whole_n (D : TD (K + 3) q) : (cut3 D q q q).gdd.n = (K + 3) * q := by
  change (cut3 D q q q).S + K * q = _
  rw [cut3_S, Nat.add_mul]
  omega

/-- The size of the group of a kept point. -/
theorem gdd_gsz_grp {T : Cut K q} {x : Nat} :
    T.gdd.gsz (T.gdd.grp x) = T.ghi (T.gdd.grp x) - T.glo (T.gdd.grp x) := rfl

/-- A point of the whole group `3`, when `0 < K`. -/
theorem gdd_whole_pt {T : Cut K q} (hT : T.Valid) (hK : 0 < K) {i : Nat} (hi : i < q) :
    ∃ x, x < T.gdd.n ∧ T.gdd.grp x = 3 ∧ T.gdd.gidx x = i := by
  have hk : T.Kept (3, i) := kept_iff.2 ⟨by omega, by rw [glo_of_ge (by omega)]; omega,
    by rw [ghi_of_ge (by omega)]; exact hi⟩
  refine ⟨T.encPt (3, i), encPt_lt hT hk, ?_, ?_⟩
  · show (T.decPt (T.encPt (3, i))).1 = 3
    rw [decPt_encPt hT hk]
  · show (T.decPt (T.encPt (3, i))).2 - T.glo (T.decPt (T.encPt (3, i))).1 = i
    rw [decPt_encPt hT hk]
    show i - T.glo 3 = i
    rw [glo_of_ge (by omega)]
    omega

end Cut

/-- **A truncation glued with models on its groups.** The groups `0, 1, 2` of `cut3 D a b c`
carry `opa`, `opb`, `opc` with the `m` new points, the whole groups `opq`; every block carries
an idempotent model. -/
theorem hasPtModel_cut3 {K q a b c m : Nat} (D : TD (K + 3) q) (ha : a ≤ q) (hb : b ≤ q)
    (hc : c ≤ q) {emod opa opb opc opq : Nat → Nat → Nat} {bmod : Nat → Nat → Nat → Nat}
    (he : IsModel m emod) (hA : IsModel (m + a) opa) (hB : IsModel (m + b) opb)
    (hC : IsModel (m + c) opc) (hQ : IsModel (m + q) opq)
    (hAe : ∀ x y, x < m → y < m → opa x y = emod x y)
    (hBe : ∀ x y, x < m → y < m → opb x y = emod x y)
    (hCe : ∀ x y, x < m → y < m → opc x y = emod x y)
    (hQe : ∀ x y, x < m → y < m → opq x y = emod x y)
    (hbl : ∀ L : D.Line, IsIdemModel ((cut3 D a b c).bsize L) (bmod ((cut3 D a b c).bsize L)))
    (hpt : (∃ e, e < m ∧ emod e e = e) ∨ (0 < K ∧ ∃ e, e < q ∧ opq (m + e) (m + e) = m + e)) :
    HasPtModel (m + (K * q + a + b + c)) := by
  have hv := Cut.cut3_valid D ha hb hc
  let gmod : Nat → Nat → Nat → Nat := fun g =>
    if g = 0 then opa else if g = 1 then opb else if g = 2 then opc else opq
  have hg : ∀ g, IsModel (m + ((cut3 D a b c).ghi g - (cut3 D a b c).glo g)) (gmod g) ∧
      ∀ x y, x < m → y < m → gmod g x y = emod x y := by
    intro g
    rw [Cut.cut3_gsz]
    by_cases g0 : g = 0
    · simp only [gmod, g0, ite_true]; exact ⟨hA, hAe⟩
    by_cases g1 : g = 1
    · simp only [gmod, g1, ite_true]; exact ⟨hB, hBe⟩
    by_cases g2 : g = 2
    · simp only [gmod, g2]; exact ⟨hC, hCe⟩
    · simp only [gmod, g0, g1, g2, ite_false]; exact ⟨hQ, hQe⟩
  have hok : (cut3 D a b c).gdd.GlueOK m emod gmod bmod :=
    { valid := Cut.gdd_valid hv
      he := he
      hg := fun x _ => (hg _).1
      hge := fun x _ => (hg _).2
      hb := fun x y _ => hbl _ }
  have := GDD.hasPtModel_glue hok ?_
  · have hn : (cut3 D a b c).gdd.n = K * q + a + b + c := by
      change (cut3 D a b c).S + K * q = _
      rw [Cut.cut3_S]
      omega
    rwa [hn] at this
  rcases hpt with h | ⟨hK, e, heq, hee⟩
  · exact Or.inr (Or.inl h)
  · obtain ⟨x, hx, hgx, -⟩ := Cut.gdd_whole_pt (T := cut3 D a b c) hv hK heq
    refine Or.inr (Or.inr ⟨x, hx, m + e, ?_, ?_⟩)
    · rw [Cut.gdd_gsz_grp, hgx, Cut.cut3_gsz]
      simp only [show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
        show (3 : Nat) ≠ 2 by decide, ite_false]
      omega
    · rw [hgx]
      simpa [gmod] using hee

/-! ### Truncations -/

/-- The block models of the truncations with `79` whole groups: `T79`,
`A(5; 2, 4, 0) × F₂[ζ]/(Φ₁₀)` and `F₃[ζ]/(Φ₁₀)`. -/
def bop79 (k : Nat) : Nat → Nat → Nat := if k = 79 then opT79 else if k = 80 then op80 else phiOpN 3

theorem bop79_spec {k : Nat} (h1 : 79 ≤ k) (h2 : k ≤ 81) : IsIdemModel k (bop79 k) := by
  unfold bop79
  by_cases e79 : k = 79
  · subst e79; exact isIdemModel_T79
  by_cases e80 : k = 80
  · subst e80; exact isIdemModel_80
  rw [show k = 81 by omega]
  exact isIdemModel_81

/-- **The two-group truncation.** A `TD(82, q)` and pointed models of sizes `q`, `s ≤ q` and
`r ≤ q` give a pointed model of size `79 q + s + r`: the groups `0` and `1` cut to their first
`s` and `r` points and the group `2` emptied, so that every block has `79`, `80` or `81` points. -/
theorem hasPtModel_two {q s r : Nat} (D : TD 82 q) (hs : s ≤ q) (hr : r ≤ q) (Hq : HasPtModel q)
    (Hs : HasPtModel s) (Hr : HasPtModel r) : HasPtModel (79 * q + s + r) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · rw [show s = 0 by omega, show r = 0 by omega]; exact hasPtModel_zero
  obtain ⟨opq, Hq, eq⟩ := Hq
  obtain ⟨ops, Hs, -⟩ := Hs
  obtain ⟨opr, Hr, -⟩ := Hr
  obtain ⟨e, he, hee⟩ := eq.resolve_left (by omega)
  have := hasPtModel_cut3 (K := 79) (m := 0) D hs hr (Nat.zero_le q) (emod := triv) (opa := ops)
    (opb := opr) (opc := opq) (opq := opq) (bmod := bop79) (isModel_zero _)
    (by rwa [Nat.zero_add]) (by rwa [Nat.zero_add]) (isModel_zero _) (by rwa [Nat.zero_add])
    (fun _ _ h => absurd h (Nat.not_lt_zero _)) (fun _ _ h => absurd h (Nat.not_lt_zero _))
    (fun _ _ h => absurd h (Nat.not_lt_zero _)) (fun _ _ h => absurd h (Nat.not_lt_zero _))
    (fun L => by
      obtain ⟨h1, -, h3, -⟩ := Cut.cut3_bsize D s r 0 L
      exact bop79_spec h1 (h3 rfl))
    (Or.inr ⟨by decide, e, he, by rwa [Nat.zero_add]⟩)
  rwa [Nat.zero_add, Nat.add_zero] at this

/-- **The run truncation.** A `TD(167, q)` and pointed models of sizes `q`, `s ≤ q` and `r ≤ q`
give a pointed model of size `165 q + s + r`, when the idempotent models `bmod 165`,
`bmod 166` and `bmod 167` exist: the groups `0` and `1` cut to their first `s` and `r` points,
so that every block has `165`, `166` or `167` points. -/
theorem hasPtModel_run {q s r : Nat} {bmod : Nat → Nat → Nat → Nat}
    (hb : ∀ k, 165 ≤ k → k ≤ 167 → IsIdemModel k (bmod k)) (D : TD 167 q) (hs : s ≤ q)
    (hr : r ≤ q) (Hq : HasPtModel q) (Hs : HasPtModel s) (Hr : HasPtModel r) :
    HasPtModel (165 * q + s + r) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · rw [show s = 0 by omega, show r = 0 by omega]; exact hasPtModel_zero
  obtain ⟨opq, Hq, eq⟩ := Hq
  obtain ⟨ops, Hs, -⟩ := Hs
  obtain ⟨opr, Hr, -⟩ := Hr
  obtain ⟨e, he, hee⟩ := eq.resolve_left (by omega)
  have := hasPtModel_cut3 (K := 164) (m := 0) D hs hr (Nat.le_refl q) (emod := triv) (opa := ops)
    (opb := opr) (opc := opq) (opq := opq) (bmod := bmod) (isModel_zero _)
    (by rwa [Nat.zero_add]) (by rwa [Nat.zero_add]) (by rwa [Nat.zero_add])
    (by rwa [Nat.zero_add])
    (fun _ _ h => absurd h (Nat.not_lt_zero _)) (fun _ _ h => absurd h (Nat.not_lt_zero _))
    (fun _ _ h => absurd h (Nat.not_lt_zero _)) (fun _ _ h => absurd h (Nat.not_lt_zero _))
    (fun L => by
      obtain ⟨-, h2, -, h4⟩ := Cut.cut3_bsize D s r q L
      exact hb _ (h4 rfl) h2)
    (Or.inr ⟨by decide, e, he, by rwa [Nat.zero_add]⟩)
  rw [Nat.zero_add] at this
  rwa [show 164 * q + s + r + q = 165 * q + s + r by omega] at this

/-- **A point at infinity.** A `TD(5, g)` and a pointed model of size `g + 1` give a pointed
model of size `1 + 5 g`: the idempotent is adjoined to all five groups. -/
theorem hasPtModel_inf {g : Nat} (D : TD 5 g) (Hg : HasPtModel (g + 1)) :
    HasPtModel (1 + 5 * g) := by
  obtain ⟨op, Hop, h0⟩ := exists_idem_zero Hg (by omega)
  have Hop' : IsModel (1 + g) op := by rwa [Nat.add_comm]
  have he : ∀ x y, x < 1 → y < 1 → op x y = triv x y := by
    intro x y hx hy
    rw [show x = 0 by omega, show y = 0 by omega, h0]; rfl
  have := hasPtModel_cut3 (K := 2) (m := 1) D (Nat.le_refl g) (Nat.le_refl g) (Nat.le_refl g)
    (emod := triv) (opa := op) (opb := op) (opc := op) (opq := op) (bmod := fun _ => opF5)
    isIdemModel_triv.toIsModel Hop' Hop' Hop' Hop' he he he he
    (fun L => by rw [Cut.cut3_bsize_whole]; exact isIdemModel_F5)
    (Or.inl ⟨0, by decide, rfl⟩)
  rwa [show 2 * g + g + g + g = 5 * g by omega] at this

/-- **The two-group truncation with a point at infinity.** A `TD(82, q)` and pointed models of
sizes `q + 1`, `s + 1` and `r + 1`, `s, r ≤ q`, give a pointed model of size
`1 + 79 q + s + r`: the idempotents are made one point, adjoined to every group. -/
theorem hasPtModel_inftrunc {q s r : Nat} (D : TD 82 q) (hs : s ≤ q) (hr : r ≤ q)
    (Hq : HasPtModel (q + 1)) (Hs : HasPtModel (s + 1)) (Hr : HasPtModel (r + 1)) :
    HasPtModel (1 + 79 * q + s + r) := by
  obtain ⟨opq, Hq, hq0⟩ := exists_idem_zero Hq (by omega)
  obtain ⟨ops, Hs, hs0⟩ := exists_idem_zero Hs (by omega)
  obtain ⟨opr, Hr, hr0⟩ := exists_idem_zero Hr (by omega)
  have e0 : ∀ {op : Nat → Nat → Nat}, op 0 0 = 0 → ∀ x y, x < 1 → y < 1 → op x y = triv x y := by
    intro op h x y hx hy
    rw [show x = 0 by omega, show y = 0 by omega, h]; rfl
  have := hasPtModel_cut3 (K := 79) (m := 1) D hs hr (Nat.zero_le q) (emod := triv) (opa := ops)
    (opb := opr) (opc := triv) (opq := opq) (bmod := bop79) isIdemModel_triv.toIsModel
    (by rwa [Nat.add_comm]) (by rwa [Nat.add_comm]) isIdemModel_triv.toIsModel
    (by rwa [Nat.add_comm]) (e0 hs0) (e0 hr0) (e0 rfl) (e0 hq0)
    (fun L => by
      obtain ⟨h1, -, h3, -⟩ := Cut.cut3_bsize D s r 0 L
      exact bop79_spec h1 (h3 rfl))
    (Or.inl ⟨0, by decide, rfl⟩)
  rwa [show 1 + (79 * q + s + r + 0) = 1 + 79 * q + s + r by omega] at this

/-! ### The keep truncation -/

/-- In `cyclicTD`, the point in group `2` is the sum of the points in groups `0` and `1`. -/
theorem cyclicTD_pt_two {q : Nat} (hq : Nat.gcd q P79 = 1) (L : (cyclicTD hq).Line) :
    (cyclicTD hq).pt L 2 = ((cyclicTD hq).pt L 0 + (cyclicTD hq).pt L 1) % q := by
  exact @cyclicPlane_pt_two q 81 (neZero_of_gcd hq) _ L

/-- The **keep truncation** of `cyclicTD` to `79 q + s₁ + s₂ + s₃`: groups `0` and `1` cut to
their first `s₁` and `s₂` points, group `2` to its last `s₃`. -/
noncomputable def cutKeep {q : Nat} (hq : Nat.gcd q P79 = 1) (s₁ s₂ s₃ : Nat) : Cut 79 q :=
  ⟨cyclicTD hq, fun j => if j = 2 then q - s₃ else 0,
    fun j => if j = 0 then s₁ else if j = 1 then s₂ else q⟩

theorem cutKeep_valid {q s₁ s₂ s₃ : Nat} (hq : Nat.gcd q P79 = 1) (h₁ : s₁ ≤ q) (h₂ : s₂ ≤ q)
    (h₃ : s₃ ≤ q) : (cutKeep hq s₁ s₂ s₃).Valid where
  lo_le j hj := by
    show (if j = 2 then q - s₃ else 0) ≤ (if j = 0 then s₁ else if j = 1 then s₂ else q)
    split <;> split <;> (try split) <;> omega
  hi_le j _ := by
    show (if j = 0 then s₁ else if j = 1 then s₂ else q) ≤ q
    split <;> (try split) <;> omega

theorem cutKeep_gsz {q s₁ s₂ s₃ : Nat} (hq : Nat.gcd q P79 = 1) (h₃ : s₃ ≤ q) (g : Nat) :
    (cutKeep hq s₁ s₂ s₃).ghi g - (cutKeep hq s₁ s₂ s₃).glo g =
      if g = 0 then s₁ else if g = 1 then s₂ else if g = 2 then s₃ else q := by
  unfold Cut.ghi Cut.glo
  by_cases h3 : g < 3
  · rw [ite_of_pos h3, ite_of_pos h3]
    show (if g = 0 then s₁ else if g = 1 then s₂ else q) - (if g = 2 then q - s₃ else 0) = _
    rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl <;> simp <;> omega
  · rw [ite_of_neg h3, ite_of_neg h3, Nat.sub_zero, ite_of_neg (by omega), ite_of_neg (by omega),
      ite_of_neg (by omega)]

/-- **No line keeps all three cut points**: `a < s₁` and `b < s₂` give
`a + b ≤ s₁ + s₂ - 2 < q - s₃` when `s₁ + s₂ + s₃ ≤ q + 1`. So every block has `79`, `80` or
`81` points. -/
theorem cutKeep_bsize {q s₁ s₂ s₃ : Nat} (hq : Nat.gcd q P79 = 1) (hs : s₁ + s₂ + s₃ ≤ q + 1)
    (L : (cyclicTD hq).Line) : 79 ≤ (cutKeep hq s₁ s₂ s₃).bsize L ∧
      (cutKeep hq s₁ s₂ s₃).bsize L ≤ 81 := by
  have hpt := cyclicTD_pt_two hq L
  have l0 := (cyclicTD hq).pt_lt L 0 (by decide)
  have l1 := (cyclicTD hq).pt_lt L 1 (by decide)
  have key : ¬ ((cutKeep hq s₁ s₂ s₃).keeps L 0 = true ∧ (cutKeep hq s₁ s₂ s₃).keeps L 1 = true ∧
      (cutKeep hq s₁ s₂ s₃).keeps L 2 = true) := by
    unfold Cut.keeps cutKeep
    simp only [decide_eq_true_eq]
    intro ⟨⟨_, a⟩, ⟨_, b⟩, ⟨c, _⟩⟩
    simp only [ite_true, show (0 : Nat) ≠ 1 by decide, show (1 : Nat) ≠ 0 by decide,
      ite_false] at a b c
    change (cyclicTD hq).pt L 0 < s₁ at a
    change (cyclicTD hq).pt L 1 < s₂ at b
    change q - s₃ ≤ (cyclicTD hq).pt L 2 at c
    rw [hpt, Nat.mod_eq_of_lt (by omega)] at c
    omega
  unfold Cut.bsize Cut.nopt
  revert key
  cases (cutKeep hq s₁ s₂ s₃).keeps L 0 <;> cases (cutKeep hq s₁ s₂ s₃).keeps L 1 <;>
    cases (cutKeep hq s₁ s₂ s₃).keeps L 2 <;> simp

theorem cutKeep_S {q s₁ s₂ s₃ : Nat} (hq : Nat.gcd q P79 = 1) (h₃ : s₃ ≤ q) :
    (cutKeep hq s₁ s₂ s₃).S = s₁ + s₂ + s₃ := by
  show ((if (0 : Nat) = 0 then s₁ else if (0 : Nat) = 1 then s₂ else q) -
      (if (0 : Nat) = 2 then q - s₃ else 0)) +
    ((if (1 : Nat) = 0 then s₁ else if (1 : Nat) = 1 then s₂ else q) -
      (if (1 : Nat) = 2 then q - s₃ else 0)) +
    ((if (2 : Nat) = 0 then s₁ else if (2 : Nat) = 1 then s₂ else q) -
      (if (2 : Nat) = 2 then q - s₃ else 0)) = s₁ + s₂ + s₃
  simp only [ite_true, show (0 : Nat) ≠ 1 by decide, show (1 : Nat) ≠ 0 by decide,
    show (0 : Nat) ≠ 2 by decide, show (1 : Nat) ≠ 2 by decide, show (2 : Nat) ≠ 0 by decide,
    show (2 : Nat) ≠ 1 by decide, ite_false]
  omega

/-! ### Truncations as models, with their first group a submagma -/

/-- **A truncation with lower end `0` in group `0` contains the model of group `0`**: on the
first `hi 0` points the glued operation (with no new points) is the model of group `0`. -/
theorem Cut.glue_slot0 {K q : Nat} {T : Cut K q} (_hT : T.Valid) (h0 : T.lo 0 = 0)
    {emod : Nat → Nat → Nat} {gmod bmod : Nat → Nat → Nat → Nat}
    (hok : T.gdd.GlueOK 0 emod gmod bmod) {a b : Nat} (ha : a < T.hi 0) (hb : b < T.hi 0) :
    T.gdd.glue 0 emod gmod bmod a b = gmod 0 a b := by
  have n0 : T.n0 = T.hi 0 := by show T.hi 0 - T.lo 0 = T.hi 0; omega
  have hx : a < T.gdd.n := by
    show a < T.S + K * q
    have : T.S = T.n0 + T.n1 + T.n2 := rfl
    omega
  have hg : T.gdd.grp a = 0 := Cut.gdd_grp_lt0 (by omega)
  have hsz : T.gdd.gsz 0 = T.hi 0 := by
    show T.ghi 0 - T.glo 0 = T.hi 0
    rw [Cut.ghi_of_lt (by decide), Cut.glo_of_lt (by decide), h0, Nat.sub_zero]
  have ha' : a < 0 + T.gdd.gsz (T.gdd.grp a) := by rw [hg, hsz]; omega
  have hb' : b < 0 + T.gdd.gsz (T.gdd.grp a) := by rw [hg, hsz]; omega
  have e : ∀ i, T.gdd.gemb 0 0 i = i := by
    intro i
    unfold GDD.gemb
    rw [ite_of_neg (Nat.not_lt_zero _), Nat.zero_add, Nat.sub_zero, Cut.gdd_gpt0 h0]
  have := GDD.glue_gemb hok hx ha' hb'
  rw [hg, e, e, e] at this
  exact this

/-- The two-group truncation's glued operation, with the models `opq`, `ops`, `opr`. -/
def twoOp {q : Nat} (D : TD 82 q) (s r : Nat) (opq ops opr : Nat → Nat → Nat) :
    Nat → Nat → Nat :=
  (cut3 D s r 0).gdd.glue 0 triv
    (fun g => if g = 0 then ops else if g = 1 then opr else if g = 2 then opq else opq) bop79

/-- The two-group truncation's glued operation is a model of order `s + r + 79 q`, equal to
`ops` on its first `s` points. -/
theorem twoOp_spec {q s r : Nat} (D : TD 82 q) (hs : s ≤ q) (hr : r ≤ q)
    {opq ops opr : Nat → Nat → Nat} (Hq : IsModel q opq) (Hs : IsModel s ops)
    (Hr : IsModel r opr) :
    IsModel (s + (79 * q + r)) (twoOp D s r opq ops opr) ∧
      ∀ a b, a < s → b < s → twoOp D s r opq ops opr a b = ops a b := by
  have hv := Cut.cut3_valid D hs hr (Nat.zero_le q)
  have hok : (cut3 D s r 0).gdd.GlueOK 0 triv
      (fun g => if g = 0 then ops else if g = 1 then opr else if g = 2 then opq else opq)
      bop79 :=
    { valid := Cut.gdd_valid hv
      he := isModel_zero _
      hg := fun x _ => by
        rw [Nat.zero_add, Cut.gdd_gsz_grp, Cut.cut3_gsz]
        generalize (cut3 D s r 0).gdd.grp x = g
        by_cases g0 : g = 0
        · simp only [g0, ite_true]; exact Hs
        by_cases g1 : g = 1
        · simp only [g1, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]; exact Hr
        by_cases g2 : g = 2
        · simp only [g2, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_true,
            ite_false]
          exact isModel_zero _
        · simp only [g0, g1, g2, ite_false]; exact Hq
      hge := fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)
      hb := fun x y _ => by
        obtain ⟨h1, -, h3, -⟩ :=
          Cut.cut3_bsize D s r 0 ((cut3 D s r 0).lineOf ((cut3 D s r 0).gdd.blk x y))
        exact bop79_spec h1 (h3 rfl) }
  have hn : (cut3 D s r 0).gdd.n = s + (79 * q + r) := by
    change (cut3 D s r 0).S + 79 * q = _
    rw [Cut.cut3_S]
    omega
  refine ⟨?_, fun a b ha hb => ?_⟩
  · have := GDD.isModel_glue hok
    rwa [Nat.zero_add, hn] at this
  · exact Cut.glue_slot0 hv rfl hok
      (by change a < (if (0 : Nat) = 0 then s else if (0 : Nat) = 1 then r else 0); simpa using ha)
      (by change b < (if (0 : Nat) = 0 then s else if (0 : Nat) = 1 then r else 0); simpa using hb)

/-- The keep truncation's glued operation, with the models `opq`, `op₁`, `op₂`, `op₃`. -/
noncomputable def keepOp {q : Nat} (hq : Nat.gcd q P79 = 1) (s₁ s₂ s₃ : Nat)
    (opq op₁ op₂ op₃ : Nat → Nat → Nat) : Nat → Nat → Nat :=
  (cutKeep hq s₁ s₂ s₃).gdd.glue 0 triv
    (fun g => if g = 0 then op₁ else if g = 1 then op₂ else if g = 2 then op₃ else opq) bop79

/-- The keep truncation's glued operation is a model of order `s₁ + (79 q + s₂ + s₃)`, equal to
`op₁` on its first `s₁` points. -/
theorem keepOp_spec {q s₁ s₂ s₃ : Nat} (hq : Nat.gcd q P79 = 1) (h₁ : s₁ ≤ q) (h₂ : s₂ ≤ q)
    (h₃ : s₃ ≤ q) (hs : s₁ + s₂ + s₃ ≤ q + 1) {opq op₁ op₂ op₃ : Nat → Nat → Nat}
    (Hq : IsModel q opq) (H₁ : IsModel s₁ op₁) (H₂ : IsModel s₂ op₂) (H₃ : IsModel s₃ op₃) :
    IsModel (s₁ + (79 * q + s₂ + s₃)) (keepOp hq s₁ s₂ s₃ opq op₁ op₂ op₃) ∧
      ∀ a b, a < s₁ → b < s₁ → keepOp hq s₁ s₂ s₃ opq op₁ op₂ op₃ a b = op₁ a b := by
  have hv := cutKeep_valid hq h₁ h₂ h₃
  have hok : (cutKeep hq s₁ s₂ s₃).gdd.GlueOK 0 triv
      (fun g => if g = 0 then op₁ else if g = 1 then op₂ else if g = 2 then op₃ else opq)
      bop79 :=
    { valid := Cut.gdd_valid hv
      he := isModel_zero _
      hg := fun x _ => by
        rw [Nat.zero_add, Cut.gdd_gsz_grp, cutKeep_gsz hq h₃]
        generalize (cutKeep hq s₁ s₂ s₃).gdd.grp x = g
        by_cases g0 : g = 0
        · simp only [g0, ite_true]; exact H₁
        by_cases g1 : g = 1
        · simp only [g1, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]; exact H₂
        by_cases g2 : g = 2
        · simp only [g2, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_true,
            ite_false]
          exact H₃
        · simp only [g0, g1, g2, ite_false]; exact Hq
      hge := fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)
      hb := fun x y _ => by
        have := cutKeep_bsize hq hs
          ((cutKeep hq s₁ s₂ s₃).lineOf ((cutKeep hq s₁ s₂ s₃).gdd.blk x y))
        exact bop79_spec this.1 this.2 }
  have hn : (cutKeep hq s₁ s₂ s₃).gdd.n = s₁ + (79 * q + s₂ + s₃) := by
    change (cutKeep hq s₁ s₂ s₃).S + 79 * q = _
    rw [cutKeep_S hq h₃]
    omega
  refine ⟨?_, fun a b ha hb => ?_⟩
  · have := GDD.isModel_glue hok
    rwa [Nat.zero_add, hn] at this
  · exact Cut.glue_slot0 hv rfl hok
      (by change a < (if (0 : Nat) = 0 then s₁ else if (0 : Nat) = 1 then s₂ else q)
          simpa using ha)
      (by change b < (if (0 : Nat) = 0 then s₁ else if (0 : Nat) = 1 then s₂ else q)
          simpa using hb)

/-- **The keep truncation.** For `q` coprime to `P79`, pointed models of sizes `q` and
`s₁, s₂, s₃ ≤ q` with `s₁ + s₂ + s₃ ≤ q + 1` give a pointed model of size
`79 q + s₁ + s₂ + s₃`. -/
theorem hasPtModel_keep {q s₁ s₂ s₃ : Nat} (hq : Nat.gcd q P79 = 1) (h₁ : s₁ ≤ q) (h₂ : s₂ ≤ q)
    (h₃ : s₃ ≤ q) (hs : s₁ + s₂ + s₃ ≤ q + 1) (Hq : HasPtModel q) (H₁ : HasPtModel s₁)
    (H₂ : HasPtModel s₂) (H₃ : HasPtModel s₃) : HasPtModel (79 * q + s₁ + s₂ + s₃) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp [P79] at hq)
  obtain ⟨opq, Hq, eq⟩ := Hq
  obtain ⟨op₁, H₁, -⟩ := H₁
  obtain ⟨op₂, H₂, -⟩ := H₂
  obtain ⟨op₃, H₃, -⟩ := H₃
  obtain ⟨e, he, hee⟩ := eq.resolve_left (by omega)
  have hv := cutKeep_valid hq h₁ h₂ h₃
  have hok : (cutKeep hq s₁ s₂ s₃).gdd.GlueOK 0 triv
      (fun g => if g = 0 then op₁ else if g = 1 then op₂ else if g = 2 then op₃ else opq)
      bop79 :=
    { valid := Cut.gdd_valid hv
      he := isModel_zero _
      hg := fun x _ => by
        rw [Nat.zero_add, Cut.gdd_gsz_grp, cutKeep_gsz hq h₃]
        generalize (cutKeep hq s₁ s₂ s₃).gdd.grp x = g
        by_cases g0 : g = 0
        · simp only [g0, ite_true]; exact H₁
        by_cases g1 : g = 1
        · simp only [g1, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]; exact H₂
        by_cases g2 : g = 2
        · simp only [g2, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_true,
            ite_false]
          exact H₃
        · simp only [g0, g1, g2, ite_false]; exact Hq
      hge := fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)
      hb := fun x y _ => by
        have := cutKeep_bsize hq hs
          ((cutKeep hq s₁ s₂ s₃).lineOf ((cutKeep hq s₁ s₂ s₃).gdd.blk x y))
        exact bop79_spec this.1 this.2 }
  obtain ⟨x, hx, hgx, -⟩ := Cut.gdd_whole_pt (T := cutKeep hq s₁ s₂ s₃) hv (by decide) he
  have := GDD.hasPtModel_glue hok (Or.inr (Or.inr ⟨x, hx, e, ?_, ?_⟩))
  · have hn : (cutKeep hq s₁ s₂ s₃).gdd.n = 79 * q + s₁ + s₂ + s₃ := by
      change (cutKeep hq s₁ s₂ s₃).S + 79 * q = _
      rw [cutKeep_S hq h₃]
      omega
    rwa [Nat.zero_add, hn] at this
  · rw [Nat.zero_add, Cut.gdd_gsz_grp, hgx, cutKeep_gsz hq h₃]
    simpa using he
  · rw [hgx]
    simpa using hee

/-! ### Truncations adjoined at a cut group -/

/-- **A two-group truncation adjoined at its cut group.** The two-group truncation
`79 q + s + r`, its first group of `s` points numbered first, is a model in which those `s`
points form a submagma; put it on every group of a `TD(5, g)`, `g = 79 q + r`, all the groups
sharing those `s` points, and `A(5; 2, 4, 0)` on the blocks: a pointed model of size `5 g + s`. -/
theorem hasPtModel_sub2 {q s r : Nat} (D : TD 82 q) (D5 : TD 5 (79 * q + r)) (hs1 : 1 ≤ s)
    (hs : s ≤ q) (hr : r ≤ q) (Hq : HasPtModel q) (Hs : HasPtModel s) (Hr : HasPtModel r) :
    HasPtModel (5 * (79 * q + r) + s) := by
  obtain ⟨opq, Hq, -⟩ := Hq
  obtain ⟨ops, Hs, es⟩ := Hs
  obtain ⟨opr, Hr, -⟩ := Hr
  obtain ⟨e, he, hee⟩ := es.resolve_left (by omega)
  obtain ⟨HT, HTs⟩ := twoOp_spec D hs hr Hq Hs Hr
  have HE : IsModel s (twoOp D s r opq ops opr) := Hs.congr HTs
  have hE : ∀ x y, x < s → y < s → twoOp D s r opq ops opr x y = twoOp D s r opq ops opr x y :=
    fun _ _ _ _ => rfl
  have := hasPtModel_cut3 (K := 2) (m := s) D5 (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (emod := twoOp D s r opq ops opr) (opa := twoOp D s r opq ops opr)
    (opb := twoOp D s r opq ops opr) (opc := twoOp D s r opq ops opr)
    (opq := twoOp D s r opq ops opr) (bmod := fun _ => opF5) HE HT HT HT HT hE hE hE hE
    (fun L => by rw [Cut.cut3_bsize_whole]; exact isIdemModel_F5)
    (Or.inl ⟨e, he, by rw [HTs e e he he]; exact hee⟩)
  rwa [show s + (2 * (79 * q + r) + (79 * q + r) + (79 * q + r) + (79 * q + r)) =
    5 * (79 * q + r) + s by omega] at this

/-- **A keep truncation adjoined at its cut group**: as `hasPtModel_sub2`, from the keep
truncation `79 q + s₁ + s₂ + s₃`, `1 ≤ s₁`, its first group of `s₁` points shared. -/
theorem hasPtModel_subk {q s₁ s₂ s₃ : Nat} (hq : Nat.gcd q P79 = 1)
    (D5 : TD 5 (79 * q + s₂ + s₃)) (hs1 : 1 ≤ s₁) (h₁ : s₁ ≤ q) (h₂ : s₂ ≤ q) (h₃ : s₃ ≤ q)
    (hs : s₁ + s₂ + s₃ ≤ q + 1) (Hq : HasPtModel q) (H₁ : HasPtModel s₁) (H₂ : HasPtModel s₂)
    (H₃ : HasPtModel s₃) : HasPtModel (5 * (79 * q + s₂ + s₃) + s₁) := by
  obtain ⟨opq, Hq, -⟩ := Hq
  obtain ⟨op₁, H₁, e₁⟩ := H₁
  obtain ⟨op₂, H₂, -⟩ := H₂
  obtain ⟨op₃, H₃, -⟩ := H₃
  obtain ⟨e, he, hee⟩ := e₁.resolve_left (by omega)
  obtain ⟨HT, HTs⟩ := keepOp_spec hq h₁ h₂ h₃ hs Hq H₁ H₂ H₃
  have HE : IsModel s₁ (keepOp hq s₁ s₂ s₃ opq op₁ op₂ op₃) := H₁.congr HTs
  have hE : ∀ x y, x < s₁ → y < s₁ → keepOp hq s₁ s₂ s₃ opq op₁ op₂ op₃ x y =
      keepOp hq s₁ s₂ s₃ opq op₁ op₂ op₃ x y := fun _ _ _ _ => rfl
  have := hasPtModel_cut3 (K := 2) (m := s₁) D5 (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (emod := keepOp hq s₁ s₂ s₃ opq op₁ op₂ op₃) (opa := keepOp hq s₁ s₂ s₃ opq op₁ op₂ op₃)
    (opb := keepOp hq s₁ s₂ s₃ opq op₁ op₂ op₃) (opc := keepOp hq s₁ s₂ s₃ opq op₁ op₂ op₃)
    (opq := keepOp hq s₁ s₂ s₃ opq op₁ op₂ op₃) (bmod := fun _ => opF5) HE HT HT HT HT
    hE hE hE hE
    (fun L => by rw [Cut.cut3_bsize_whole]; exact isIdemModel_F5)
    (Or.inl ⟨e, he, by rw [HTs e e he he]; exact hee⟩)
  rwa [show s₁ + (2 * (79 * q + s₂ + s₃) + (79 * q + s₂ + s₃) + (79 * q + s₂ + s₃) +
    (79 * q + s₂ + s₃)) = 5 * (79 * q + s₂ + s₃) + s₁ by omega] at this

/-! ### Models glued along developed designs -/

namespace GDD

variable {B : Type} {D : GDD B}

/-- **With idempotent models on the groups and no new points, the glued model is idempotent.** -/
theorem glue_idem_all {emod : Nat → Nat → Nat} {gmod bmod : Nat → Nat → Nat → Nat}
    (hok : D.GlueOK 0 emod gmod bmod)
    (hid : ∀ x, x < D.n → ∀ i, i < 0 + D.gsz (D.grp x) → gmod (D.grp x) i i = i) {x : Nat}
    (hx : x < D.n) : D.glue 0 emod gmod bmod x x = x := by
  have hx' : x < 0 + D.n := by omega
  obtain ⟨l, e⟩ := gloc_spec hok.valid hx' (Nat.not_lt_zero x)
  rw [Nat.sub_zero] at l e
  have := glue_gemb hok hx l l
  rw [e, hid x hx _ l, e] at this
  exact this

end GDD

namespace Dev

variable {E : Dev}

/-- Every base block has five points. -/
def len5 (E : Dev) : Bool := E.base.all fun L => L.length == 5

theorem sz_five (hc : E.Checked) (h5 : E.len5 = true) {x y : Nat} (h : E.gdd.Cross x y) :
    E.gdd.sz (E.gdd.blk x y) = 5 := by
  obtain ⟨i, j₁, j₂, t, hm, ht, hb, -, -⟩ := blk_spec E hc h
  rw [hb]
  show (E.blockOf (i * E.N + t)).length = 5
  unfold blockOf
  rw [mul_add_div ht]
  have := List.all_eq_true.1 h5 _ (getD_mem_base (mem_triples.1 hm).1)
  simpa using this

/-- The size of the group of a point: `W` for the fixed points, `N / Mo r` in the orbit `r`. -/
theorem gsz_grp (hp : E.Params) {x : Nat} (hx : x < E.W + E.R * E.N) :
    E.gdd.gsz (E.gdd.grp x) = if x < E.W then E.W else E.N / E.Mo (E.orb x) := by
  change (if E.grp x = 0 then E.W else E.N / E.Mo ((E.grp x - 1) / E.N)) = _
  by_cases hw : x < E.W
  · rw [ite_of_pos (by unfold grp; rw [ite_of_pos hw]), ite_of_pos hw]
  · have m0 := (hp.hM _ (orb_lt hp hx hw)).1
    have mN := Nat.le_of_dvd hp.hN (hp.hM _ (orb_lt hp hx hw)).2
    have := Nat.mod_lt (E.pos x) m0
    have g0 : E.grp x ≠ 0 := by unfold grp; rw [ite_of_neg hw]; omega
    have g1 : (E.grp x - 1) / E.N = E.orb x := by
      unfold grp
      rw [ite_of_neg hw, Nat.add_sub_cancel_left, mul_add_div (by omega)]
    rw [ite_of_neg g0, g1, ite_of_neg hw]

/-- **A model glued along a developed design** with blocks of five points, `A(5; 2, 4, 0)` on
the blocks and the models `gmod` on the groups. -/
theorem hasPtModel_glue5 (hck : E.check = true) (h5 : E.len5 = true)
    (gmod : Nat → Nat → Nat → Nat)
    (hg : ∀ x, x < E.W + E.R * E.N → IsModel (E.gdd.gsz (E.gdd.grp x)) (gmod (E.gdd.grp x)))
    (hpt : ∃ x, x < E.W + E.R * E.N ∧ ∃ i, i < E.gdd.gsz (E.gdd.grp x) ∧
      gmod (E.gdd.grp x) i i = i) :
    HasPtModel (E.W + E.R * E.N) := by
  have hc := checked_of_check hck
  have hok : E.gdd.GlueOK 0 triv gmod (fun _ => opF5) :=
    { valid := gdd_valid hc
      he := isModel_zero _
      hg := fun x hx => by rw [Nat.zero_add]; exact hg x hx
      hge := fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)
      hb := fun x y h => by rw [sz_five hc h5 h]; exact isIdemModel_F5 }
  obtain ⟨x, hx, i, hi, hii⟩ := hpt
  have := GDD.hasPtModel_glue hok (Or.inr (Or.inr ⟨x, hx, i, by omega, hii⟩))
  rwa [Nat.zero_add] at this

end Dev

def base46 : List (List Nat) :=
  [[4, 8, 12, 16, 20], [0, 8, 13, 18, 23], [0, 6, 12, 19, 21], [0, 7, 10, 17, 20],
   [0, 4, 9, 15, 22], [0, 5, 11, 14, 16]]

def base126 : List (List Nat) :=
  [[0, 12, 33, 40, 55], [0, 13, 31, 36, 58], [0, 14, 25, 51, 71], [0, 15, 47, 59, 68],
   [0, 16, 30, 41, 67], [0, 17, 27, 56, 69], [0, 18, 35, 45, 62], [0, 19, 34, 54, 66],
   [0, 20, 24, 38, 49], [0, 21, 28, 43, 63], [0, 22, 39, 52, 70], [0, 23, 37, 57, 61],
   [0, 26, 46, 50, 64], [0, 29, 42, 48, 65], [0, 32, 44, 53, 60], [12, 24, 45, 52, 67],
   [12, 25, 43, 48, 70], [12, 32, 36, 50, 61]]

def base557 : List (List Nat) :=
  [[49, 88, 63, 138, 243], [49, 155, 61, 89, 179], [49, 158, 150, 174, 233],
   [303, 342, 317, 392, 497], [303, 409, 315, 343, 433], [303, 412, 404, 428, 487],
   [49, 108, 173, 163, 479], [49, 154, 119, 56, 472], [49, 139, 109, 55, 466],
   [303, 362, 427, 417, 225], [303, 408, 373, 310, 218], [303, 393, 363, 309, 212],
   [49, 85, 165, 156, 427], [49, 98, 94, 50, 373], [49, 91, 142, 68, 363],
   [303, 339, 419, 410, 173], [303, 352, 348, 304, 119], [303, 345, 396, 322, 109],
   [49, 95, 177, 385, 453], [49, 161, 195, 337, 486], [49, 145, 283, 314, 478],
   [303, 349, 431, 131, 199], [303, 415, 449, 83, 232], [303, 399, 537, 60, 224],
   [49, 81, 239, 309, 474], [49, 149, 230, 417, 504], [49, 171, 186, 310, 439],
   [303, 335, 493, 55, 220], [303, 403, 484, 163, 250], [303, 425, 440, 56, 185],
   [49, 107, 282, 426, 551], [49, 135, 285, 354, 443], [49, 159, 215, 383, 550],
   [303, 361, 536, 172, 297], [303, 389, 539, 100, 189], [303, 413, 469, 129, 296],
   [176, 208, 287, 297, 423], [176, 276, 253, 189, 424], [176, 298, 242, 296, 316],
   [430, 462, 541, 551, 169], [430, 530, 507, 443, 170], [430, 552, 496, 550, 62],
   [49, 221, 270, 217, 218], [49, 269, 184, 193, 212], [49, 292, 201, 245, 225],
   [303, 475, 524, 471, 472], [303, 523, 438, 447, 466], [303, 546, 455, 499, 479],
   [176, 206, 231, 245, 496], [176, 238, 205, 217, 541], [176, 211, 219, 193, 507],
   [430, 460, 485, 499, 242], [430, 492, 459, 471, 287], [430, 465, 473, 447, 253],
   [49, 196, 185, 308, 456], [49, 302, 220, 398, 543], [49, 284, 250, 330, 545],
   [303, 450, 439, 54, 202], [303, 556, 474, 144, 289], [303, 538, 504, 76, 291],
   [49, 248, 202, 358, 438], [49, 274, 289, 332, 455], [49, 260, 291, 346, 524],
   [303, 502, 456, 104, 184], [303, 528, 543, 78, 201], [303, 514, 545, 92, 270],
   [49, 209, 277, 393, 451], [49, 295, 190, 362, 448], [49, 278, 188, 408, 518],
   [303, 463, 531, 139, 197], [303, 549, 444, 108, 194], [303, 532, 442, 154, 264],
   [0, 49, 176, 303, 430], [1, 49, 254, 386, 556], [2, 49, 261, 356, 538], [3, 49, 267, 421, 450],
   [4, 49, 219, 347, 552], [5, 49, 231, 377, 462], [6, 49, 205, 312, 530], [7, 49, 189, 351, 473],
   [8, 49, 296, 326, 485], [9, 49, 297, 359, 459], [10, 49, 298, 382, 522],
   [11, 49, 208, 407, 527], [12, 49, 276, 374, 495], [13, 49, 247, 313, 510],
   [14, 49, 255, 366, 553], [15, 49, 280, 357, 481], [16, 49, 246, 420, 491],
   [17, 49, 236, 367, 446], [18, 49, 300, 376, 480], [19, 49, 181, 411, 463],
   [20, 49, 271, 323, 549], [21, 49, 203, 429, 532], [22, 49, 228, 322, 454],
   [23, 49, 275, 410, 505], [24, 49, 279, 304, 458], [25, 49, 180, 318, 432],
   [26, 49, 252, 334, 468], [27, 49, 223, 384, 517], [28, 49, 290, 415, 546],
   [29, 49, 183, 399, 475], [30, 49, 182, 349, 523], [31, 49, 242, 364, 521],
   [32, 49, 287, 319, 508], [33, 49, 253, 353, 515], [34, 49, 206, 369, 435],
   [35, 49, 238, 414, 525], [36, 49, 211, 380, 457], [37, 49, 240, 428, 489],
   [38, 49, 249, 392, 535], [39, 49, 293, 343, 520], [40, 49, 237, 305, 496],
   [41, 49, 192, 341, 541], [42, 49, 226, 390, 507], [43, 49, 241, 406, 452],
   [44, 49, 268, 355, 467], [45, 49, 273, 402, 498], [46, 49, 222, 327, 519],
   [47, 49, 288, 378, 470], [48, 49, 272, 331, 555]]

def base383 : List (List Nat) :=
  [[201, 286, 341, 324, 374], [201, 238, 369, 307, 302], [201, 261, 348, 336, 382],
   [19, 104, 159, 142, 192], [19, 56, 187, 125, 120], [19, 79, 166, 154, 200],
   [201, 290, 335, 370, 327], [201, 274, 315, 357, 334], [201, 221, 317, 331, 306],
   [19, 108, 153, 188, 145], [19, 92, 133, 175, 152], [19, 39, 135, 149, 124],
   [110, 137, 317, 338, 323], [110, 171, 335, 342, 298], [110, 113, 315, 378, 346],
   [292, 319, 135, 156, 141], [292, 353, 153, 160, 116], [292, 295, 133, 196, 164],
   [110, 163, 265, 282, 214], [110, 132, 231, 202, 227], [110, 126, 289, 210, 253],
   [292, 345, 83, 100, 32], [292, 314, 49, 20, 45], [292, 308, 107, 28, 71],
   [110, 181, 246, 208, 291], [110, 112, 242, 264, 283], [110, 128, 206, 222, 211],
   [292, 363, 64, 26, 109], [292, 294, 60, 82, 101], [292, 310, 24, 40, 29],
   [19, 113, 280, 337, 377], [19, 137, 275, 333, 329], [19, 171, 230, 297, 352],
   [201, 295, 98, 155, 195], [201, 319, 93, 151, 147], [201, 353, 48, 115, 170],
   [19, 132, 256, 340, 330], [19, 126, 241, 360, 361], [19, 163, 288, 358, 367],
   [201, 314, 74, 158, 148], [201, 308, 59, 178, 179], [201, 345, 106, 176, 185],
   [19, 118, 226, 223, 334], [19, 182, 244, 217, 306], [19, 121, 224, 254, 327],
   [201, 300, 44, 41, 152], [201, 364, 62, 35, 124], [201, 303, 42, 72, 145],
   [19, 173, 258, 279, 326], [19, 131, 259, 266, 325], [19, 117, 268, 240, 316],
   [201, 355, 76, 97, 144], [201, 313, 77, 84, 143], [201, 299, 86, 58, 134],
   [19, 29, 208, 242, 284], [19, 109, 264, 206, 220], [19, 101, 222, 246, 281],
   [201, 211, 26, 60, 102], [201, 291, 82, 24, 38], [201, 283, 40, 64, 99],
   [0, 19, 110, 201, 292], [1, 19, 162, 233, 314], [2, 19, 123, 216, 308], [3, 19, 136, 245, 345],
   [4, 19, 191, 260, 312], [5, 19, 111, 277, 381], [6, 19, 119, 248, 365], [7, 19, 161, 250, 296],
   [8, 19, 114, 278, 328], [9, 19, 146, 257, 343], [10, 19, 156, 243, 294],
   [11, 19, 160, 215, 310], [12, 19, 196, 236, 363], [13, 19, 181, 210, 335],
   [14, 19, 112, 282, 315], [15, 19, 128, 202, 317], [16, 19, 144, 283, 354],
   [17, 19, 143, 211, 304], [18, 19, 134, 291, 309]]

def base165 : List (List Nat) :=
  [[1, 47, 155, 126, 131], [1, 51, 147, 144, 153], [1, 50, 149, 160, 127], [1, 81, 128, 156, 154],
   [1, 63, 164, 157, 137], [83, 129, 73, 44, 49], [83, 133, 65, 62, 71], [83, 132, 67, 78, 45],
   [83, 163, 46, 74, 72], [83, 145, 82, 75, 55], [1, 4, 79, 48, 112], [1, 31, 43, 61, 86],
   [1, 14, 52, 68, 113], [1, 8, 60, 56, 96], [1, 30, 58, 59, 90], [83, 86, 161, 130, 30],
   [83, 113, 125, 143, 4], [83, 96, 134, 150, 31], [83, 90, 142, 138, 14], [83, 112, 140, 141, 8],
   [1, 75, 101, 119, 141], [1, 44, 99, 115, 130], [1, 62, 120, 116, 143], [1, 78, 84, 85, 150],
   [1, 74, 93, 103, 138], [83, 157, 19, 37, 59], [83, 126, 17, 33, 48], [83, 144, 38, 34, 61],
   [83, 160, 2, 3, 68], [83, 156, 11, 21, 56], [2, 11, 17, 19, 38], [84, 93, 99, 101, 120],
   [0, 1, 42, 83, 124]]

def base53 : List (List Nat) :=
  [[0, 1, 14, 27, 40], [2, 13, 19, 22, 40], [4, 11, 16, 25, 40], [10, 5, 20, 21, 40],
   [15, 26, 32, 35, 40], [17, 24, 29, 38, 40], [23, 18, 33, 34, 40], [28, 39, 6, 9, 40],
   [30, 37, 3, 12, 40], [36, 31, 7, 8, 40]]

/-- A `5`-GDD of type `4⁶` developed under `ℤ / 4`: six orbits, each a group. -/
def dev46 : Dev := ⟨0, 6, 4, fun _ => 1, base46⟩

/-- A `5`-GDD of type `12⁶` developed under `ℤ / 12`: six orbits, each a group. -/
def dev126 : Dev := ⟨0, 6, 12, fun _ => 1, base126⟩

/-- A `(557, {5, 49*})` design with a hole developed under `ℤ / 127`: the `49` fixed points are
the hole, every other point a group of its own. -/
def dev557 : Dev := ⟨49, 4, 127, fun _ => 127, base557⟩

/-- A `5`-GDD of type `7⁵² 19¹` developed under `ℤ / 91`: the `19` fixed points form a group,
and in each orbit the classes modulo `13`. -/
def dev383 : Dev := ⟨19, 4, 91, fun _ => 13, base383⟩

/-- A pairwise balanced design on `165` points with blocks of five, developed under `ℤ / 41`. -/
def dev165 : Dev := ⟨1, 4, 41, fun _ => 41, base165⟩

/-- A `(53, {5, 13*})` design with a hole: a resolvable design with blocks of four on
`40 = 1 + 3 · 13` points, developed under `ℤ / 13`, with the point `(3, t)` of the hole orbit
adjoined to every block of the parallel class `t`. -/
def dev53 : Dev := ⟨1, 4, 13, fun r => if r = 3 then 1 else 13, base53⟩

theorem dev46_check : dev46.check = true := by decide +kernel
theorem dev126_check : dev126.check = true := by decide +kernel
theorem dev557_check : dev557.check = true := by decide +kernel
theorem dev383_check : dev383.check = true := by decide +kernel
theorem dev165_check : dev165.check = true := by decide +kernel
theorem dev53_check : dev53.check = true := by decide +kernel

theorem dev46_len5 : dev46.len5 = true := by decide +kernel
theorem dev126_len5 : dev126.len5 = true := by decide +kernel
theorem dev557_len5 : dev557.len5 = true := by decide +kernel
theorem dev383_len5 : dev383.len5 = true := by decide +kernel
theorem dev165_len5 : dev165.len5 = true := by decide +kernel
theorem dev53_len5 : dev53.len5 = true := by decide +kernel

/-- The affine model `A(m; a, b, 0)`. -/
def affOp (m a b : Nat) (x y : Nat) : Nat := (a * x + b * y) % m

theorem isModel_aff {m a b : Nat} (hm : 0 < m) (h : affineOK m a b = true) :
    IsModel m (affOp m a b) := isModel_affine hm h

/-- **The order `557`**: `A(49; 18, 8, 0)` on the hole of `dev557`. -/
theorem hasPtModel_557 : HasPtModel 557 := by
  have hp := (Dev.checked_of_check dev557_check).params
  refine Dev.hasPtModel_glue5 (E := dev557) dev557_check dev557_len5
    (fun g => if g = 0 then affOp 49 18 8 else triv) (fun x hx => ?_) ⟨49, by decide, 0, ?_, ?_⟩
  · rw [Dev.gsz_grp hp hx]
    by_cases hw : x < dev557.W
    · have : dev557.gdd.grp x = 0 := by
        show (if x < dev557.W then 0 else _) = 0
        rw [ite_of_pos hw]
      rw [this, ite_of_pos hw, ite_of_pos rfl]
      change IsModel 49 (affOp 49 18 8)
      exact isModel_aff (by decide) (by decide)
    · have : dev557.gdd.grp x ≠ 0 := by
        show (if x < dev557.W then 0 else _) ≠ 0
        rw [ite_of_neg hw]
        omega
      rw [ite_of_neg this, ite_of_neg hw]
      change IsModel (127 / 127) triv
      exact isIdemModel_triv.toIsModel
  · rw [Dev.gsz_grp hp (by decide)]
    decide
  · rfl

/-- **The order `383`**: `A(19; 7, 3, 0)` on the fixed points of `dev383`, `A(7; 4, 1, 0)` on the
classes. -/
theorem hasPtModel_383 : HasPtModel 383 := by
  have hp := (Dev.checked_of_check dev383_check).params
  refine Dev.hasPtModel_glue5 (E := dev383) dev383_check dev383_len5
    (fun g => if g = 0 then affOp 19 7 3 else affOp 7 4 1) (fun x hx => ?_)
    ⟨19, by decide, 0, ?_, ?_⟩
  · rw [Dev.gsz_grp hp hx]
    by_cases hw : x < dev383.W
    · have : dev383.gdd.grp x = 0 := by
        show (if x < dev383.W then 0 else _) = 0
        rw [ite_of_pos hw]
      rw [this, ite_of_pos hw, ite_of_pos rfl]
      change IsModel 19 (affOp 19 7 3)
      exact isModel_aff (by decide) (by decide)
    · have : dev383.gdd.grp x ≠ 0 := by
        show (if x < dev383.W then 0 else _) ≠ 0
        rw [ite_of_neg hw]
        omega
      rw [ite_of_neg this, ite_of_neg hw]
      change IsModel (91 / 13) (affOp 7 4 1)
      exact isModel_aff (m := 7) (by decide) (by decide)
  · rw [Dev.gsz_grp hp (by decide)]
    decide
  · rfl

/-- **The order `53`**: `A(13; 9, 11, 0)` on the hole orbit of `dev53`, the one-point model on the
other groups. -/
theorem hasPtModel_53 : HasPtModel 53 := by
  have hp := (Dev.checked_of_check dev53_check).params
  refine Dev.hasPtModel_glue5 (E := dev53) dev53_check dev53_len5
    (fun g => if dev53.gdd.gsz g = 13 then affOp 13 9 11 else triv) (fun x hx => ?_)
    ⟨0, by decide, 0, ?_, ?_⟩
  · have hs : dev53.gdd.gsz (dev53.gdd.grp x) = 13 ∨ dev53.gdd.gsz (dev53.gdd.grp x) = 1 := by
      rw [Dev.gsz_grp hp hx]
      by_cases hw : x < dev53.W
      · rw [ite_of_pos hw]; exact Or.inr rfl
      · rw [ite_of_neg hw]
        show 13 / (if dev53.orb x = 3 then 1 else 13) = 13 ∨
          13 / (if dev53.orb x = 3 then 1 else 13) = 1
        split
        · exact Or.inl rfl
        · exact Or.inr rfl
    rcases hs with h | h
    · simp only [h, ite_true]
      exact isModel_aff (by decide) (by decide)
    · simp only [h]
      exact isIdemModel_triv.toIsModel
  · rw [Dev.gsz_grp hp (by decide)]
    decide
  · show (if dev53.gdd.gsz (dev53.gdd.grp 0) = 13 then affOp 13 9 11 else triv) 0 0 = 0
    split
    · rfl
    · rfl

/-- **The idempotent model of order `165`**, glued along `dev165`: every group is one point. -/
def op165 : Nat → Nat → Nat := dev165.gdd.glue 0 triv (fun _ => triv) (fun _ => opF5)

theorem isIdemModel_165 : IsIdemModel 165 op165 := by
  have hc := Dev.checked_of_check dev165_check
  have hp := hc.params
  have h1 : ∀ x, x < dev165.W + dev165.R * dev165.N → dev165.gdd.gsz (dev165.gdd.grp x) = 1 := by
    intro x hx
    rw [Dev.gsz_grp hp hx]
    split
    · rfl
    · change 41 / 41 = 1
      rfl
  have hok : dev165.gdd.GlueOK 0 triv (fun _ => triv) (fun _ => opF5) :=
    { valid := Dev.gdd_valid hc
      he := isModel_zero _
      hg := fun x hx => by rw [Nat.zero_add, h1 x hx]; exact isIdemModel_triv.toIsModel
      hge := fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)
      hb := fun x y h => by rw [Dev.sz_five hc dev165_len5 h]; exact isIdemModel_F5 }
  have := GDD.isModel_glue hok
  rw [Nat.zero_add] at this
  refine ⟨this, fun x hx => GDD.glue_idem_all hok (fun y hy i hi => ?_) hx⟩
  rw [Nat.zero_add, h1 y hy] at hi
  show 0 = i
  omega

/-- The block models of the run truncations: `op165`, the Paley pencil `op166`, and the
two-piece model of order `167`. -/
def bop165 (k : Nat) : Nat → Nat → Nat :=
  if k = 165 then op165 else if k = 166 then op166 else tiNat 167 (fun d => tp167Table.getD d 0)

theorem bop165_spec {k : Nat} (h1 : 165 ≤ k) (h2 : k ≤ 167) : IsIdemModel k (bop165 k) := by
  unfold bop165
  by_cases e165 : k = 165
  · subst e165; exact isIdemModel_165
  by_cases e166 : k = 166
  · subst e166; exact isIdemModel_166
  rw [show k = 167 by omega]
  exact isIdemModel_TP167

/-! ### Inflations -/

namespace GDD

variable {A B : Type} {D : GDD A} {w : Nat} {F : Nat → GDD B}

/-- A pair of points of different groups of the inflation is one of `D`, and its points in the
design on their block are of different groups there. -/
theorem inflate_cross (hD : D.Valid) (hw : 0 < w) (hF : BlockDesigns D w F) {x y : Nat}
    (h : (D.inflate w F).Cross x y) :
    D.Cross (x / w) (y / w) ∧
      (F (D.sz (D.blk (x / w) (y / w)))).Cross
        (D.idx (D.blk (x / w) (y / w)) (x / w) * w + x % w)
        (D.idx (D.blk (x / w) (y / w)) (y / w) * w + y % w) := by
  have md : ∀ {x : Nat}, x % w < w := fun {x} => Nat.mod_lt x hw
  obtain ⟨hx, hy, hg⟩ := h
  have hc : D.Cross (x / w) (y / w) :=
    ⟨(Nat.div_lt_iff_lt_mul hw).2 hx, (Nat.div_lt_iff_lt_mul hw).2 hy, hg⟩
  obtain ⟨fv, fn, fg⟩ := hF _ _ hc
  have l1 := hD.idx_lt _ _ hc
  have l2 := hD.idx_lt' _ _ hc
  refine ⟨hc, ?_, ?_, ?_⟩
  · rw [fn]; exact mul_add_lt l1 md
  · rw [fn]; exact mul_add_lt l2 md
  · rw [Ne, fg _ _ (mul_add_lt l1 md) (mul_add_lt l2 md), mul_add_div md, mul_add_div md]
    intro e
    apply hg
    rw [inflate_grp, inflate_grp]
    have := congrArg (D.pt (D.blk (x / w) (y / w))) e
    rw [hD.pt_idx _ _ hc, hD.pt_idx' _ _ hc] at this
    rw [this]

/-- The blocks of an inflation by designs with blocks of five points have five points. -/
theorem inflate_sz_five (hD : D.Valid) (hw : 0 < w) (hF : BlockDesigns D w F)
    (h5 : ∀ x y, D.Cross x y → ∀ e e', (F (D.sz (D.blk x y))).Cross e e' →
      (F (D.sz (D.blk x y))).sz ((F (D.sz (D.blk x y))).blk e e') = 5)
    {x y : Nat} (h : (D.inflate w F).Cross x y) :
    (D.inflate w F).sz ((D.inflate w F).blk x y) = 5 := by
  obtain ⟨hc, hc'⟩ := inflate_cross hD hw hF h
  rw [inflate_blk, inflate_sz]
  exact h5 _ _ hc _ _ hc'

end GDD

/-- `TD(5, x)` as a design on `5 x` points whose groups are the runs of `x` points. -/
noncomputable def gddTD5 {x : Nat} (Dx : TD 5 x) : GDD Nat := (cut3 (K := 2) Dx x x x).gdd

theorem gddTD5_valid {x : Nat} (Dx : TD 5 x) : (gddTD5 Dx).Valid :=
  Cut.gdd_valid (Cut.cut3_valid Dx (Nat.le_refl x) (Nat.le_refl x) (Nat.le_refl x))

theorem gddTD5_n {x : Nat} (Dx : TD 5 x) : (gddTD5 Dx).n = 5 * x := Cut.cut3_whole_n Dx

theorem gddTD5_sz {x : Nat} (Dx : TD 5 x) (b : Nat) : (gddTD5 Dx).sz b = 5 :=
  Cut.cut3_bsize_whole Dx _

theorem gddTD5_grp {x : Nat} (Dx : TD 5 x) {e : Nat} (he : e < 5 * x) :
    (gddTD5 Dx).grp e = e / x := Cut.cut3_whole_grp Dx (by rw [Cut.cut3_whole_n]; exact he)

/-- **`TD(5, x)` on the blocks of a design with blocks of five points.** -/
theorem blockDesigns_TD5 {A : Type} {D : GDD A} {x : Nat} (Dx : TD 5 x)
    (h5 : ∀ y z, D.Cross y z → D.sz (D.blk y z) = 5) :
    GDD.BlockDesigns D x (fun _ => gddTD5 Dx) := by
  intro y z h
  rw [h5 y z h]
  refine ⟨gddTD5_valid Dx, gddTD5_n Dx, fun e e' he he' => ?_⟩
  rw [gddTD5_grp Dx he, gddTD5_grp Dx he']

/-- The `5`-GDD of type `(4 x)⁵`: `TD(5, 4)` inflated by `TD(5, x)`. -/
noncomputable def gddE5 {x : Nat} (Dx : TD 5 x) : GDD (Nat × Nat) :=
  (gddTD5 td4).inflate x (fun _ => gddTD5 Dx)

/-- The `5`-GDD of type `(4 x)⁶`: the design `dev46` inflated by `TD(5, x)`. -/
noncomputable def gddE6 {x : Nat} (Dx : TD 5 x) : GDD (Nat × Nat) :=
  dev46.gdd.inflate x (fun _ => gddTD5 Dx)

/-- The designs on the blocks of five and six points of an inflation by the weight `4 x`. -/
noncomputable def gddW {x : Nat} (Dx : TD 5 x) (k : Nat) : GDD (Nat × Nat) :=
  if k = 5 then gddE5 Dx else gddE6 Dx

theorem gddW_sz {x : Nat} (Dx : TD 5 x) (k : Nat) (b : Nat × Nat) : (gddW Dx k).sz b = 5 := by
  unfold gddW
  split
  · exact gddTD5_sz Dx _
  · exact gddTD5_sz Dx _

theorem dev46_grp {c : Nat} : dev46.gdd.grp c = 1 + (c / 4 * 4 + 0) := by
  show (if c < 0 then 0 else 1 + ((c - 0) / 4 * 4 + (c - 0) % 4 % 1)) = _
  rw [ite_of_neg (Nat.not_lt_zero _), Nat.sub_zero, Nat.mod_one]

/-- **The designs `gddE5` and `gddE6`** on the blocks of a design with blocks of five or six
points, inflated by `4 x`. -/
theorem blockDesigns_W {A : Type} {D : GDD A} {x : Nat} (Dx : TD 5 x) (hx : 0 < x)
    (h56 : ∀ y z, D.Cross y z → D.sz (D.blk y z) = 5 ∨ D.sz (D.blk y z) = 6) :
    GDD.BlockDesigns D (4 * x) (gddW Dx) := by
  have h46 := Dev.checked_of_check dev46_check
  have v5 : (gddE5 Dx).Valid := GDD.inflate_valid (gddTD5_valid td4) hx
    (blockDesigns_TD5 Dx fun _ _ _ => gddTD5_sz td4 _)
  have v6 : (gddE6 Dx).Valid := GDD.inflate_valid (Dev.gdd_valid h46) hx
    (blockDesigns_TD5 Dx fun _ _ h => Dev.sz_five h46 dev46_len5 h)
  intro y z h
  rcases h56 y z h with e | e <;> rw [e]
  · refine ⟨v5, ?_, fun c c' hc hc' => ?_⟩
    · show (gddTD5 td4).n * x = 5 * (4 * x)
      rw [gddTD5_n]
      rw [Nat.mul_assoc]
    · show (gddTD5 td4).grp (c / x) = (gddTD5 td4).grp (c' / x) ↔ _
      have l : c / x < 5 * 4 := (Nat.div_lt_iff_lt_mul hx).2 (by rw [Nat.mul_assoc]; exact hc)
      have l' : c' / x < 5 * 4 :=
        (Nat.div_lt_iff_lt_mul hx).2 (by rw [Nat.mul_assoc]; exact hc')
      rw [gddTD5_grp td4 l, gddTD5_grp td4 l', Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
        Nat.mul_comm x 4]
  · refine ⟨v6, ?_, fun c c' _ _ => ?_⟩
    · show (0 + 6 * 4) * x = 6 * (4 * x)
      rw [Nat.zero_add, Nat.mul_assoc]
    · show dev46.gdd.grp (c / x) = dev46.gdd.grp (c' / x) ↔ _
      rw [dev46_grp, dev46_grp, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm x 4]
      omega

/-- The blocks of the master design `cut3 Dn t n n` of an inflation have five or six points. -/
theorem master_sz {n t : Nat} (Dn : TD 6 n) {y z : Nat}
    (_h : (cut3 (K := 3) Dn t n n).gdd.Cross y z) :
    (cut3 (K := 3) Dn t n n).gdd.sz ((cut3 (K := 3) Dn t n n).gdd.blk y z) = 5 ∨
      (cut3 (K := 3) Dn t n n).gdd.sz ((cut3 (K := 3) Dn t n n).gdd.blk y z) = 6 := by
  obtain ⟨-, h2, -, h4⟩ := Cut.cut3_bsize Dn t n n
    ((cut3 (K := 3) Dn t n n).lineOf ((cut3 (K := 3) Dn t n n).gdd.blk y z))
  have h5 : 5 ≤ (cut3 (K := 3) Dn t n n).bsize
      ((cut3 (K := 3) Dn t n n).lineOf ((cut3 (K := 3) Dn t n n).gdd.blk y z)) := by
    obtain ⟨k0, k1, k2⟩ := Cut.cut3_keeps Dn t n n
      ((cut3 (K := 3) Dn t n n).lineOf ((cut3 (K := 3) Dn t n n).gdd.blk y z))
    have t1 : (cut3 (K := 3) Dn t n n).keeps ((cut3 (K := 3) Dn t n n).lineOf
        ((cut3 (K := 3) Dn t n n).gdd.blk y z)) 1 = true := by
      rw [k1]; simpa using Dn.pt_lt _ 1 (by omega)
    have t2 : (cut3 (K := 3) Dn t n n).keeps ((cut3 (K := 3) Dn t n n).lineOf
        ((cut3 (K := 3) Dn t n n).gdd.blk y z)) 2 = true := by
      rw [k2]; simpa using Dn.pt_lt _ 2 (by omega)
    unfold Cut.bsize Cut.nopt
    rw [t1, t2]
    split <;> simp
  change (cut3 (K := 3) Dn t n n).bsize _ = 5 ∨ (cut3 (K := 3) Dn t n n).bsize _ = 6
  omega

/-- The groups of the master design: `t` points in group `0`, `n` in the others. -/
theorem master_gsz {n t : Nat} (Dn : TD 6 n) (g : Nat) :
    (cut3 (K := 3) Dn t n n).gdd.gsz g = if g = 0 then t else n := by
  show (cut3 (K := 3) Dn t n n).ghi g - (cut3 (K := 3) Dn t n n).glo g = _
  rw [Cut.cut3_gsz]
  by_cases g0 : g = 0
  · simp [g0]
  · simp only [g0, ite_false]
    split <;> (try split) <;> rfl

theorem master_n {n t : Nat} (Dn : TD 6 n) : (cut3 (K := 3) Dn t n n).gdd.n = 5 * n + t := by
  change (cut3 (K := 3) Dn t n n).S + 3 * n = _
  rw [Cut.cut3_S]
  omega

/-- **The inflation with `m ∈ {0, 1}` new points.** `TD(6, n)` with its group `0` cut to
`t ≤ n` points, every point given the weight `4 x` and every block replaced by `gddE5` or
`gddE6`: a `5`-GDD with five groups of `4 x n` points and one of `4 x t`. With models of orders
`m + 4 x t` and `m + 4 x n` on its groups, sharing the `m` new points, and `A(5; 2, 4, 0)` on its
blocks, it gives a pointed model of order `m + (5 n + t) 4 x`. -/
theorem hasPtModel_inflate {x n t m : Nat} (Dx : TD 5 x) (Dn : TD 6 n) (ht : t ≤ n)
    (hx : 0 < x) (hn : 0 < n) {emod opT opN : Nat → Nat → Nat} (he : IsModel m emod)
    (hT : IsModel (m + t * (4 * x)) opT) (hN : IsModel (m + n * (4 * x)) opN)
    (hTe : ∀ a b, a < m → b < m → opT a b = emod a b)
    (hNe : ∀ a b, a < m → b < m → opN a b = emod a b)
    (hpt : (∃ e, e < m ∧ emod e e = e) ∨ ∃ e, e < m + n * (4 * x) ∧ opN e e = e) :
    HasPtModel (m + (5 * n + t) * (4 * x)) := by
  have hM := Cut.cut3_valid (K := 3) Dn ht (Nat.le_refl n) (Nat.le_refl n)
  have hMv := Cut.gdd_valid hM
  have hw : 0 < 4 * x := by omega
  have hBD := blockDesigns_W (D := (cut3 (K := 3) Dn t n n).gdd) Dx hx (fun _ _ h => master_sz Dn h)
  have hI := GDD.inflate_valid hMv hw hBD
  let gmod : Nat → Nat → Nat → Nat := fun g => if g = 0 then opT else opN
  have hok : ((cut3 (K := 3) Dn t n n).gdd.inflate (4 * x) (gddW Dx)).GlueOK m emod gmod
      (fun _ => opF5) :=
    { valid := hI
      he := he
      hg := fun y _ => by
        change IsModel (m + (cut3 (K := 3) Dn t n n).gdd.gsz _ * (4 * x)) (gmod _)
        rw [master_gsz]
        by_cases g0 : (cut3 (K := 3) Dn t n n).gdd.grp (y / (4 * x)) = 0
        · simp only [gmod, GDD.inflate_grp, g0, ite_true]; exact hT
        · simp only [gmod, GDD.inflate_grp, g0, ite_false]; exact hN
      hge := fun y _ a b ha hb => by
        by_cases g0 : (cut3 (K := 3) Dn t n n).gdd.grp (y / (4 * x)) = 0
        · simp only [gmod, GDD.inflate_grp, g0, ite_true]; exact hTe a b ha hb
        · simp only [gmod, GDD.inflate_grp, g0, ite_false]; exact hNe a b ha hb
      hb := fun y z h => by
        rw [GDD.inflate_sz_five hMv hw hBD (fun _ _ _ _ _ _ => gddW_sz Dx _ _) h]
        exact isIdemModel_F5 }
  have hn' : ((cut3 (K := 3) Dn t n n).gdd.inflate (4 * x) (gddW Dx)).n =
      (5 * n + t) * (4 * x) := by
    rw [GDD.inflate_n, master_n]
  rw [← hn']
  refine GDD.hasPtModel_glue hok ?_
  rcases hpt with h | ⟨e, he', hee⟩
  · exact Or.inr (Or.inl h)
  · obtain ⟨xM, hxM, hg3, -⟩ := Cut.gdd_whole_pt (T := cut3 (K := 3) Dn t n n) hM (by decide) hn
    refine Or.inr (Or.inr ⟨xM * (4 * x), ?_, e, ?_, ?_⟩)
    · rw [GDD.inflate_n]
      exact Nat.mul_lt_mul_of_pos_right hxM hw
    · change e < m + (cut3 (K := 3) Dn t n n).gdd.gsz
        ((cut3 (K := 3) Dn t n n).gdd.grp (xM * (4 * x) / (4 * x))) * (4 * x)
      rw [Nat.mul_div_cancel _ hw, hg3, master_gsz]
      exact he'
    · show (if (cut3 (K := 3) Dn t n n).gdd.grp (xM * (4 * x) / (4 * x)) = 0 then opT else opN)
        e e = e
      rw [Nat.mul_div_cancel _ hw, hg3]
      exact hee

/-- **The inflation**: pointed models of orders `4 x n` and `4 x t` give one of order
`(5 n + t) 4 x`, from `TD(5, x)`, `TD(6, n)` and `t ≤ n`. -/
theorem hasPtModel_infl {x n t : Nat} (Dx : TD 5 x) (Dn : TD 6 n) (ht : t ≤ n)
    (Hn : HasPtModel (4 * x * n)) (Ht : HasPtModel (4 * x * t)) :
    HasPtModel ((5 * n + t) * (4 * x)) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · exact hasPtModel_zero
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show t = 0 by omega, show (5 * 0 + 0) * (4 * x) = 0 by simp]; exact hasPtModel_zero
  obtain ⟨opN, HN, eN⟩ := Hn
  obtain ⟨opT, HT, -⟩ := Ht
  obtain ⟨e, he, hee⟩ := eN.resolve_left (Nat.ne_of_gt (Nat.mul_pos (by omega) hn))
  have := hasPtModel_inflate (m := 0) Dx Dn ht hx hn (emod := triv) (opT := opT) (opN := opN)
    (isModel_zero _) (by rwa [Nat.zero_add, Nat.mul_comm]) (by rwa [Nat.zero_add, Nat.mul_comm])
    (fun _ _ h => absurd h (Nat.not_lt_zero _)) (fun _ _ h => absurd h (Nat.not_lt_zero _))
    (Or.inr ⟨e, by rw [Nat.zero_add, Nat.mul_comm]; exact he, hee⟩)
  rwa [Nat.zero_add] at this

/-- **The inflation with a point at infinity**: pointed models of orders `4 x n + 1` and
`4 x t + 1` give one of order `1 + (5 n + t) 4 x`. -/
theorem hasPtModel_iinfl {x n t : Nat} (Dx : TD 5 x) (Dn : TD 6 n) (ht : t ≤ n)
    (Hn : HasPtModel (4 * x * n + 1)) (Ht : HasPtModel (4 * x * t + 1)) :
    HasPtModel (1 + (5 * n + t) * (4 * x)) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · exact hasPtModel_one
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show t = 0 by omega, show 1 + (5 * 0 + 0) * (4 * x) = 1 by simp]; exact hasPtModel_one
  obtain ⟨opN, HN, hN0⟩ := exists_idem_zero Hn (by omega)
  obtain ⟨opT, HT, hT0⟩ := exists_idem_zero Ht (by omega)
  have e0 : ∀ {op : Nat → Nat → Nat}, op 0 0 = 0 → ∀ a b, a < 1 → b < 1 → op a b = triv a b := by
    intro op h a b ha hb
    rw [show a = 0 by omega, show b = 0 by omega, h]; rfl
  exact hasPtModel_inflate (m := 1) Dx Dn ht hx hn (emod := triv) (opT := opT) (opN := opN)
    isIdemModel_triv.toIsModel (by rwa [Nat.add_comm, Nat.mul_comm])
    (by rwa [Nat.add_comm, Nat.mul_comm]) (e0 hT0) (e0 hN0) (Or.inl ⟨0, by decide, rfl⟩)

/-! ### The orders `337` and `360` -/

/-- `TD(6, 5)`: the cyclic plane over `ℤ / 5`. -/
noncomputable def td65 : TD 6 5 :=
  cyclicPlane 5 5 fun d h0 h => by
    rcases (show d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 by omega) with rfl | rfl | rfl | rfl <;> decide

/-- The designs on the blocks of the inflation of `337`: `TD(5, 12)` and `dev126`. -/
noncomputable def gdd337 (k : Nat) : GDD Nat := if k = 5 then gddTD5 td12 else dev126.gdd

theorem dev126_grp {c : Nat} : dev126.gdd.grp c = 1 + (c / 12 * 12 + 0) := by
  show (if c < 0 then 0 else 1 + ((c - 0) / 12 * 12 + (c - 0) % 12 % 1)) = _
  rw [ite_of_neg (Nat.not_lt_zero _), Nat.sub_zero, Nat.mod_one]

/-- **The order `337 = 1 + (5 · 5 + 3) · 12`**: `TD(6, 5)` with a group cut to `3` points,
inflated by the weight `12` with `TD(5, 12)` and the `5`-GDD of type `12⁶` on its blocks, and a
point at infinity: `A(37; 26, 2, 0)` and `A(61; 59, 3, 0)` on its groups. -/
theorem hasPtModel_337 : HasPtModel 337 := by
  have hM := Cut.cut3_valid (K := 3) td65 (show 3 ≤ 5 by decide) (Nat.le_refl 5) (Nat.le_refl 5)
  have hMv := Cut.gdd_valid hM
  have h126 := Dev.checked_of_check dev126_check
  have hBD : GDD.BlockDesigns (cut3 (K := 3) td65 3 5 5).gdd 12 gdd337 := by
    intro y z h
    rcases master_sz td65 h with e | e <;> rw [e]
    · refine ⟨gddTD5_valid td12, gddTD5_n td12, fun c c' hc hc' => ?_⟩
      show (gddTD5 td12).grp c = (gddTD5 td12).grp c' ↔ _
      rw [gddTD5_grp td12 hc, gddTD5_grp td12 hc']
    · refine ⟨Dev.gdd_valid h126, rfl, fun c c' _ _ => ?_⟩
      show dev126.gdd.grp c = dev126.gdd.grp c' ↔ _
      rw [dev126_grp, dev126_grp]
      omega
  have hI := GDD.inflate_valid hMv (by decide) hBD
  have e0 : ∀ {op : Nat → Nat → Nat}, op 0 0 = 0 → ∀ a b, a < 1 → b < 1 → op a b = triv a b := by
    intro op h a b ha hb
    rw [show a = 0 by omega, show b = 0 by omega, h]; rfl
  let gmod : Nat → Nat → Nat → Nat := fun g => if g = 0 then affOp 37 26 2 else affOp 61 59 3
  have hok : ((cut3 (K := 3) td65 3 5 5).gdd.inflate 12 gdd337).GlueOK 1 triv gmod
      (fun _ => opF5) :=
    { valid := hI
      he := isIdemModel_triv.toIsModel
      hg := fun y _ => by
        change IsModel (1 + (cut3 (K := 3) td65 3 5 5).gdd.gsz _ * 12) (gmod _)
        rw [master_gsz]
        by_cases g0 : (cut3 (K := 3) td65 3 5 5).gdd.grp (y / 12) = 0
        · simp only [gmod, GDD.inflate_grp, g0, ite_true]
          exact isModel_aff (by decide) (by decide)
        · simp only [gmod, GDD.inflate_grp, g0, ite_false]
          exact isModel_aff (by decide) (by decide)
      hge := fun y _ a b ha hb => by
        by_cases g0 : (cut3 (K := 3) td65 3 5 5).gdd.grp (y / 12) = 0
        · simp only [gmod, GDD.inflate_grp, g0, ite_true]; exact e0 rfl a b ha hb
        · simp only [gmod, GDD.inflate_grp, g0, ite_false]; exact e0 rfl a b ha hb
      hb := fun y z h => by
        rw [GDD.inflate_sz_five hMv (by decide) hBD (fun y' z' h' e e' he => ?_) h]
        · exact isIdemModel_F5
        · rcases master_sz td65 h' with k | k <;> rw [k] at he ⊢
          · exact gddTD5_sz td12 _
          · have hk : gdd337 6 = dev126.gdd := rfl
            rw [hk] at he ⊢
            exact Dev.sz_five h126 dev126_len5 he }
  have := GDD.hasPtModel_glue hok (Or.inr (Or.inl ⟨0, by decide, rfl⟩))
  rwa [GDD.inflate_n, master_n] at this

/-- `TD(5, 71)`: the cyclic plane over `ℤ / 71`. -/
noncomputable def td71 : TD 5 71 :=
  cyclicPlane 71 4 fun d h0 h => by
    rcases (show d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl <;> decide

/-- **The order `360 = 5 + 5 · 71`**: the submagma of `5` points of the census model of order
`76` adjoined to the five groups of `TD(5, 71)`. -/
theorem hasPtModel_360 : HasPtModel 360 := by
  have hE : IsModel 5 op76 :=
    ⟨fun a b ha hb => op76_sub a b ha hb,
      fun a b ha hb => isIdemModel_76.eq a b (by omega) (by omega)⟩
  have h76 : IsModel (5 + 71) op76 := isIdemModel_76.toIsModel
  have hrfl : ∀ a b, a < 5 → b < 5 → op76 a b = op76 a b := fun _ _ _ _ => rfl
  have := hasPtModel_cut3 (K := 2) (m := 5) td71 (Nat.le_refl 71) (Nat.le_refl 71) (Nat.le_refl 71)
    (emod := op76) (opa := op76) (opb := op76) (opc := op76) (opq := op76)
    (bmod := fun _ => opF5) hE h76 h76 h76 h76 hrfl hrfl hrfl hrfl
    (fun L => by rw [Cut.cut3_bsize_whole]; exact isIdemModel_F5)
    (Or.inl ⟨0, by decide, isIdemModel_76.idem 0 (by decide)⟩)
  exact this

/- The checks below are only ever evaluated by the kernel, and `List.rec` has no compiled
code in core Lean. -/
noncomputable section

namespace OrderBitmap

/-! ## Bitmaps of orders -/

/-- A bitmap is **sound** when each of its set bits is the size of a pointed model. -/
def Sound (B : Nat) : Prop := ∀ n, B.testBit n = true → HasPtModel n

theorem Sound.or {A B : Nat} (hA : Sound A) (hB : Sound B) : Sound (A ||| B) := by
  intro n h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  exact h.elim (hA n) (hB n)

theorem sound_single {n : Nat} (h : HasPtModel n) : Sound (1 <<< n) := by
  intro m hm
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hm
  exact hm ▸ h

/-- **A list of orders that all carry pointed models** gives a sound bitmap. -/
theorem sound_foldr {l : List Nat} (h : ∀ n ∈ l, HasPtModel n) :
    Sound (l.foldr (fun n B => B ||| 1 <<< n) 0) := by
  induction l with
  | nil => intro n hn; simp at hn
  | cons n l ih =>
    simp only [List.foldr_cons]
    exact (ih fun m hm => h m (List.Mem.tail _ hm)).or (sound_single (h n (List.Mem.head _)))

/-- Evaluate `a` and continue with it. The test is decided by evaluating `a`, so in a kernel
reduction `forceThen a k` evaluates `a` before `k` runs; the loops below use it to keep their
accumulators evaluated. -/
def forceThen (a : Nat) (k : Nat → Nat) : Nat := if a == 0 then k 0 else k a

theorem forceThen_eq (a : Nat) (k : Nat → Nat) : forceThen a k = k a := by
  unfold forceThen
  split
  · rename_i h
    rw [beq_iff_eq] at h
    rw [h]
  · rfl

/-! ### Bitmaps read relative to a base point -/

/-- A bitmap read relative to `a` is sound when each set bit `i` is the size `a + i` of a
pointed model. -/
def WSound (a A : Nat) : Prop := ∀ i, A.testBit i = true → HasPtModel (a + i)

theorem WSound.or {a A B : Nat} (hA : WSound a A) (hB : WSound a B) : WSound a (A ||| B) := by
  intro n h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  exact h.elim (hA n) (hB n)

theorem wsound_zero (a : Nat) : WSound a 0 := fun i h => by simp at h

theorem wsound_single {a n : Nat} (h : HasPtModel n) (han : a ≤ n) :
    WSound a (1 <<< (n - a)) := by
  intro i hi
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hi
  rwa [show a + i = n by omega]

theorem Sound.wsound_shiftRight {B : Nat} (hB : Sound B) (a L : Nat) :
    WSound a ((B >>> a) % 2 ^ L) := by
  intro i hi
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Bool.and_eq_true] at hi
  exact hB _ hi.2

/-- Place the bits `B`, standing for the orders `base + r`, relative to `a`. -/
def placeAt (B base a : Nat) : Nat := if a ≤ base then B <<< (base - a) else B >>> (a - base)

theorem testBit_placeAt {B base a i : Nat} (h : (placeAt B base a).testBit i = true) :
    base ≤ a + i ∧ B.testBit (a + i - base) = true := by
  unfold placeAt at h
  by_cases hab : a ≤ base
  · rw [ite_of_pos hab, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨by omega, by rwa [show a + i - base = i - (base - a) by omega]⟩
  · rw [ite_of_neg hab, Nat.testBit_shiftRight] at h
    exact ⟨by omega, by rwa [show a + i - base = a - base + i by omega]⟩

/-! ### Packed instructions -/

/-- A single order `v`, recorded when `ok` holds, read relative to `a`. -/
def single (ok : Bool) (a v : Nat) : Nat := if ok && decide (a ≤ v) then 1 <<< (v - a) else 0

theorem wsound_single' {ok : Bool} {a v : Nat} (h : ok = true → HasPtModel v) :
    WSound a (single ok a v) := by
  unfold single
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact wsound_single (h hc.1) hc.2
  · exact wsound_zero a

/-- **The two-group truncation `(q, s)`, read relative to `a`.** Let `hq` be the bits of `P`
up to `q`. If `tdOK q` holds, `s ≤ q`, and the orders `q` and `s` are recorded, the result
records `79 q + s + r` for every recorded `r ≤ q`; otherwise it is empty. -/
def truncImage (P a q s : Nat) : Nat :=
  let hq := P % 2 ^ (q + 1)
  if tdOK q && decide (s ≤ q) && hq.testBit q && hq.testBit s then placeAt hq (79 * q + s) a
  else 0

theorem wsound_truncImage {P : Nat} (hP : Sound P) (a q s : Nat) :
    WSound a (truncImage P a q s) := by
  intro i hi
  unfold truncImage at hi
  dsimp only at hi
  by_cases ht : (tdOK q && decide (s ≤ q) && (P % 2 ^ (q + 1)).testBit q &&
      (P % 2 ^ (q + 1)).testBit s) = true
  · rw [ite_of_pos ht] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_mod_two_pow] at ht
    obtain ⟨⟨⟨hg, hsq⟩, -, hq⟩, -, hs⟩ := ht
    obtain ⟨hle, hbit⟩ := testBit_placeAt hi
    simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hbit
    obtain ⟨hlt, hbit⟩ := hbit
    obtain ⟨D⟩ := td_of_tdOK hg
    have := hasPtModel_two D hsq (by omega : a + i - (79 * q + s) ≤ q) (hP q hq) (hP s hs)
      (hP _ hbit)
    rwa [show 79 * q + s + (a + i - (79 * q + s)) = a + i by omega] at this
  · rw [ite_of_neg ht] at hi
    simp at hi

/-- **The run truncation `(q, s)`, read relative to `a`**: as `truncImage`, with `tdOK167` and
`165 q + s + r`. -/
def runImage (P a q s : Nat) : Nat :=
  let hq := P % 2 ^ (q + 1)
  if tdOK167 q && decide (s ≤ q) && hq.testBit q && hq.testBit s then placeAt hq (165 * q + s) a
  else 0

theorem wsound_runImage {P : Nat} (hP : Sound P) (a q s : Nat) :
    WSound a (runImage P a q s) := by
  intro i hi
  unfold runImage at hi
  dsimp only at hi
  by_cases ht : (tdOK167 q && decide (s ≤ q) && (P % 2 ^ (q + 1)).testBit q &&
      (P % 2 ^ (q + 1)).testBit s) = true
  · rw [ite_of_pos ht] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_mod_two_pow] at ht
    obtain ⟨⟨⟨hg, hsq⟩, -, hq⟩, -, hs⟩ := ht
    obtain ⟨hle, hbit⟩ := testBit_placeAt hi
    simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hbit
    obtain ⟨hlt, hbit⟩ := hbit
    obtain ⟨D⟩ := td_of_tdOK167 hg
    have := hasPtModel_run (fun _ h1 h2 => bop165_spec h1 h2) D hsq
      (by omega : a + i - (165 * q + s) ≤ q) (hP q hq) (hP s hs) (hP _ hbit)
    rwa [show 165 * q + s + (a + i - (165 * q + s)) = a + i by omega] at this
  · rw [ite_of_neg ht] at hi
    simp at hi

/-- **The two-group truncation with a point at infinity `(q, s)`, read relative to `a`.** Let
`hq` be the bits of `P` up to `q + 1`. If `tdOK q` holds, `s ≤ q`, and the orders `q + 1` and
`s + 1` are recorded, the result records `1 + 79 q + s + r` for every `r ≤ q` with `r + 1`
recorded; otherwise it is empty. -/
def infTruncImage (P a q s : Nat) : Nat :=
  let hq := P % 2 ^ (q + 2)
  if tdOK q && decide (s ≤ q) && hq.testBit (q + 1) && hq.testBit (s + 1) then
    placeAt (hq >>> 1) (1 + 79 * q + s) a
  else 0

theorem wsound_infTruncImage {P : Nat} (hP : Sound P) (a q s : Nat) :
    WSound a (infTruncImage P a q s) := by
  intro i hi
  unfold infTruncImage at hi
  dsimp only at hi
  by_cases ht : (tdOK q && decide (s ≤ q) && (P % 2 ^ (q + 2)).testBit (q + 1) &&
      (P % 2 ^ (q + 2)).testBit (s + 1)) = true
  · rw [ite_of_pos ht] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_mod_two_pow] at ht
    obtain ⟨⟨⟨hg, hsq⟩, -, hq⟩, -, hs⟩ := ht
    obtain ⟨hle, hbit⟩ := testBit_placeAt hi
    simp only [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Bool.and_eq_true,
      decide_eq_true_eq] at hbit
    obtain ⟨hlt, hbit⟩ := hbit
    obtain ⟨D⟩ := td_of_tdOK hg
    have := hasPtModel_inftrunc D hsq (by omega : a + i - (1 + 79 * q + s) ≤ q) (hP _ hq)
      (hP _ hs) (hP _ (by rwa [Nat.add_comm] at hbit))
    rwa [show 1 + 79 * q + s + (a + i - (1 + 79 * q + s)) = a + i by omega] at this
  · rw [ite_of_neg ht] at hi
    simp at hi

/-- The side conditions of the keep truncation `(q, s₁, s₂)`, shared by the keep
truncation adjoined at a cut group: `q` is coprime to `P79`, and the orders `q`, `s₁ ≤ q` and
`s₂ ≤ q` are recorded among the bits `hq` of `P` up to `q`. -/
def tripleOK (hq q s₁ s₂ : Nat) : Bool :=
  Nat.gcd q P79 == 1 && decide (s₁ ≤ q) && decide (s₂ ≤ q) && hq.testBit q && hq.testBit s₁ &&
    hq.testBit s₂

theorem of_tripleOK {P q s₁ s₂ : Nat} (hP : Sound P)
    (h : tripleOK (P % 2 ^ (q + 1)) q s₁ s₂ = true) :
    Nat.gcd q P79 = 1 ∧ s₁ ≤ q ∧ s₂ ≤ q ∧ HasPtModel q ∧ HasPtModel s₁ ∧ HasPtModel s₂ := by
  simp only [tripleOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Nat.testBit_mod_two_pow] at h
  obtain ⟨⟨⟨⟨⟨hg, h₁⟩, h₂⟩, ⟨-, hq⟩⟩, ⟨-, hs₁⟩⟩, ⟨-, hs₂⟩⟩ := h
  exact ⟨hg, h₁, h₂, hP _ hq, hP _ hs₁, hP _ hs₂⟩

/-- **The keep truncation `(q, s₁, s₂)`, read relative to `a`.** If `tripleOK` holds and
`s₁ + s₂ ≤ q + 1`, the result records `79 q + s₁ + s₂ + r` for every recorded `r ≤ q` with
`s₁ + s₂ + r ≤ q + 1`; otherwise it is empty. -/
def keepImage (P a q s₁ s₂ : Nat) : Nat :=
  let hq := P % 2 ^ (q + 1)
  if tripleOK hq q s₁ s₂ && decide (s₁ + s₂ ≤ q + 1) then
    placeAt (hq % 2 ^ (q + 2 - (s₁ + s₂))) (79 * q + s₁ + s₂) a
  else 0

theorem wsound_keepImage {P : Nat} (hP : Sound P) (a q s₁ s₂ : Nat) :
    WSound a (keepImage P a q s₁ s₂) := by
  intro i hi
  unfold keepImage at hi
  dsimp only at hi
  by_cases ht : (tripleOK (P % 2 ^ (q + 1)) q s₁ s₂ && decide (s₁ + s₂ ≤ q + 1)) = true
  · rw [ite_of_pos ht] at hi
    rw [Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨hg, h₁, h₂, hq, hm₁, hm₂⟩ := of_tripleOK hP ht.1
    obtain ⟨hle, hbit⟩ := testBit_placeAt hi
    simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hbit
    obtain ⟨hlt, hlt', hbit⟩ := hbit
    have := hasPtModel_keep hg h₁ h₂ (by omega : a + i - (79 * q + s₁ + s₂) ≤ q) (by omega) hq
      hm₁ hm₂ (hP _ hbit)
    rwa [show 79 * q + s₁ + s₂ + (a + i - (79 * q + s₁ + s₂)) = a + i by omega] at this
  · rw [ite_of_neg ht] at hi
    simp at hi

/-- Clearing bit `0`: the bits of `B` at the positions `j ≥ 1`. -/
theorem testBit_clear0 {B j : Nat} (h : ((B >>> 1) <<< 1).testBit j = true) :
    1 ≤ j ∧ B.testBit j = true := by
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_shiftRight] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, by rwa [show 1 + (j - 1) = j by omega] at h2⟩

/-- **A two-group truncation adjoined at a cut group, `(q, r)`, read relative to `a`.** If
`tdOK q` holds, `r ≤ q`, the orders `q` and `r` are recorded and `tdOK5 (79 q + r)` holds, the
result records `5 (79 q + r) + s` for every recorded `s` with `1 ≤ s ≤ q`
(`Spectrum677.hasPtModel_subTwo`); otherwise it is empty. -/
def subTwoImage (P a q r : Nat) : Nat :=
  let hq := P % 2 ^ (q + 1)
  if tdOK q && decide (r ≤ q) && hq.testBit q && hq.testBit r && tdOK5 (79 * q + r) then
    placeAt ((hq >>> 1) <<< 1) (5 * (79 * q + r)) a
  else 0

theorem wsound_subTwoImage {P : Nat} (hP : Sound P) (a q r : Nat) :
    WSound a (subTwoImage P a q r) := by
  intro i hi
  unfold subTwoImage at hi
  dsimp only at hi
  by_cases ht : (tdOK q && decide (r ≤ q) && (P % 2 ^ (q + 1)).testBit q &&
      (P % 2 ^ (q + 1)).testBit r && tdOK5 (79 * q + r)) = true
  · rw [ite_of_pos ht] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_mod_two_pow] at ht
    obtain ⟨⟨⟨⟨hg, hrq⟩, -, hq⟩, -, hr⟩, h5⟩ := ht
    obtain ⟨hle, hbit⟩ := testBit_placeAt hi
    obtain ⟨h1, hbit⟩ := testBit_clear0 hbit
    simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hbit
    obtain ⟨hlt, hbit⟩ := hbit
    obtain ⟨D⟩ := td_of_tdOK hg
    obtain ⟨D5⟩ := td5_of_tdOK5 h5
    have := hasPtModel_sub2 D D5 h1 (by omega : a + i - 5 * (79 * q + r) ≤ q) hrq (hP q hq)
      (hP _ hbit) (hP r hr)
    rwa [show 5 * (79 * q + r) + (a + i - 5 * (79 * q + r)) = a + i by omega] at this
  · rw [ite_of_neg ht] at hi
    simp at hi

/-- **A keep truncation adjoined at a cut group, `(q, s₂, s₃)`, read relative to `a`.** If
`tripleOK` holds, `s₂ + s₃ ≤ q + 1` and `tdOK5 (79 q + s₂ + s₃)` holds, the result records
`5 (79 q + s₂ + s₃) + s₁` for every recorded `s₁` with `1 ≤ s₁ ≤ q` and
`s₁ + s₂ + s₃ ≤ q + 1` (`Spectrum677.hasPtModel_subKeep`); otherwise it is empty. -/
def subKeepImage (P a q s₂ s₃ : Nat) : Nat :=
  let hq := P % 2 ^ (q + 1)
  if tripleOK hq q s₂ s₃ && decide (s₂ + s₃ ≤ q + 1) && tdOK5 (79 * q + s₂ + s₃) then
    placeAt (((hq % 2 ^ (q + 2 - (s₂ + s₃))) >>> 1) <<< 1) (5 * (79 * q + s₂ + s₃)) a
  else 0

theorem wsound_subKeepImage {P : Nat} (hP : Sound P) (a q s₂ s₃ : Nat) :
    WSound a (subKeepImage P a q s₂ s₃) := by
  intro i hi
  unfold subKeepImage at hi
  dsimp only at hi
  by_cases ht : (tripleOK (P % 2 ^ (q + 1)) q s₂ s₃ && decide (s₂ + s₃ ≤ q + 1) &&
      tdOK5 (79 * q + s₂ + s₃)) = true
  · rw [ite_of_pos ht] at hi
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨htr, hsum⟩, h5⟩ := ht
    obtain ⟨hg, h₂, h₃, hq, hm₂, hm₃⟩ := of_tripleOK hP htr
    obtain ⟨hle, hbit⟩ := testBit_placeAt hi
    obtain ⟨h1, hbit⟩ := testBit_clear0 hbit
    simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hbit
    obtain ⟨hlt, hlt', hbit⟩ := hbit
    obtain ⟨D5⟩ := td5_of_tdOK5 h5
    have := hasPtModel_subk hg D5 h1 (by omega : a + i - 5 * (79 * q + s₂ + s₃) ≤ q) h₂ h₃
      (by omega) hq (hP _ hbit) hm₂ hm₃
    rwa [show 5 * (79 * q + s₂ + s₃) + (a + i - 5 * (79 * q + s₂ + s₃)) = a + i by omega] at this
  · rw [ite_of_neg ht] at hi
    simp at hi

/-- The instructions with tags from `7` on: a point at infinity, the two-group truncation with a
point at infinity, the two inflations and the run truncation. -/
def highImage (P a t x y z : Nat) : Nat :=
  if t == 7 then single (tdOK5 x && P.testBit (x + 1)) a (1 + 5 * x)
  else if t == 8 then infTruncImage P a x y
  else if t == 9 then
    single (tdOK5 x && tdOK6 y && decide (z ≤ y) && P.testBit (4 * x * y) &&
      P.testBit (4 * x * z)) a ((5 * y + z) * (4 * x))
  else if t == 10 then
    single (tdOK5 x && tdOK6 y && decide (z ≤ y) && P.testBit (4 * x * y + 1) &&
      P.testBit (4 * x * z + 1)) a (1 + (5 * y + z) * (4 * x))
  else if t == 11 then runImage P a x y
  else 0

theorem wsound_highImage {P : Nat} (hP : Sound P) (a t x y z : Nat) :
    WSound a (highImage P a t x y z) := by
  unfold highImage
  split
  · refine wsound_single' fun h => ?_
    simp only [Bool.and_eq_true] at h
    obtain ⟨D⟩ := td5_of_tdOK5 h.1
    exact hasPtModel_inf D (hP _ h.2)
  split
  · exact wsound_infTruncImage hP a _ _
  split
  · refine wsound_single' fun h => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h5, h6⟩, ht⟩, hn⟩, htt⟩ := h
    obtain ⟨Dx⟩ := td5_of_tdOK5 h5
    obtain ⟨Dn⟩ := td_of_tdOK6 h6
    exact hasPtModel_infl Dx Dn ht (hP _ hn) (hP _ htt)
  split
  · refine wsound_single' fun h => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h5, h6⟩, ht⟩, hn⟩, htt⟩ := h
    obtain ⟨Dx⟩ := td5_of_tdOK5 h5
    obtain ⟨Dn⟩ := td_of_tdOK6 h6
    exact hasPtModel_iinfl Dx Dn ht (hP _ hn) (hP _ htt)
  split
  · exact wsound_runImage hP a _ _
  · exact wsound_zero a

/-- **One packed instruction, read from `P` and placed relative to `a`.** The low four bits are
a tag and three 18-bit fields `x`, `y`, `z` follow. Tag `0`: the affine certificate with modulus
`x` and coefficients `y`, `z`. Tag `1`: the product of the recorded orders `x` and `y`. Tag `2`:
the two-group truncation `(q, s) = (x, y)`. Tag `3`: the keep truncation
`(q, s₁, s₂) = (x, y, z)`. Tag `4`: the Paley pencil over `ℤ / 11`, recording `11 x + 1` when
`x + 1` is recorded. Tags `5` and `6`: a two-group truncation `(q, r) = (x, y)` and a keep
truncation `(q, s₂, s₃) = (x, y, z)` adjoined at a cut group. Tag `7`: a point at infinity,
recording `1 + 5 x` when `TD(5, x)` exists and `x + 1` is recorded. Tag `8`: the two-group
truncation with a point at infinity `(q, s) = (x, y)`. Tags `9` and `10`: the inflations
`(x, n, t) = (x, y, z)`, recording `(5 n + t) 4 x` from `4 x n` and `4 x t`, and
`1 + (5 n + t) 4 x` from `4 x n + 1` and `4 x t + 1`, when `TD(5, x)` and `TD(6, n)` exist and
`t ≤ n`. Tag `11`: the run truncation `(q, s) = (x, y)`. Anything else, or a failed side
condition, gives the empty bitmap; so does a single order below `a`, and of a range of orders
only those from `a` on are kept. -/
def opImage (P a op : Nat) : Nat :=
  let t := op % 16
  let x := (op >>> 4) % 2 ^ 18
  let y := (op >>> 22) % 2 ^ 18
  let z := (op >>> 40) % 2 ^ 18
  if t == 0 then single (affineOK x y z) a x
  else if t == 1 then single (P.testBit x && P.testBit y) a (x * y)
  else if t == 2 then truncImage P a x y
  else if t == 3 then keepImage P a x y z
  else if t == 4 then single (P.testBit (x + 1)) a (11 * x + 1)
  else if t == 5 then subTwoImage P a x y
  else if t == 6 then subKeepImage P a x y z
  else highImage P a t x y z

theorem wsound_opImage {P : Nat} (hP : Sound P) (a op : Nat) : WSound a (opImage P a op) := by
  unfold opImage
  dsimp only
  split
  · exact wsound_single' hasPtModel_of_affineOK
  split
  · refine wsound_single' fun h => ?_
    simp only [Bool.and_eq_true] at h
    exact (hP _ h.1).mul (hP _ h.2)
  split
  · exact wsound_truncImage hP a _ _
  split
  · exact wsound_keepImage hP a _ _ _
  split
  · exact wsound_single' fun h => hasPtModel_paley paleyOK_11 (hP _ h)
  split
  · exact wsound_subTwoImage hP a _ _
  split
  · exact wsound_subKeepImage hP a _ _ _
  · exact wsound_highImage hP a _ _ _ _

/-- **Accumulate the images of a list of instructions**, read from `P` and placed relative to
`a`, keeping the accumulator evaluated between instructions. -/
def blockAcc (P a : Nat) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun op _ ih acc => forceThen acc fun acc => ih (acc ||| opImage P a op))

theorem wsound_blockAcc {P : Nat} (hP : Sound P) (a : Nat) :
    ∀ (ops : List Nat) {acc : Nat}, WSound a acc → WSound a (blockAcc P a ops acc)
  | [], _, h => h
  | op :: ops, acc, h => by
    change WSound a (forceThen acc fun acc => blockAcc P a ops (acc ||| opImage P a op))
    rw [forceThen_eq]
    exact wsound_blockAcc hP a ops (h.or (wsound_opImage hP a op))

/-! ### Two kinds of check -/

/-- **A block of a bitmap is produced from below.** The bits of `H` in `[a, a + L)` all
appear among the bits of `seeds` there and the images of `ops` read from the bits of `H` below
`a`. -/
def blockOK (seeds H a L : Nat) (ops : List Nat) : Bool :=
  (H >>> a) % 2 ^ L &&& blockAcc (H % 2 ^ a) a ops ((seeds >>> a) % 2 ^ L) ==
    (H >>> a) % 2 ^ L

/-- **Soundness grows by a block.** -/
theorem Sound.mod_add {seeds H a L : Nat} {ops : List Nat} (hs : Sound seeds)
    (hP : Sound (H % 2 ^ a)) (h : blockOK seeds H a L ops = true) :
    Sound (H % 2 ^ (a + L)) := by
  intro n hn
  rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hn
  by_cases hna : n < a
  · exact hP n (by rw [Nat.testBit_mod_two_pow]; simp [hna, hn.2])
  have hacc := wsound_blockAcc hP a ops (hs.wsound_shiftRight a L)
  rw [blockOK, beq_iff_eq] at h
  have hb := congrArg (fun x => Nat.testBit x (n - a)) h
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    show n - a < L by omega, show a + (n - a) = n by omega, hn.2, decide_true,
    Bool.true_and] at hb
  have := hacc (n - a) hb
  rwa [show a + (n - a) = n by omega] at this

/-- **An interval above a sound bitmap is covered.** Every size in `[a, a + L)` is recorded
by the images of `ops` read from `H`. -/
def coverOK (H a L : Nat) (ops : List Nat) : Bool :=
  blockAcc H a ops 0 % 2 ^ L == 2 ^ L - 1

theorem hasPtModel_of_coverOK {H a L : Nat} {ops : List Nat} (hH : Sound H)
    (h : coverOK H a L ops = true) {n : Nat} (h1 : a ≤ n) (h2 : n < a + L) : HasPtModel n := by
  rw [coverOK, beq_iff_eq] at h
  have hb := congrArg (fun x => Nat.testBit x (n - a)) h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, show n - a < L by omega,
    decide_true, Bool.true_and] at hb
  have := wsound_blockAcc hH a ops (wsound_zero a) (n - a) hb
  rwa [show a + (n - a) = n by omega] at this

/-- Consecutive blocks `(L, ops)` from `a` on are all produced from below. -/
def blocksOK (seeds H : Nat) : Nat → List (Nat × List Nat) → Bool
  | _, [] => true
  | a, (L, ops) :: rest => blockOK seeds H a L ops && blocksOK seeds H (a + L) rest

/-- The end of consecutive blocks `(L, ops)` starting at `a`. -/
def blocksEnd : Nat → List (Nat × List Nat) → Nat
  | a, [] => a
  | a, (L, _) :: rest => blocksEnd (a + L) rest

/-- **Soundness grows by consecutive blocks.** -/
theorem Sound.of_blocksOK {seeds H : Nat} (hs : Sound seeds) :
    ∀ (a : Nat) (bs : List (Nat × List Nat)), Sound (H % 2 ^ a) →
      blocksOK seeds H a bs = true → Sound (H % 2 ^ blocksEnd a bs)
  | _, [], hP, _ => hP
  | a, (L, ops) :: rest, hP, h => by
    simp only [blocksOK, Bool.and_eq_true] at h
    exact Sound.of_blocksOK hs (a + L) rest (hs.mod_add hP h.1) h.2

/-- Consecutive intervals `(L, ops)` from `a` on are all covered. -/
def coversOK (H : Nat) : Nat → List (Nat × List Nat) → Bool
  | _, [] => true
  | a, (L, ops) :: rest => coverOK H a L ops && coversOK H (a + L) rest

/-- **Covered intervals above a sound bitmap**: every size from the start of the first
interval to the end of the last carries a pointed model. -/
theorem hasPtModel_of_coversOK {H : Nat} (hH : Sound H) :
    ∀ (a : Nat) (ws : List (Nat × List Nat)), coversOK H a ws = true →
      ∀ n, a ≤ n → n < blocksEnd a ws → HasPtModel n
  | a, [], _, n, h1, h2 => by simp [blocksEnd] at h2; omega
  | a, (L, ops) :: rest, h, n, h1, h2 => by
    simp only [coversOK, Bool.and_eq_true] at h
    simp only [blocksEnd] at h2
    by_cases hn : n < a + L
    · exact hasPtModel_of_coverOK hH h.1 h1 hn
    · exact hasPtModel_of_coversOK hH (a + L) rest h.2 n (by omega) h2

/-- `ofWords ws acc` appends the 64-bit words `ws`, most significant first, below `acc`,
evaluating the accumulator after each word; `ofWords ws 0` is the number the words spell. -/
def ofWords : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun w _ ih acc => forceThen acc fun acc => ih (acc <<< 64 ||| w))

/-- The bits `lo, …, lo + len - 1` of `H` are all set. -/
def intervalOK (H lo len : Nat) : Bool := (H >>> lo) % 2 ^ len == 2 ^ len - 1

theorem testBit_of_intervalOK {H lo len : Nat} (h : intervalOK H lo len = true) {n : Nat}
    (h1 : lo ≤ n) (h2 : n < lo + len) : H.testBit n = true := by
  rw [intervalOK, beq_iff_eq] at h
  have hb := congrArg (fun x => Nat.testBit x (n - lo)) h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
    show n - lo < len by omega, decide_true, Bool.true_and] at hb
  rwa [show lo + (n - lo) = n by omega] at hb

/-! ## From a long interval of orders to all large orders -/

/-- Every size in `[N, X]` carries a model. -/
def Upto (N X : Nat) : Prop := ∀ n, N ≤ n → n ≤ X → HasPtModel n

/-- **One step up.** If every size in `[N, X]` carries a model, and `q ∈ [N, X]` is coprime
to `P79` with `79 q + N ≤ X + 1`, then every size up to `80 q` carries a model: a size
`n > X` is `79 q + 0 + (n - 79 q)` with `n - 79 q ∈ [N, q]`. -/
theorem Upto.extend {N X q : Nat} (hX : Upto N X) (hg : Nat.gcd q P79 = 1) (hNq : N ≤ q)
    (hq : 79 * q + N ≤ X + 1) : Upto N (80 * q) := by
  intro n hn1 hn2
  by_cases hnX : n ≤ X
  · exact hX n hn1 hnX
  have hqX : q ≤ X := by omega
  have := hasPtModel_two (s := 0) (r := n - 79 * q) (cyclicTD hg) (Nat.zero_le q) (by omega)
    (hX q hNq hqX) hasPtModel_zero (hX _ (by omega) (by omega))
  rwa [show 79 * q + 0 + (n - 79 * q) = n by omega] at this

/-- The first `q` coprime to `P79` found counting down from the argument, among `fuel`
candidates, or `0` if there is none. -/
def findGood (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih q => if Nat.gcd q P79 == 1 then q else ih (q - 1)) fuel

/-- One step of the chain from `[N, X]`: the new right end `max X (80 q)` for the
`q ≤ (X + 1 - N) / 79` coprime to `P79` that `findGood` finds, when `N ≤ q` and
`79 q + N ≤ X + 1`; otherwise `X`. -/
def chainStep (N X : Nat) : Nat :=
  let q := findGood 1000 ((X + 1 - N) / 79)
  if Nat.gcd q P79 == 1 && decide (N ≤ q) && decide (79 * q + N ≤ X + 1) then max X (80 * q)
  else X

theorem Upto.chainStep {N X : Nat} (hX : Upto N X) : Upto N (chainStep N X) := by
  unfold OrderBitmap.chainStep
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    have h' := hX.extend h.1.1 h.1.2 h.2
    intro n hn1 hn2
    by_cases hn : n ≤ X
    · exact hX n hn1 hn
    · exact h' n hn1 (by omega)
  · exact hX

/-- Iterate `chainStep` `steps` times, evaluating each result before the next step. -/
def chain (N : Nat) (steps : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun _ ih X => forceThen X fun X => ih (chainStep N X)) steps

/-- **The chain is sound**: every size in the interval it reaches carries a model. -/
theorem Upto.chain {N : Nat} :
    ∀ (steps : Nat) {X : Nat}, Upto N X → Upto N (OrderBitmap.chain N steps X)
  | 0, _, hX => hX
  | steps + 1, X, hX => by
    change Upto N (forceThen X fun X => OrderBitmap.chain N steps (OrderBitmap.chainStep N X))
    rw [forceThen_eq]
    exact Upto.chain steps hX.chainStep

/-- **The tail.** If every size in `[N, X]` carries a model and `X ≥ 80 (79 (P79 + 2) + N)`,
then every size `n ≥ N` does: for `n > X`, some `q ≡ 1 (mod P79)` with
`n / 80 < q ≤ n / 80 + P79 + 2` is coprime to `P79`, and `n - 79 q` lies in `[N, q]`. -/
theorem Upto.tail {N X : Nat} (hX : Upto N X) (hbig : 80 * (79 * (P79 + 2) + N) ≤ X) :
    ∀ n, N ≤ n → HasPtModel n := by
  intro n
  refine Nat.strongRecOn (motive := fun n => N ≤ n → HasPtModel n) n ?_
  intro n ih hn
  by_cases hnX : n ≤ X
  · exact hX n hn hnX
  have hP : 1 < P79 := by decide
  obtain ⟨c, hc⟩ : ∃ c, c = (n + 79) / 80 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = P79 * (c / P79) := ⟨_, rfl⟩
  have hm1 : m ≤ c := hm ▸ Nat.mul_div_le c P79
  have hm2 : c < m + P79 := by
    have := Nat.lt_mul_div_succ c (by omega : 0 < P79)
    rw [Nat.mul_add, Nat.mul_one, ← hm] at this
    exact this
  obtain ⟨q, hq⟩ : ∃ q, q = m + P79 + 1 := ⟨_, rfl⟩
  have hg : Nat.gcd q P79 = 1 := by
    have hqmod : q % P79 = 1 := by
      rw [hq, hm, show P79 * (c / P79) + P79 + 1 = P79 * (c / P79 + 1) + 1 by
        rw [Nat.mul_add, Nat.mul_one], Nat.mul_add_mod, Nat.mod_eq_of_lt hP]
    rw [Nat.gcd_comm, Nat.gcd_rec, hqmod, Nat.gcd_one_left]
  have hc1 : 80 * c ≤ n + 79 := hc ▸ Nat.mul_div_le (n + 79) 80
  have hc2 : n + 79 < 80 * c + 80 := by
    have := Nat.lt_mul_div_succ (n + 79) (by omega : 0 < 80)
    rw [← hc] at this
    omega
  have h80 : n ≤ 80 * q := by omega
  have h79q : 79 * q + N ≤ n := by omega
  have hqn : q < n := by omega
  have hNq : N ≤ q := by omega
  have := hasPtModel_two (s := 0) (r := n - 79 * q) (cyclicTD hg) (Nat.zero_le q) (by omega)
    (ih q hqn hNq) hasPtModel_zero (ih _ (by omega) (by omega))
  rwa [show 79 * q + 0 + (n - 79 * q) = n by omega] at this

end OrderBitmap

end
namespace OrderBitmap.Cert

/-! ## The seeds -/

/-- The orders recorded before any instruction runs: `0`, `1`, the nine-element `GF9`, the
translation-invariant `T29` and the two-piece models of orders `83` and `227`, the census models
of orders `69` and `76`, the orders `53`, `337`, `360`, `383` and `557` from designs, and the
fourth powers `j⁴` for `2 ≤ j ≤ 18`. -/
def seedList : List Nat :=
  [0, 1, 9, 29, 53, 69, 76, 83, 227, 337, 360, 383, 557] ++ (List.range 17).map fun j => (j + 2) ^ 4

/-- The bitmap of `seedList`. -/
def seedBits : Nat := seedList.foldr (fun n B => B ||| 1 <<< n) 0

theorem hasPtModel_of_mem_seedList {n : Nat} (h : n ∈ seedList) : HasPtModel n := by
  simp only [seedList, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at h
  rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    ⟨j, -, rfl⟩
  · exact hasPtModel_zero
  · exact hasPtModel_one
  · exact hasPtModel_nine
  · exact isIdemModel_T29.hasPtModel
  · exact hasPtModel_53
  · exact ⟨op69, isModel_69, Or.inr ⟨0, by decide, by decide⟩⟩
  · exact isIdemModel_76.hasPtModel
  · exact isIdemModel_TP83.hasPtModel
  · exact isIdemModel_TP227.hasPtModel
  · exact hasPtModel_337
  · exact hasPtModel_360
  · exact hasPtModel_383
  · exact hasPtModel_557
  · exact hasPtModel_pow_four (j + 2)

theorem sound_seedBits : Sound seedBits := sound_foldr fun _ h => hasPtModel_of_mem_seedList h

end OrderBitmap.Cert

namespace OrderBitmap.Cert

/-! ## The certificate data

`hWords` is the bitmap `certH` of the orders below `107601` that the certificate records, as
64-bit words, most significant first. `stageA0`, … list consecutive blocks `(L, ops)` of `certH`
from `0` up, each to be produced from the bits below it; an instruction packs a tag and three
18-bit fields, as `opImage` reads them. `stageB0`, … list consecutive intervals `(L, ops)` from
`107601` up, each to be covered by two-group truncations read from `certH`. Nothing here is
trusted: an instruction whose side conditions fail records nothing, and a wrong bitmap fails
its check. -/

def hWords : List Nat :=
  [0x000000000001ffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]
  ++ [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]
  ++ [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]
  ++ [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]
  ++ [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffb33f73bb, 0xbbb33bbb3bb3fb33, 0xb33333bbba3333bb,
    0x3bbb3b33bb3bbab3, 0x3b3fb3b33bbbb3fb, 0xbb3bbbb3bb3bb73b, 0x3333bbb3b3bb3b37]
  ++ [0x333bbb3bb37b33b3, 0xfbbbb3b3bb3b337b, 0xbbb33bbbb33bb3b3, 0xbab3bb733b33b3b3,
    0xf73bbbbb33b3bbbb, 0x3bf3b33bb33b3bbb, 0xfffbbbfbfffbffbf, 0xfbfbfffbffbffbfb,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xfbb33f3bb33b33b3,
    0x3b33bbbb3bbbb3b3, 0x3bbbb333bbb3b3f7, 0x3b333bbbb33b323b, 0xb3bb33bb3bb7bb33,
    0x3bf3bbb3bb3bbb3b, 0x3bbbb33bbbbbb3b3, 0xbb3bb3bb3bb33bb3, 0xb73bbbbbbf33b33b,
    0x33bb33bb3bbb33b3, 0xbbb3bbbbbb733b3b, 0xb3b3bab3b33bbb3b, 0x333bb3b3b33b3bbb,
    0x3bbb73733bb3bb3b, 0xb7bbb73b3bbbb3bb, 0x3abb3b3bb3bbbb33, 0x3b7f3b3bbbb33fb3,
    0xbb3b33b3ba3bbbbb, 0xb3bb33bfbb333bf3, 0x3333b3bb33bbb3bb, 0x3bbbbb333bb3b3b3,
    0xb3b3bb3b3bfb3bbb, 0xbbb37fbbbabbb3b3, 0xbbbb3bbbbbbbfffb, 0xbfbffbbbfffbffbf,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffff7b, 0xb33bb3bbbb3b3bb7, 0xb3b333bbbb3b3bbb,
    0xbbb33bbbbb33bfb3, 0xb33b3ab33bbbb3bb, 0x3b3b3b333bb33333, 0x3bb3b33bbfb3b33b,
    0xb3b77bbb33bbbffb, 0xbbfffbffbffbffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffbbbb, 0xfffbffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xfffbbb3bbb3373bb, 0xb2b33aff33333bbb, 0x32fb3ab3ba3bb3ab, 0x3e3b3bb33bbbbbb3,
    0x3b3b333bbab3bb7b, 0xbabbbbabbbfffbff, 0xbfffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xfffffff7b2b33b33, 0xbbfbbbbbbbbb3233, 0xb3bb3333bb3b33b3, 0xbabbbbbbfffbffbf,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffba3b, 0xb3fb33b3bbbbb6bb,
    0xb23b3a3b3bbbb3b3, 0xbb33ba3b3affb3f3, 0xb23bb2bbb2b3b2bf, 0x3b7333bfb3bb2a3b,
    0x3abb3bb33bbbbb3b, 0xb33bbbb3b33bb333, 0x33b33ab3bbb337bb, 0xfffbffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xfffffffffbb3bbb3, 0xb3bb333b3ab33bb3, 0x3bb3bb33bbbfbbbb,
    0xb33b333bb2bbbb3b, 0xbb3f33b3ba33b3bb, 0xbbb333fb333bba33, 0x3a33bbbb3bbbb3bb,
    0xb2bb33b33b3bbb33, 0xb3b33b3bb3bb33bb, 0xb3bbbbfbbffffbbf, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xfffffebb3bb3fbb3, 0xbbbbbbfb3b33bbbb, 0xfbffffbfffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffff333bbb3bb3bb, 0x3ab3b3b3b333bbb3,
    0x3a3bb3f33bbb3b3b, 0xb3b3bbbb3a333bbb, 0xb3bbbb3b32bb3abb, 0x3b7b3b3bb333bb33,
    0xb33b3333bab333b3, 0xbefbfffffffffbff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffff7b3bb3bb, 0xbb3bba73bbb3b32b,
    0x3a3bb3bbbbf33a3b, 0xbbbb3bb33bb33b3b, 0xb2fbbb2bbbbb7bb3, 0xbbbbbb333bbb3bbb,
    0xb3b33bbbbb33b3b3, 0x33bbbb333ab3bbab, 0x3bbbbb3b32bfb233, 0xbaa33aabba7bbabb,
    0xbaa33aa3b3bb3b33, 0x33a3b3bbfabb3bbb, 0xbbbb3a73ba33b23b, 0xb3333f3bbb3bbbf7,
    0xb3bbbbbb3abbbb33, 0x337b3a2bb3bbb3b3, 0xbbbbbbb3b33b33bb, 0x3abbb3ab3a3bbbbb,
    0xffffffbfffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xfffffffffffffab3, 0xbb3b3373b3b3b2bb, 0xb3bb73bb3b3bbb3b, 0x3ab3bbbbfffffbfb,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xfffb3abbb3bbb33b, 0x32b3bab3337b3b33, 0xb33bb333babb33bb, 0xfffbfbffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xfbb33a233bbbbabb, 0xb3b332bb32a33bab,
    0xb2b33a2b3273ba3b, 0xb3aabb3bb2bb33b3, 0x3abfb3bbb333bbbb, 0x7a3bbae33b3bbb3b,
    0x76b3b22bb2abb22b, 0x3abbf33bbaa33a2b, 0xbbebbabbbfafffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xfffffffbb3ab3a23, 0xbba3bb2333fbbaa3,
    0xbab3b723ba2bb22b, 0xba2332eb33bbb2b3, 0x3b27ba7b3abbbbab, 0xb23bb33bbabbb2bb,
    0x3bbb33bbbfffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xfffff23b3a2b32bb, 0xb3ab3ab3b3b3ba23, 0x32bb3bbb3ab33b23, 0xba33b2bbb33bfa3b,
    0xba3b3ab33a233bbb, 0x3abbbabb3a3bbab3, 0xb3b3333baab3ba2b, 0xb2a33b2b3bb3babb,
    0x2af33a33ababb223, 0xbaab323b3aab3aa3, 0x3a2bb2b3ba23bafb, 0x33b3bab3f63bbaab,
    0xbaa3bbbfbbbbba33, 0x32a3bba3b3eb333b, 0xa23bbabbb2ab33e3, 0x323bbabbbb23baa3]
  ++ [0xbaab32fbbaa3a2b3, 0xba23332bb233322b, 0xaaa3b2bf22a3ba3b, 0xfbffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xfffffff7aaaba2ab, 0x32abba2333a332bb,
    0xaaabbfffffffffff, 0xbfffffffffffffff, 0xffffffffffffffff, 0xfffffffbaabbba33,
    0xa22bb63b2a3bb2bb, 0x22b33a23bab3bbb3, 0x2a3ba22ba2b3b233, 0xbbbb23b322bbffbf,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffff7ba3aaaba233, 0x2a2b3273a2bbb23b, 0x6e3befaffffffbff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffaaab22bb22bb, 0x222b3aa33a2ba37b,
    0x22a3a233a6aba22b, 0x2233ee2baaa3363b, 0xa2abaab3aa633abb, 0xaaa3a2bb263b22bb,
    0xa2a3a2ab2ab32ab3, 0xaabbaaeb3ffbffff, 0xffbfffffbfffffff, 0xffffffffffffffff,
    0xffeb2a2ba22ba22b, 0xaa2b32a3aaab2ab3, 0xa223a2ab3aab2a2b, 0x2ba3a2a32a63baab,
    0xa2abbaaba2a322ab, 0xfeffffffefffffef, 0xffffffffffffffff, 0xfffffffffaaba3ab,
    0x2a2322eb2aa3ba2b, 0x32abb32b2a2b22ab, 0x3aa3a2232a2b2a23, 0xaae3a2bba2232aab,
    0xa22baaa33aababab, 0x32abb223bbab3aeb, 0x7a3ba2a2e22bae2b, 0xb223bbab3aa3ba2b,
    0x2aa3aa23a22b3a23, 0xaaa3232bba2b33a3, 0xaa23b3abba27b2ab, 0x3b267a2bba6bba23,
    0x3aabb2abb2a3aa2b, 0x2a2bba23bbabba3b, 0x33a3baabb2ab3bab, 0x232bb23b3aab32a3,
    0xb2ab32a3aaaba263, 0xbaaa3bab323bb2a3, 0xaa233aab3ba3bb2b, 0x22b33a233ae3b3a3,
    0xbab2e623a22b3a2b, 0xbbaaa2aa36ab2a23, 0xbaaba2733a2ba2ab, 0x3aa33aabbb3b62ab,
    0xaaaba23bbaa33aab, 0xaa232abbaa2baabb, 0x2abaa23ba2bb6223, 0x3a32a2baaab3a2bb,
    0x2aaba3ab222aab3a, 0x22b3aa33baabaaa3, 0x2ab3aa3b2a632aa3, 0xb22222bb222baabb,
    0x322b2aaba233aaab, 0x2a2ba2f3bbabaa3b, 0xeeab2abbb223a33a, 0x32bab3b332ab3aa3,
    0xba2aaab2a23b3ea2, 0xb2ef32272a2baba3, 0xaaa33aab3baa3ab3, 0xba23aa2332a3b32a,
    0xa32be2b3aaa3b2ab, 0x2aa23aaba223aaab, 0xb22a2baa22aa3a33, 0xa22bbaa32aab3222,
    0x2aa3ba633aabb323, 0xaa2baa2b22a332a3, 0xb3ab3aa3aa23aa2b, 0x2aaaaa2b6aab22a3,
    0xa2aba223b3aa2aab, 0xa22baaa33a23aa7b, 0x2222aaa3222b3abb, 0xaaab23222a2baa23,
    0xbbab2a2b2a3e2abb, 0xaa323a2322aba2b3, 0xaa3b22a32aa332ab, 0xaa322aabaab3a2ab,
    0x222222bbaa2b2223, 0x32b2a3aa32baaa23, 0x32fbbaa33bb2abba, 0xaabbaa2bb2ab22a3,
    0x3ab2aa3b2aa3b22b, 0xa2ab2223baa3a22b, 0x3aa22a2bb3a3a2ab, 0xb2abbaab33a32aab,
    0xa223aaa3322b33aa, 0x22bbaa332a233aa3, 0xaa23a3fa22bbaaa2, 0x3223a22b3a2aa22b,
    0x222a7a2baaab3aa3, 0xba232a23baa22a22, 0x3a2a22a3baa3baaa, 0x3322aa22a2abaa62,
    0xbaa23baa2aabaa2a, 0xa22a2aaf23aba3b3, 0xa2a3aa2aa22ba223, 0xaaaa22a3aaab3a23,
    0x22ab2aa3aa2322ab, 0x3aa32aeaaa2baa2b, 0xaa23a0a2226b2a22, 0xaaab2a3a2aa3a222,
    0xa2ab2a23a2238aa2, 0x2a2b2a22a223aaa3, 0xa2aa22abaa2ba263, 0x2a22a023aa2b26ab,
    0xaa23a2ab2aa32a2a, 0xa28b8aa3aa6bbaa3, 0x22a3a2abba2b2aa3, 0x0a22222aaa22a2ab,
    0x2a233ae322a3a232, 0x66aaaa2a22ab2aaa, 0x2a8aaa2aa2a33a2a, 0xa2ab3aa3a223aa2b,
    0xa2a2aa22aa2b22a3, 0x2aa3aaaa2a322a0a, 0xa22b88ab3a23a3aa, 0x2282aa2382abb22a,
    0xbaaaa32a22a3aa22, 0x8aab2202a2aaa22b, 0x0aa202aaa28b2a82, 0xa2218a6a2aaba828,
    0x2223a2ab8a0b32aa, 0xa0a22a28a2292aa3]

def opsA0 : List Nat :=
  []

def opsA1 : List Nat :=
  []

def opsA2 : List Nat :=
  []

def opsA4 : List Nat :=
  [0x40000800050, 0x10001000070]

def opsA8 : List Nat :=
  [0x200028000b0, 0xb00024000d0]

def opsA16 : List Nat :=
  [0x30001c00130, 0x47, 0x1400051, 0x900014001f0]

def opsA32 : List Nat :=
  [0x1d0008000230, 0x20006800250, 0x40009800290, 0xe00090002b0, 0x2400051, 0x80004800310,
    0x180008000370, 0x3000ec003d0, 0x2400071]

def opsA64 : List Nat :=
  [0x180005800410, 0x200007400430, 0xe000e800470, 0x220002000490, 0x3900080004d0, 0x4000051, 0x84,
    0x3200128005b0, 0x4f0001c005f0, 0x10000400049, 0x8000f400610, 0x2c00091, 0x60018000650,
    0x18000e000670, 0x5400051, 0x14000b4006d0, 0xa4, 0x4000071, 0x3000140001a, 0x3400091,
    0x700002800790, 0x6400051]

def opsA128 : List Nat :=
  [0x2a0016800830, 0x160019800850, 0x33000a8008b0, 0x1c7, 0x180015c008f0, 0x4000091, 0x7400051,
    0x5400071, 0x20001c0001a, 0x440008000970, 0x30001c0001a, 0x90010c009b0, 0x2000030009d0,
    0x50001c0001a, 0x40000e800a30, 0x1b, 0x34000d1, 0x4c00091, 0x8c00051, 0x40000b1, 0xf000c000b50,
    0x270022400b90, 0x5400091, 0x7002e400bf0, 0x7b001b000c10, 0x124, 0x287, 0x7400071,
    0x40032800cd0, 0x40000d1, 0x4f0031400d10, 0x17002f400d30, 0xe001e800d70, 0x470010c00d90, 0x144,
    0x400009c00df0, 0xb400051, 0xa0021800e50, 0x54000b1, 0x30002c0001a, 0x90038400f10,
    0xcc0010c00f50, 0xc1002c800f70, 0x70002c0001a, 0x200037000fb0]

def opsA256 : List Nat :=
  [0x90002c0001a, 0x710022401030, 0x7400091, 0xd400051, 0x2000340001a, 0x1b003d4010f0, 0x54000d1,
    0xdc00051, 0xa4001d001150, 0x7c00091, 0x31003a401190, 0x6000340001a, 0x7f00470011f0,
    0x7000340001a, 0x9000340001a, 0x3900294012d0, 0x4c00101, 0x40003c801310, 0x780048401330, 0x1c4,
    0x5f0036401370, 0xd000340001a, 0xfc00051, 0x74000b1, 0x400001a, 0x10400051, 0x2000400001a,
    0x800510014b0, 0x9400091, 0x63004a4014f0, 0x5400101, 0x1200018801550, 0x12e0004801570,
    0x11400051, 0x3b001e8015d0, 0x3000440001a, 0xe0055801630, 0x9000400001a, 0x1200049001690,
    0x220038c016d0, 0x240046c016f0, 0xa400091, 0xd400071, 0xd000400001a, 0x224, 0x74000d1,
    0x500051c017b0, 0x13000051, 0x4c7, 0x860008001810, 0xac00091, 0xc000440001a, 0xd000440001a,
    0x15, 0x1e005a8018d0, 0x5400131, 0x14000051, 0x1d005d401910, 0x66002fc01930, 0x14400051,
    0x20047401970, 0x270058c01990, 0x14c00051, 0x10001400049, 0x90004c0001a, 0x2c005e801a50,
    0xb0004c0001a, 0x40003c801ab0, 0xc0004c0001a, 0x1a0065801af0, 0xd0004c0001a, 0x22002ac01b70,
    0xfc00071, 0x16400051, 0x110004c0001a, 0x14c001e001c30, 0x120004c0001a, 0x19e0056c01c70,
    0x130004c00019, 0x1640050c01c90, 0x5d005c401cd0, 0xbb0005401cf0, 0x7400101, 0x4000140004a,
    0x63006bc01d50, 0x390034001d90, 0x17c00051, 0x5f7, 0xd400091, 0x18000051, 0x4c0019001e10,
    0x11400071, 0x12b0058001e50, 0x42003f801e70, 0x6e005f801eb0, 0x18c00051, 0x7c00101,
    0x550032001f10, 0xff0022c01f30, 0x647, 0x1350031401f90, 0x2000640001a, 0xfd0014401ff0]

def opsA512 : List Nat :=
  [0x3000640001a, 0x180041802030, 0x50081402090, 0x9f00738020b0, 0x1a400051, 0x304, 0x13000071,
    0x19e003cc02150, 0x9000640001a, 0x390041c021b0, 0x8600204021d0, 0x81005d002210, 0xc9007e802230,
    0xf400091, 0x7400131, 0xd000640001a, 0x1bc00051, 0x19100294022f0, 0x1c000051, 0xf000640001a,
    0x1c400051, 0x14400071, 0x11000640001a, 0x5a00788023b0, 0x344, 0x10001c00049, 0x43005ac02410,
    0x14c00071, 0xd4000b1, 0x1d400051, 0x120007d4024d0, 0x9400101, 0x3000740001a, 0x364,
    0x18000640001a, 0xa9006c402590, 0x10c00091, 0x162003f0025d0, 0x16000348025f0, 0x7400151,
    0xa30088c02650, 0x9000740001a, 0x125003f0026b0, 0x11400091, 0x16400071, 0xc000740001a,
    0x52000ac02770, 0xd000740001a, 0x25400294027d0, 0x11c00091, 0x50001c00049, 0x4f008cc02810,
    0x14b002c402830, 0x10000740001a, 0x11000740001a, 0x7c00151, 0x12000740001a, 0x13000580028f0,
    0xa400101, 0x12400091, 0xbe0076002950, 0x22a0019802990, 0x16000740001a, 0x228001e0029f0,
    0x18000071, 0x240068402a10, 0x18000740001a, 0x80027802a70, 0x19000740001a, 0x3e4, 0x13000091,
    0x1a000740001a, 0xac00101, 0xd4000d1, 0x6f006d402b30, 0x18c00071, 0x149000a802b70,
    0x1d000740001a, 0x3f009fc02bd0, 0x29c0006802bf0, 0x23400051, 0x135004a802c30, 0x510038c02c50,
    0x30008c0001a, 0x180015c02cb0, 0x8f7, 0x180007c0001a, 0x24000051, 0x7f008ec02d10, 0x24400051,
    0x424, 0x14400091, 0x6b006a402dd0, 0x24c00051, 0xe90039802e10, 0x5d0050002e30, 0x947,
    0x25400051, 0x14c00091, 0x444, 0x5e00a9802ef0, 0xd0008c0001a, 0xdb0008002f30, 0x114000b1,
    0x4d00ab402f90, 0x1c80041c02fb0, 0x26400051, 0x1e2005a003010, 0x464, 0x120008c0001a,
    0x26c00051, 0x1bc00071, 0xfa00a34030b0, 0x9c009c8030d0, 0x1c000071, 0xbd0003003110,
    0x860065c03130, 0x160008c0001a, 0x1c400071, 0x2a2006a403190, 0x180008c0001a, 0x16400091,
    0x26a005d403230, 0x28400051, 0x1b0008c0001a, 0x500aa0032b0, 0x1c0008c0001a, 0x400088c032f0,
    0x23d00bfc03310, 0x1d400071, 0x15f0075c03350, 0x5000a2003370, 0x29400051, 0x4b4,
    0x16000940001a, 0x29800051, 0x210008c0001a, 0x130000b1, 0x4c4, 0x74001d1, 0x2a400051,
    0x254007b8034f0, 0xd400101, 0x1b000940001a, 0x1070037003550, 0x2ac00051, 0x1d000940001a,
    0xa400151, 0x18000091, 0x1f000940001a, 0xc000a40001a, 0x4f4, 0x27b0039803670, 0x18400091,
    0x2bc00051, 0xaf7, 0x29a00948036d0, 0x2c000051, 0x8900ba403710, 0x24000940001a, 0x25000940001a,
    0x18c00091, 0x12000a40001a, 0x10002c00049, 0x114000d1, 0x7c001d1, 0xb47, 0xac00151,
    0x2e300c1003890, 0x19400091, 0x1ad0078c038f0, 0x14c000b1, 0x1b30037403950, 0xb87,
    0x1b8008ac039b0, 0x2e400051, 0x19c00091, 0x1b000a40001a, 0x9b00e1003a30, 0x1c000a40001a,
    0x1d000a40001a, 0xb900bd403ad0, 0x2f400051, 0xb4005d403b50, 0x21000a40001a, 0x185008dc03bb0,
    0x50002c00049, 0x310006dc03c10, 0x1fd00abc03c50, 0xe0023803c70, 0x584, 0xa800c9003cb0,
    0xbe0072c03cd0, 0xf400101, 0x27000a40001a, 0x164000b1, 0x1b400091, 0x29000a40001a, 0x23400071,
    0x130000d1, 0xc000bc0001a, 0x7f00db403df0, 0x70002c00049, 0xd000bc0001a, 0x31c00051,
    0x1c6004c003e50, 0x1bc00091, 0x25400c8803e90, 0x32400051, 0xd400131, 0x24000071,
    0x61005d803f10, 0x12000bc0001a, 0x32c00051, 0x1c400091, 0x1a00f9003fd0]

def opsA1024 : List Nat :=
  [0x90002c00049, 0x33400051, 0x24c00071, 0x17300a5404070, 0x9300d1404090, 0x5e4, 0xcf7,
    0x18000bc0001a, 0x9800e08040f0, 0x34000051, 0x19000bc0001a, 0x25400071, 0x4f0031404150, 0x5f4,
    0x1b000bc0001a, 0x23002d0041b0, 0x1d400091, 0xea00cd8041f0, 0x180000b1, 0x3ce0008004210,
    0xc400d8804250, 0x18b0055c04270, 0x1f000bc0001a, 0x12b00e98042b0, 0x26400071, 0x10c00101,
    0x94001d1, 0x35c00051, 0x14c000d1, 0xd87, 0x3ab0010c043d0, 0x17200cf4043f0, 0x1e400091,
    0x4f00fd404430, 0x26000bc0001a, 0x27000bc0001a, 0x3ce00518044b0, 0x644, 0x11400101, 0x37400051,
    0x2a000bc0001a, 0x3930031404570, 0xd400151, 0x4000418045b0, 0x118001e0045d0, 0x50003400049,
    0x2d000bc0001a, 0x1630110404630, 0x38400051, 0x28400071, 0x13600b9404690, 0x18008ec046d0,
    0x38c00051, 0x11c00101, 0x9000dc0001a, 0x400037404750, 0xef0094004790, 0x3e900758047b0,
    0xc000dc0001a, 0x5b01094047f0, 0x70003400049, 0x85007d804810, 0x39c00051, 0x164000d1,
    0x3006a404870, 0xe87, 0x29800071, 0x3a400051, 0x12400101, 0x11000dc0001a, 0x67010b404930,
    0x12000dc0001a, 0x13000dc0001a, 0x20c00091, 0x901254049d0, 0x2a400071, 0x90003400049,
    0x9000340004a, 0xa4001d1, 0x2ac00071, 0x30f0041c04af0, 0x8b0109c04b10, 0x900b0c04b50,
    0x1b000dc0001a, 0x6e4, 0x1c000dc0001a, 0x13000101, 0x1d000dc0001a, 0x1bc000b1, 0x6f4,
    0x3d400051, 0x2000f40001a, 0x6d0114004cf0, 0x2c000071, 0x704, 0x3a600a8004d30, 0x3e100ea004d50,
    0xf87, 0x1c4000b1, 0x3e400051, 0xac001d1, 0x180000d1, 0xb0120c04e10, 0x22c00091,
    0x26000dc0001a, 0x21600b4804e70, 0x27000dc0001a, 0x2af000f404ed0, 0x29000dc0001a,
    0xf0066804f30, 0x23400091, 0x2940047004f70, 0x4d600e1004f90, 0x744, 0x16500c1804ff0,
    0x40000051, 0xf400151, 0x40400051, 0x23c00091, 0x2f000dc0001a, 0xe4010a0050b0, 0x30000dc0001a,
    0x47d00224050f0, 0x13000f40001a, 0x11a00ff005150, 0x41400051, 0x34000dc0001a, 0x11400131,
    0x2c90063c05210, 0x36000dc0001a, 0x40013a805290, 0x2f400071, 0x42400051, 0x14c00101,
    0x1b000f40001a, 0x25400b8005330, 0x4c20009005350, 0x30300ed405390, 0x1800dc0053b0, 0x25400091,
    0x43400051, 0x1b80107005450, 0x13c007b805470, 0x21000f40001a, 0x23900c4c054b0, 0x25c00091,
    0x50004000049, 0x810134405510, 0x44400051, 0x1e30091405590, 0x26000f40001a, 0x44c00051,
    0x60004000049, 0x26400091, 0xc50100805650, 0xa400ecc05690, 0x14600ef4056b0, 0x2a000f40001a,
    0x70004000049, 0x31c00071, 0x45c00051, 0x18001040001a, 0x4ac00fc005770, 0x1187, 0x3101534057d0,
    0x32400071, 0x2f000f40001a, 0x27400091, 0x2a20137005890, 0x32c00071, 0x3800c2c058f0,
    0x16400101, 0x47400051, 0x36600bf005950, 0x824, 0x21001040001a, 0x19e01660059b0,
    0x36000f40001a, 0x3bf0078c05a10, 0x1bc000d1, 0x13000131, 0x48400051, 0x28400091,
    0x1ae00ff805ab0, 0xe000bdc05ad0, 0x34000071, 0x27001040001a, 0x1370117c05b30, 0x3c000f40001a,
    0x1200102405b70, 0x3d000f40001a, 0x28c00091, 0x1c4000d1, 0x230130c05bf0, 0x210010c0001a,
    0x5090102405c50, 0x62015a005c90, 0x1a90169005cb0, 0x4a400051, 0xd0004000049, 0x4dc00fb405d10,
    0x11c00151, 0x30001040001a, 0x29800091, 0x270010c0001a, 0x12c7, 0x29300bfc05e10,
    0x34001040001a, 0x1a70110405e70, 0x2e60166005ed0, 0x3ab0010c05ef0, 0x4c000051, 0x2a400091,
    0x4c400051, 0x25f0120805f90, 0xf017b405fb0, 0x12400151, 0x2de017b405ff0, 0x18000101, 0xd4001d1,
    0x2ac00091, 0x8c4, 0x4d400051, 0x37400071, 0x14013e4060d0, 0x234000b1, 0x18400101,
    0x210011c0001a, 0x53b0036406130, 0x40001040001a, 0x400009c06190, 0x8e4, 0x4e400051,
    0xd80101c061f0, 0x390010c0001a, 0xb3015c406230, 0x254005d406250, 0x8f4, 0x4ec00051, 0x14c00131,
    0x15d00eac062b0, 0x3c0010c0001a, 0x2c000091, 0x904, 0x38c00071, 0x5ef0100406370, 0xd001340001a,
    0x4fc00051, 0x13000151, 0x601578063d0, 0x50004c00049, 0x28800ee806410, 0xef0094006430,
    0x50400051, 0x924, 0x430010c0001a]
  ++ [0x300011c0001a, 0x19400101, 0x39c00071, 0x840174806550, 0x51400051, 0x18f01548065b0,
    0x2d400091, 0x3a400071, 0x70004c00049, 0x11000440004a, 0x360011c0001a, 0x254000b1, 0x1487,
    0xd4001f1, 0x52400051, 0x19c00101, 0x390011c0001a, 0x964, 0x3a0011c0001a, 0x1530149406770,
    0x13a018c806790, 0x4400080067d0, 0x90004c00049, 0x53400051, 0xbb0163006850, 0x984, 0x53c00051,
    0x14f7, 0x400011c0001a, 0x54000051, 0x33800d6806910, 0x264000b1, 0x54400051, 0x1eb0074806970,
    0x430011c0001a, 0x16400131, 0x2ba006c4069d0, 0x9a4, 0xb0004c00049, 0x450011c0001a, 0x2f400091,
    0x442015e006a70, 0x275016d806a90, 0x2a001340001a, 0x1c001400001a, 0x68a0105c06b30, 0x9c4,
    0x2fc00091, 0x1660155006b90, 0x8d01a4406bb0, 0x56400051, 0xbd0078c06bf0, 0xd0004c00049,
    0x2af0123806c10, 0x30001340001a, 0x30400091, 0x2c01a8806cd0, 0x3e400071, 0x1b400101,
    0x3b001e806d10, 0x3f6005cc06d30, 0x34001340001a, 0x2720188806d90, 0x31101af806dd0,
    0x2390138806df0, 0xa04, 0x61a0013c06e30, 0x58400051, 0xf4001d1, 0x284000b1, 0x3a001340001a,
    0x58c00051, 0x1bc00101, 0x1d0014c0001a, 0x1647, 0x2240030406f70, 0x59400051, 0x2380199006fd0,
    0x31c00091, 0x40000071, 0x5fb0060007010, 0x1677, 0x40001340001a, 0x40400071, 0x5a000051,
    0x25a01afc07090, 0x28900490070d0, 0x5a100b84070f0, 0x1c400101, 0x32400091, 0x26b012a407130,
    0x37a00a3c07150, 0x294000b1, 0xa54, 0x45001340001a, 0x16c7, 0x18000131, 0x5b400051, 0x298000b1,
    0x41400071, 0x48001340001a, 0x2e600a8007270, 0x234000d1, 0x5e000fe4072b0, 0x4a001340001a,
    0x4b001340001a, 0x2af011a007330, 0x5c400051, 0x1910069c07390, 0x300014c0001a, 0x5cc00051,
    0x40001400001a, 0x2a4000b1, 0x1e50158407450, 0x5d400051, 0x12a00d08074b0, 0x16400151,
    0x3ab00e94074f0, 0x34000091, 0x44001400001a, 0x5dc00051, 0x45001400001a, 0x21d007a007570,
    0x34400091, 0x43400071, 0x5e400051, 0x48001400001a, 0x5f8016d807630, 0x3a0014c0001a,
    0x1cb0051c07670, 0x17b7, 0x6750190007690, 0x34c00091, 0x5f000051, 0x5b01c4c076d0, 0x5f400051,
    0x4d001400001a, 0x44400071, 0x4e001400001a, 0x5fc00051, 0x40017c00019, 0x400014c0001a,
    0x39300314077f0, 0x50001400001a, 0x60400051, 0xaf4, 0x430014c0001a, 0x7201c68078b0,
    0x2660093c078d0, 0x60c00051, 0x2c0000b1, 0x254000d1, 0x3e3001d007930, 0x1847, 0x10c001d1,
    0x61400051, 0x480014c0001a, 0x11f00130079f0, 0x45c00071, 0x5ba0027c07a50, 0xd400251,
    0xdb0053807ab0, 0x62400051, 0x14a00c6c07af0, 0x4d0014c0001a, 0x4e0014c0001a, 0x18b7,
    0x45001540001a, 0x63000051, 0xb44, 0x338005a807c10, 0x5fd014ec07c30, 0x37400091,
    0x2e301d0807c70, 0x3a3004e007c90, 0x63c00051, 0x180017c00019, 0x4a001540001a, 0x11b0129807cf0,
    0x64000051, 0x114001d1, 0x1d01ee407d50, 0x37c00091, 0x3dc011e407d90, 0x3501e9c07db0,
    0x1c0017c00019, 0x4e001540001a, 0x6b200f9407df0, 0x18000151, 0x300049807e10, 0x1947,
    0x48400071, 0x65400051, 0xbd0107407ed0, 0x53001540001a, 0x19900ad007f30, 0x18400151,
    0x331018b807f90, 0x38c00091, 0x240017c00019, 0x27018b807fd0]

def opsA2048 : List Nat :=
  [0x43001640001a, 0x44001640001a, 0x45001640001a, 0x11c001d1, 0x39400091, 0x47001640001a, 0xbc4,
    0x4c3000b408170, 0x21001840001a, 0x67c00051, 0x19f7, 0x3ca01564081d0, 0x4a400071, 0x68000051,
    0x4d500d3408210, 0x68400051, 0x4d001640001a, 0xbe4, 0x284000d1, 0x20c00101, 0x3a400091,
    0x54000bd808350, 0x2c0203808390, 0x3900294083b0, 0x340017c00019, 0x1bc00131, 0x14501bec083f0,
    0x70006400049, 0x1e006d808410, 0x124001d1, 0x7410103008470, 0x19400151, 0x7b007b8084b0,
    0x40002c00099, 0x6a400051, 0x4c000071, 0x57001640001a, 0x5501ffc08530, 0x58001640001a,
    0x40003c808570, 0x30f01e3c08590, 0x114001f1, 0x14f01c3c085d0, 0x16400574085f0, 0x90006400049,
    0x6b400051, 0x1c400131, 0x7801c8008650, 0x530016c0001a, 0x52700d14086b0, 0x400017c00019,
    0x540016c0001a, 0x298000d1, 0x21f0194c08710, 0x4d400071, 0x6c400051, 0x3c400091, 0xd400291,
    0xb0006400049, 0x7a90208c08810, 0x2c9001ec08830, 0x5a0016c0001a, 0x5b0016c0001a, 0x31c000b1,
    0x4e400071, 0xd001ac0001a, 0x2201e1c08930, 0x2a4000d1, 0x78b0020408990, 0x3f800474089b0,
    0x130001d1, 0x6e400051, 0xd0006400049, 0x4d0017c0001a, 0x324000b1, 0x4e0017c0001a,
    0x45001840001a, 0x32c01a3408ad0, 0x3dc00091, 0x22c00101, 0x6f400051, 0x520017c0001a,
    0x4fc00071, 0x540017c00019, 0x540017c0001a, 0x3e400091, 0x70400051, 0x50400071, 0x570017c0001a,
    0x13022e408cb0, 0x580017c0001a, 0x4d200ff808cf0, 0x23400101, 0x4c701e7808d10, 0x3ec00091,
    0x5a0017c00019, 0x1c47, 0x2b300cac08d70, 0x71400051, 0x2520014808dd0, 0x5d0017c0001a,
    0x71c00051, 0x1c77, 0x5e0017c0001a, 0xcf4, 0xd4002b1, 0x72000051, 0xd10206408e90,
    0x8880135408ed0, 0x2160172808ef0, 0x340000b1, 0x1b400151, 0x67b0145c08f50, 0x59001840001a,
    0x8790099c08fb0, 0x1cc7, 0x52400071, 0x40000091, 0x22a01b6009010, 0x5c001840001a,
    0x13101f5c09070, 0x40400091, 0x7f700ecc090b0, 0x1cf7, 0x800a3c090d0, 0x74000051,
    0x5090102409110, 0x74400051, 0x61001840001a, 0x53400071, 0x4e001940001a, 0x150006400049,
    0x18001c00001a, 0xa0002c00099, 0x22201c1009250, 0x630240c09290, 0x59501098092b0, 0x41400091,
    0x9f02244092f0, 0x54000071, 0x2e3000c009310, 0xd64, 0x130001f1, 0x54001940001a, 0x54400071,
    0x1d87, 0x79d0196c093d0, 0x57001940001a, 0x7c01dc809430, 0x1c400151, 0x76c00051, 0x1db7,
    0x3d500b4409490, 0x77000051, 0x40a01510094d0, 0x25400101, 0x77400051, 0x12001c2c09530,
    0x5c001940001a, 0x5d001940001a, 0x1df7, 0x5e001940001a, 0x78000051, 0x5ef0109809650,
    0x14c001d1, 0x61001940001a, 0xd0257c096b0, 0x62001940001a, 0x78c00051, 0x25c00101,
    0x63001940001a, 0x43400091, 0x79400051, 0x48001ac0001a, 0x374000b1, 0x70007400049,
    0x30001c00001a, 0x7de0226809830, 0x3ea0015409850, 0x43c00091, 0xd3022dc09890, 0x2f5022a0098b0,
    0x4c001ac0001a, 0x26400101, 0x4d001ac0001a, 0x49b0120809950, 0x81a005f809970, 0x13001dc00019,
    0x44400091, 0x14001dc00019, 0x50001ac0001a, 0x90007400049, 0xe04, 0x2d20036009a30,
    0x52001ac0001a, 0x58400071, 0x6b016c409a90, 0x7bc00051, 0x1ef7, 0x54001ac0001a,
    0x98c00bf809af0, 0x7c000051, 0x55001ac0001a, 0x8fb011d009b30, 0x43700ae409b50, 0xe24,
    0x54801c0409b90, 0x1c001dc00019, 0x45400091, 0x2f2011c409bf0, 0xb0007400049, 0x38c000b1,
    0x59400071, 0x94e001e009c50, 0x70e0132809c70, 0x7d400051, 0x37f00dc009cd0, 0x45c00091,
    0x27400101, 0x5d001ac0001a, 0x5e001ac0001a, 0x39e01b2409d70, 0x5a000071, 0x13501cd409d90,
    0x24001dc00019, 0x7e400051, 0x120020c409df0, 0xd0007400049, 0x46400091, 0x78025b009e30,
    0x62001ac0001a, 0x63001ac0001a, 0x8d022e009eb0, 0x39c000b1, 0x7f400051, 0x66001ac0001a,
    0x16a0223809f70, 0x11400251, 0x2fc0094009fb0, 0x2c001dc00019, 0x29701ae409fd0, 0x50007c00049,
    0x69001ac0001a, 0x3a4000b1, 0x80400051, 0x24021180a090, 0x14c001f1, 0x80c00051, 0x28400101,
    0x54001c00001a, 0x164001d1, 0x5c400071, 0x56001c00001a, 0x31c000d1, 0x34001dc00019,
    0x57001c00001a]
  ++ [0x118024200a1f0, 0x70007c00049, 0x574011c40a210, 0x5cc00071, 0x48400091, 0x829008140a2d0,
    0x28c00101, 0x5c001c00001a, 0x5d400071, 0x324000d1, 0x9f007380a370, 0x534010a00a390,
    0x78027180a3d0, 0xba018c00a3f0, 0x130007400049, 0x83400051, 0x12a01a6c0a430, 0x61001c00001a,
    0x62001c00001a, 0x40001dc00019, 0x63001c00001a, 0x5e400071, 0x29400101, 0x62c016600a510,
    0x84400051, 0x40c002e40a570, 0x66001c00001a, 0x6a001a1c0a5b0, 0x7b7028a40a5d0, 0x29800101,
    0x68001c00001a, 0x1c000e1c0a630, 0x85000051, 0x2147, 0x19e01cc80a690, 0x5f400071,
    0x6b001c00001a, 0x60028400a6f0, 0x4a400091, 0x40021400019, 0x68001c40001a, 0x23400131,
    0x5fc00071, 0x2ac009f00a7b0, 0x4c001dc00019, 0x86400051, 0xd0007c00049, 0x30023e40a810,
    0x6c001c40001a, 0x68a00c880a870, 0x63001cc0001a, 0x942015cc0a8d0, 0x340000d1, 0x8601b600a910,
    0xf64, 0x60c00071, 0x2f101e9c0a970, 0x71001c40001a, 0x54001dc00019, 0x879019f00a9d0,
    0x117016b40a9f0, 0x190007400049, 0x69001cc0001a, 0x61400071, 0x88400051, 0xf84,
    0x36e01cf80aab0, 0x6c001cc0001a, 0x9550218c0aaf0, 0x4c000091, 0x59001dc0001a, 0x3e4000b1,
    0x5a001dc00019, 0x3c601bc00ab50, 0x782013700ab70, 0x89400051, 0x59f019940abb0, 0x929021a40abd0,
    0x62400071, 0x71001cc0001a, 0x89c00051, 0x180021400019, 0x72001cc0001a, 0x164001f1,
    0x5f001dc00019, 0x40c01af80ac90, 0x4cc00091, 0x8a400051, 0x2d3026180acf0, 0x61001dc0001a,
    0x63000071, 0x62001dc0001a, 0x8ac00051, 0x63001dc00019, 0x63001dc0001a, 0x65201e780adb0,
    0x64001dc00019, 0x4d400091, 0x180001d1, 0x8b400051, 0x66001dc0001a, 0x2410229c0ae70,
    0x63c00071, 0x5ef01cc80aeb0, 0x22f7, 0x78501a800aed0, 0x4dc00091, 0x8c000051, 0x190025880af10,
    0x105025540af30, 0x240021400019, 0x8c400051, 0xff4, 0x1d00c180af70, 0xd400351, 0x13000251,
    0x184001d1, 0x400000b1, 0x4e400091, 0x1f901c2c0b050, 0x8d400051, 0x404000b1, 0x11400291,
    0x25400131, 0x18d014500b110, 0x8dc00051, 0x72001dc00019, 0x72001dc0001a, 0x1024, 0x2387,
    0x74001dc00019, 0x8e400051, 0x98c02a9c0b210, 0x6b02ae40b230, 0x76001dc0001a, 0x946007880b270,
    0x77001dc00019, 0x7027280b290, 0x6002b380b2d0, 0x9bd012540b2f0, 0x8f400051, 0x340021400019,
    0x4fc00ea80b350, 0x4fc00091, 0x374000d1, 0x23f7, 0x72001e40001a, 0x90000051, 0x2be015640b410,
    0x284017b40b450, 0x50400091, 0x76001e40001a, 0x2d400101, 0x77001e40001a, 0x57a026f00b530,
    0x2447, 0x91400051, 0x26400131, 0x66001f40001a, 0x78b00f540b5f0, 0x68000071, 0x5d001fc0001a,
    0x91c00051, 0x400021400019, 0x3a8003dc0b650, 0x68400071, 0x2487, 0x92400051, 0x194001d1,
    0x6c001f40001a, 0x63001fc0001a, 0x24c7, 0x1d0007c00049, 0xa5402ca40b810, 0xa0a020380b830,
    0x10c4, 0x38c000d1, 0xe7021a00b890, 0x72001f40001a, 0x434000b1, 0x94000051, 0x52400091,
    0x4c0021400019, 0x94400051, 0x114002b1, 0x75001f40001a, 0x2ec022c00b9b0, 0x76001f40001a,
    0x94c00051, 0x180001f1, 0x48302d080ba10, 0x52c00091, 0x9a2008100ba50, 0xa8d02c580ba70,
    0x95400051, 0x19c001d1, 0x6ec011200bad0, 0x4fb01b800bb10, 0x540021400019, 0x53400091,
    0x14d00e980bb90, 0x6b400071, 0xa902c540bbd0, 0x31001ab80bbf0, 0xd0008c00049, 0x75001fc0001a,
    0x3b90202c0bc30, 0x76001fc0001a, 0x96c00051, 0xa3400d140bc90, 0x5a0021400019, 0x25c7,
    0x54000091, 0x97400051, 0x3a4000d1, 0x6c400071, 0x54400091, 0x3bf00cc40bdb0, 0x924023cc0bdd0,
    0x5f0021400019, 0x284025780be10, 0x98400051, 0x83700a780be70, 0x389027500be90, 0xe025840bed0,
    0x2fc00101, 0x63002140001a, 0x28400131, 0x640021400019, 0x1d8028780bf50, 0x56d0088c0bf90,
    0x58600f340bfb0, 0x55400091, 0x14c00251, 0x70009400049, 0xa6c017400c010, 0x680021400019,
    0x720020c0001a, 0x5e9008880c070, 0x1184, 0x9a400051, 0x6e400071, 0x30400101, 0x750020c0001a,
    0x5ae019980c130, 0x760020c0001a, 0xad1003f00c170, 0x69e00b180c190, 0x26c7, 0x130008c00049,
    0x9b400051, 0x552010f40c250, 0x71002140001a, 0x9bc00051, 0x13000291, 0x7c0020c0001a]
  ++ [0x3be021d00c310, 0x740021400019, 0x9c400051, 0x25400151, 0x4c200e200c3b0, 0x3cd0292c0c3d0,
    0x474000b1, 0x770021400019, 0x77002140001a, 0x81e018140c430, 0x780021400019, 0x57400091,
    0x70400071, 0x9d400051, 0x11e4, 0x66002240001a, 0x5d0022c0001a, 0x29800131, 0x5400281c0c530,
    0x7c0021400019, 0x858008ec0c550, 0x1b4001d1, 0xe3029080c5b0, 0x9e400051, 0xd0009400049, 0x1204,
    0x71400071, 0x80002140001a, 0x58400091, 0x484000b1, 0x22502ad00c6d0, 0x31c00101,
    0xc4800c880c710, 0x8f0148c0c730, 0x84002140001a, 0x477020040c770, 0x72000071, 0x5ba02f8c0c790,
    0x9fc00051, 0x27f7, 0x72002240001a, 0x32d028c00c7f0, 0xa0000051, 0x73002240001a,
    0x4f030dc0c850, 0x75002240001a, 0x3dc000d1, 0x59400091, 0x3ce002c40c8f0, 0x32400101,
    0xc1102f100c910, 0x1bc001d1, 0x5b801b780c950, 0xa1400051, 0x22a00cf80c9b0, 0x2ac024280c9d0,
    0xf400351, 0x3e4000d1, 0x5a000091, 0x62801d440ca90, 0xa2400051, 0x74000071, 0x5a400091,
    0x41c022600cb30, 0x14a01c540cb50, 0xa2c00051, 0x1284, 0x2eb025980cbb0, 0x28c7, 0xae9026bc0cbf0,
    0x1d0008c00049, 0xa3400051, 0x4a4000b1, 0x130002b1, 0x84002240001a, 0x456025f00cc70,
    0x85002240001a, 0xa3c00051, 0x28f7, 0x1c4001d1, 0xa4000051, 0x87002240001a, 0x40d00e100cd30,
    0xa4400051, 0x89002240001a, 0x16400251, 0x1f0008c00049, 0x27400151, 0x54032480ce50, 0x5bc00091,
    0xb12007600ce90, 0x48e000e40ceb0, 0x840022c0001a, 0x39028340cef0, 0x7460118c0cf10,
    0x860022c0001a, 0x5c400091, 0xa6400051, 0x400000d1, 0x890022c0001a, 0x16f02e540d030,
    0x77000071, 0x8a0022c0001a, 0x12f4, 0x8b0022c0001a, 0x77400071, 0x404000d1, 0x29a01df80d0f0,
    0x4c0000b1, 0xa7400051, 0x70002440001a, 0x71002440001a, 0x766016d80d1b0, 0x29f7, 0x5d400091,
    0xa8000051, 0x14c02f580d210, 0x2c5006840d250, 0xb9202ea80d270, 0x7f0023c0001a, 0x497022540d2b0,
    0x5b000a380d2d0, 0x5dc00091, 0x34c00101, 0xa10017b40d310, 0x3e9016d80d330, 0x78c00071,
    0xa9400051, 0x1344, 0xdc031900d3f0, 0x7000a400049, 0x5e400091, 0xaa400d140d430, 0x860023c0001a,
    0x4d4000b1, 0x2a87, 0x14c00291, 0xaa400051, 0x5f7022680d510, 0x5ec00091, 0x8a0023c0001a,
    0xaac00051, 0x2ab7, 0x8b0023c0001a, 0xab000051, 0x2cd02a440d5d0, 0x28c00151, 0x1d0009400049,
    0xab400051, 0x5f400091, 0x2bf004300d690, 0x62f005f80d6d0, 0x9f5025840d6f0, 0xac000051,
    0x1bc001f1, 0x4e4000b1, 0xac400051, 0x5fc00091, 0x89002440001a, 0x8a002440001a,
    0x888006d40d7f0, 0x1f0009400049, 0x3e200b480d810, 0x1ba02f300d850, 0x1030305c0d870, 0xad400051,
    0x7a01be40d8d0, 0x7c000071, 0x8f002440001a, 0xadc00051, 0x90002440001a, 0x628012a80d970,
    0x91002440001a, 0x60c00091, 0xae400051, 0x29800151, 0xd000a400049, 0x7f002540001a,
    0x7e6016f80da30, 0xcb1030f40da50, 0x434000d1, 0x5b2034380dab0, 0x61400091, 0x1c4001f1,
    0x2fc02ad80db10, 0x7d400071, 0x4fc000b1, 0x28d02cac0db70, 0x85002540001a, 0x81a016600dbb0,
    0x2b3004080dbd0, 0x230009400049, 0x1404, 0x893008100dc30, 0xb0400051, 0x3f007000dc90,
    0x504000b1, 0x8a002540001a, 0x13501ac00dcf0, 0x37400101, 0x62400091, 0x64035c80dd50,
    0x5db0038c0dd90, 0xa2012280ddb0, 0x444000d1, 0x10c00351, 0x18000251, 0x8f002540001a,
    0x90002540001a, 0x19d0166c0de70, 0x2c87, 0x7f400071, 0x63000091, 0xb2400051, 0x37c00101,
    0x14c002b1, 0x9c035600df30, 0x63400091, 0xb2c00051, 0x2cb7, 0xfd021340df90, 0xb3000051,
    0x552022b00dfd0, 0x62010380dff0, 0x13000a400049, 0xb3400051, 0x433020c80e050, 0x80400071,
    0x8f0025c0001a, 0x2cf7, 0x900025c0001a, 0xb4000051, 0x4f8028c40e110, 0x621014300e150,
    0x1900227c0e170, 0x64400091, 0x85e01e440e1d0, 0x15000a400049, 0x950025c0001a, 0x524000b1,
    0x2d47, 0xb5400051, 0x64c00091, 0xb38026b40e2d0, 0x20b030940e2f0, 0x38c00101, 0x850026c0001a,
    0xb5c00051, 0x44902df40e350, 0x67f01eec0e390, 0x1e5032500e3b0, 0xb6400051, 0x20e028a40e3f0,
    0xd000ac00049, 0x16400291, 0x5ae033f00e450]
  ++ [0x13002cc00019, 0x11400351, 0x14002cc00019, 0x4b5030140e4d0, 0x65c00091, 0x39400101,
    0xbdf034740e510, 0xd4c034f40e530, 0x8e0026c0001a, 0x810375c0e570, 0xade027640e590, 0xb7c00051,
    0x18002cc00019, 0x900026c0001a, 0x19000a400049, 0x66400091, 0x98c00f1c0e650, 0x14f4,
    0x930026c0001a, 0x103035a40e6b0, 0x1c002cc00019, 0x940026c0001a, 0xbe9027a40e6f0, 0x540000b1,
    0x20f0081c0e710, 0x821019540e750, 0x84400071, 0xb9400051, 0x544000b1, 0x980026c0001a,
    0x990026c0001a, 0x9a0026c0001a, 0x94e014f00e890, 0x85000071, 0xba400051, 0x3a400101,
    0x93002740001a, 0x19e035c40e930, 0x79a00ed00e950, 0xbac00051, 0xbdc00c8c0e990, 0x1902f900e9b0,
    0x1544, 0x68000091, 0xbb400051, 0x98002740001a, 0xbc8016d80ea70, 0x68400091, 0x5e039880eab0,
    0x2c002cc00019, 0x484000d1, 0x86400071, 0x1e000a400049, 0x3f902ae40eb10, 0x11c00351,
    0xbc400051, 0x9d002740001a, 0x68a025cc0ebd0, 0xbcc00051, 0x1f000a400049, 0x8b002840001a,
    0xa0004c00099, 0x31c00131, 0x1584, 0x86023d40ecb0, 0x34002cc00019, 0x69400091, 0x8f002840001a,
    0xbdc00051, 0x90002840001a, 0x20c001d1, 0x2d400151, 0x63f0227c0edd0, 0x93002840001a,
    0x4ec015cc0ee30, 0x94002840001a, 0x4c3027e00ee70, 0xb0004c00099, 0x95002840001a, 0x32400131,
    0x1170375c0eed0, 0xbf400051, 0x164002b1, 0x732019000ef50, 0x99002840001a, 0x40002cc00019,
    0x9a002840001a, 0xb2302d880eff0, 0x23000a400049, 0x9b002840001a, 0x89400071, 0xae5029ac0f050,
    0x26401e880f070, 0x9d002840001a, 0x3503b5c0f0b0, 0x2f502a640f0d0, 0xc0c00051, 0x3c400101,
    0x89c00071, 0x6b400091, 0xc1400051, 0x12400351, 0x8a400071, 0x25000a400049, 0x1604, 0xc1c00051,
    0x256039100f250, 0x6bc00091, 0x1cb0357c0f290, 0x584000b1, 0x4c002cc00019, 0xc2400051,
    0x5f01f380f310, 0x9e0028c0001a, 0x405016600f370, 0x6c400091, 0x8b400071, 0x30c7,
    0x1d000ac00049, 0x9c3015fc0f410, 0x43b000f80f430, 0xa20028c0001a, 0x232034580f470,
    0x3c0002940f490, 0x30f7, 0x1644, 0x4bc012440f4f0, 0xc4000051, 0x910029c0001a, 0xc4400051,
    0x8c400071, 0x930029c0001a, 0x6103bec0f5b0, 0x940029c0001a, 0x860065c0f5f0, 0x18000291,
    0x950029c0001a, 0x5a002cc00019, 0x3147, 0x26302bdc0f670, 0xc5400051, 0x980029c0001a, 0x1674,
    0x6dc00091, 0x4c0000d1, 0x990029c0001a, 0xc5c00051, 0x9a0029c0001a, 0x5a0000b1, 0x1684,
    0x2a2038340f7d0, 0x5d600de00f7f0, 0x8dc00071, 0x120037540f830, 0x9e0029c0001a, 0x63002cc00019,
    0xe6e0347c0f890, 0x64002cc00019, 0x31c7, 0x8e400071, 0x3e400101, 0xc7400051, 0xa20029c0001a,
    0x1ab017b40f970, 0xa30029c0001a, 0x68002cc00019, 0x9460224c0f9d0, 0x23000ac00049,
    0x266034f00fa10, 0xc8400051, 0x782010240fa90, 0x8f400071, 0x9e002a40001a, 0x8b002b780faf0,
    0x3ec00101, 0x4d4000d1, 0x3103e140fb50, 0xc9400051, 0xbd01c700fbb0, 0x13000351, 0xa2002a40001a,
    0x22c001d1, 0x90000071, 0x3e9030640fc10, 0x72002cc00019, 0xb9c026d40fc50, 0xdc9029bc0fc70,
    0x70400091, 0x7a9003640fcb0, 0x74002cc00019, 0xca400051, 0x1704, 0x2003ed00fd30, 0x30400151,
    0xcb1023f80fd70, 0x77002cc00019, 0xa9002a40001a, 0x70c00091, 0x78002cc00019, 0x6d1015e00fdd0,
    0x9000c400049, 0xcb400051, 0x91400071, 0x4e4000d1, 0x1724, 0x99002b40001a, 0xcbc00051,
    0x7c002cc00019, 0x71400091, 0x28000ac00049, 0x91c00071, 0xbd000bfc0ff50, 0xc2a005b00ff70,
    0x234001d1, 0x90601bd80ffb0, 0x616031d80ffd0, 0xccc00051]

def stageA0 : List (Nat × List Nat) :=
  [(1, opsA0), (1, opsA1), (2, opsA2), (4, opsA4), (8, opsA8), (16, opsA16), (32, opsA32),
    (64, opsA64), (128, opsA128), (256, opsA256), (512, opsA512), (1024, opsA1024),
    (2048, opsA2048)]

def opsA4096 : List Nat :=
  [0x9f002b40001a, 0x3347, 0x5d4000b1, 0x72000091, 0xafe0143010090, 0x1bc00251, 0xa2002b40001a,
    0x2903f9c100f0, 0x40400101, 0x72400091, 0x9f5030b410130, 0xa4002b40001a, 0x3387,
    0x120007d4101b0, 0xce400051, 0x180002b1, 0x1d901eec10210, 0xce800051, 0xa8002b40001a, 0x1784,
    0x8c002cc00019, 0x5f1028f4102d0, 0x94000071, 0xcf400051, 0x33d7, 0x5e4000b1, 0x73400091,
    0xcf800051, 0x94400071, 0x489002a810390, 0x90002cc00019, 0xa4002bc0001a, 0x17a4,
    0xa5002bc0001a, 0xd0400051, 0x73c00091, 0x34602e9010490, 0x17b4, 0x92002ce8104b0,
    0x94002cc00019, 0x504000d1, 0x74000091, 0x4810300810510, 0x95400071, 0xd1000051, 0x1c400251,
    0xd1400051, 0xac002bc0001a, 0x5f4000b1, 0xad002bc0001a, 0x40034400019, 0xae002bc0001a,
    0x37400131, 0x58d02b7410690, 0x17e4, 0xd2400051, 0xa90198c106f0, 0x114003d1, 0x3160357810730,
    0x5fc000b1, 0xae002c00001a, 0xd904028107b0, 0xa0002cc00019, 0x96c00071, 0x7f008ec107f0,
    0x13000c400049, 0xd3400051, 0xa2002cc0001a, 0xc8009b010870, 0xa3002cc0001a, 0xf9003ca8108b0,
    0x34f7, 0xe3003164108d0, 0xd4000051, 0x2520390010910, 0x1fd03da010930, 0xd4400051, 0x1824,
    0xadc032b410990, 0xa8002cc00019, 0xa8002cc0001a, 0x130034400019, 0x76400091, 0x140034400019,
    0x48019bc10a50, 0x98400071, 0xab002cc00019, 0x7b1038c010a90, 0xac002cc00019, 0x1844,
    0x2570396410af0, 0xad002cc0001a, 0xd5c00051, 0x180034400019, 0x524000d1, 0x614000b1, 0x3587,
    0x77000091, 0xd6400051, 0xb1002cc0001a, 0xc9c0420410c30, 0x1c0034400019, 0x77400091,
    0xb3002cc00019, 0x9c30160810c90, 0x35c7, 0x9150241810cf0, 0x43400101, 0xd7400051,
    0xc2501ab810d50, 0x38c00131, 0x35f7, 0xae002d40001a, 0x9a400071, 0xd8000051, 0x254001d1,
    0x624000b1, 0x240034400019, 0xd8400051, 0x288009cc10e70, 0x78400091, 0x17103dec10eb0,
    0x86603df810ed0, 0x43c00101, 0xb3002d40001a, 0x7c20401410f30, 0x3647, 0x4c203f0c10f70,
    0xd9400051, 0x18b4, 0x9b400071, 0xa2002e40001a, 0xd9800051, 0xac60179010ff0, 0x7000d400049,
    0xa3002e40001a, 0x101701ed011030, 0x630000b1, 0xab30149811050, 0x9bc00071, 0x5d700670110b0,
    0xda400051, 0x7df005a8110f0, 0x540000d1, 0xa7002e40001a, 0x234001f1, 0xa8002e40001a,
    0xdac00051, 0x36b7, 0xa9002e40001a, 0x25c001d1, 0xdb000051, 0x544000d1, 0x79c00091,
    0x1d000c400049, 0x104e0401811210, 0x340034400019, 0x63c000b1, 0x18f4, 0x17403ed011270,
    0xad002e40001a, 0xae002e40001a, 0x14c00351, 0xdc000051, 0x1904, 0x9d400071, 0x76b0272c11350,
    0xb1002e40001a, 0xfc7005d4113b0, 0xb2002e40001a, 0x1f000c400049, 0x7b701e4011410, 0x7ac00091,
    0xeb0416c11450, 0x1924, 0xdd400051, 0x3a400131, 0x2e901768114d0, 0x9e400071, 0x45400101,
    0x51f01c2c11510, 0x400034400019, 0x264001d1, 0xdb041fc11590, 0xde400051, 0x184043ac115f0,
    0xd000d400049, 0xb1002ec0001a, 0x1170413411630, 0x98b0392811650, 0xdec00051, 0xb3002ec0001a,
    0x114202070116b0, 0x37c7, 0x7c000091, 0xdf400051, 0x1964, 0x30f0247811750, 0x9fc00071, 0x37f7,
    0xcba0112c117d0, 0xe0000051, 0xca042e011810, 0x23203e2411830, 0x4c0034400019, 0xe0400051,
    0xcd401cd411870, 0x109d00aec11890, 0x7cc00091, 0xa8002fc0001a, 0xe0c00051, 0x46400101,
    0xa9002fc0001a, 0xe8803f1011930, 0x3ce0350011950, 0xe1400051, 0x7d400091, 0x25000c400049,
    0x321039c811a10, 0xe1c00051, 0x540034400019, 0xae002fc0001a, 0x4f70361811a70, 0x3887,
    0xe2400051, 0xb1002fc0001a, 0xb2002fc0001a, 0xf3a03de411b90, 0x5a0034400019, 0x38c7,
    0xa2400071, 0x13000d400049, 0xe3400051, 0xb6002fc0001a, 0x1bc00291, 0x274001d1,
    0x1ad0407c11cb0, 0xa2c00071, 0x47400101, 0xae0437411d10, 0xe4400051, 0x19f4, 0xbb002fc0001a,
    0xa3400071, 0xbc002fc0001a, 0x680000b1, 0x1a04, 0xfa02cf011e30, 0x640034400019, 0x7f400091,
    0x8dd02e7011e90, 0x684000b1, 0x584000d1, 0x5cd042e011ef0, 0xa4000071, 0xb7003040001a]
  ++ [0x680034400019, 0x31e005e411f50, 0xa4400071, 0x3987, 0x2e7002cc11fb0, 0xe6400051,
    0x2b000c400049, 0xbb003040001a, 0xbc003040001a, 0xc890425c12070, 0x80400091, 0x254001f1,
    0xe4044a8120d0, 0x11400431, 0x48400101, 0xe7400051, 0xbe03b0412130, 0xc0003040001a,
    0xd540131012170, 0x1c400291, 0xe7c00051, 0x130003d1, 0xae003140001a, 0x59203338121f0,
    0x2d000c400049, 0x594000d1, 0x740034400019, 0xe8400051, 0xb1003140001a, 0x3a103a2c122b0,
    0xb2003140001a, 0xf2702b28122f0, 0x770034400019, 0xb3003140001a, 0x780034400019, 0x3a47,
    0x25b020b012370, 0xe9400051, 0x284001d1, 0xb7003140001a, 0x6a4000b1, 0x7c0034400019,
    0xb8003140001a, 0x5a0000d1, 0x4650474812490, 0xa7400071, 0xea400051, 0x10af03fb8124f0,
    0x82400091, 0x71102d0c12530, 0xf3a0484012550, 0xf4302bd012590, 0x3ac7, 0xa8000071,
    0xf6d00bd412610, 0x82c00091, 0x1ac4, 0x240068412670, 0x850034400019, 0xc1003140001a,
    0x16400351, 0x6b4000b1, 0x1e000d400049, 0x28b03f9c12710, 0xa503e9412730, 0xec400051,
    0x28c001d1, 0xc5003140001a, 0x3e400131, 0xbc0031c0001a, 0x1f000d400049, 0xa90032c0001a,
    0xa9400071, 0x8c0034400019, 0x10f00065812850, 0x264001f1, 0x469014a812890, 0xc00031c0001a,
    0x32703da4128f0, 0x4a400101, 0x80422012910, 0x900034400019, 0xa980309c12950, 0x5ba0328412970,
    0x84400091, 0x6c4000b1, 0xee400051, 0xaa400071, 0x6fd04a0812a10, 0xd0b01b5c12a30,
    0x940034400019, 0x1bc002b1, 0xeec00051, 0xc70031c0001a, 0xaac00071, 0x56902f7412af0,
    0x294001d1, 0xab000071, 0x5ab0309412b50, 0xb70032c0001a, 0xab400071, 0x3bf7, 0x85400091,
    0xf0000051, 0x1c20440012c10, 0x310033e812c50, 0x39400151, 0xbc0032c0001a, 0x298001d1,
    0xac000071, 0xb3003340001a, 0x1b64, 0xa00034400019, 0x3c47, 0xac400071, 0xf1400051,
    0x1148032b012dd0, 0x2bf0408412df0, 0x25000d400049, 0x86400091, 0xe0023812e30, 0xa40034400019,
    0x10a10273812e50, 0x1b84, 0xf2400051, 0x12130284c12ef0, 0x5d4000d1, 0xad400071, 0xa80034400019,
    0xc60032c0001a, 0x47303a1412f70, 0xc70032c0001a, 0x1c4002b1, 0xbe046f412fd0, 0x4c000101,
    0xc250166013010, 0x29401da013030, 0xac0034400019, 0x87400091, 0xb20495813070, 0xcb0032c0001a,
    0x5dc000d1, 0xc2003340001a, 0xae400071, 0xf4000051, 0xc3003340001a, 0x40400131, 0xf4400051,
    0xc5003340001a, 0x66802a54131b0, 0x3a400151, 0xf4c00051, 0xb30034400019, 0xc7003340001a,
    0x11c00451, 0xb40034400019, 0x5e4000d1, 0x18e026d813270, 0xf5400051, 0x2fc01fe4132b0,
    0x69b008f4132d0, 0x4cc00101, 0xcb003340001a, 0xcc003340001a, 0xd980166013390, 0x88c00091,
    0xf6400051, 0x109904054133f0, 0x2b000d400049, 0x1c04, 0x614034c013430, 0x14802bc413450,
    0xf6c00051, 0xc2003400001a, 0x704000b1, 0xf7000051, 0x89400091, 0x4d400101, 0xf7400051,
    0x6bb025cc13550, 0x17d0476c13570, 0x5f4000d1, 0x83d00db4135b0, 0x3df7, 0xc7003400001a,
    0x89c00091, 0xf8000051, 0x6950333413610, 0x5db02fdc13630, 0xc40034400019, 0xf8400051,
    0xca003400001a, 0x1c44, 0xf8c00051, 0x4dc00101, 0x8a400091, 0x5fc000d1, 0x3e47, 0x714000b1,
    0x1c60431013790, 0x2d903c28137b0, 0xcf003400001a, 0xb2400071, 0x25000dc00049, 0xd0003400001a,
    0xf9c00051, 0xcc003440001a, 0xafd0299413870, 0x3e87, 0xe0f00c88138d0, 0x1c74, 0x4e400101,
    0xcf003440001a, 0x27c0446013930, 0xb3000071, 0x8b400091, 0x720000b1, 0x1c84, 0xb3400071,
    0x14003dc00019, 0x8e04c40139d0, 0x105103f94139f0, 0x31000d400049, 0xfb400051, 0xde300c3013a30,
    0xca0034c0001a, 0x8bc00091, 0xcb0034c0001a, 0xfbc00051, 0x3ef7, 0x12400451, 0xfc000051,
    0xe7a014e013b10, 0xc340256013b50, 0xe940143013b70, 0x8c400091, 0x6a04d4813bb0, 0x1c003dc00019,
    0x121400da413bd0, 0x29000dc00049, 0x614000d1, 0x3af01de013c30, 0x3c400151, 0x14c003d1,
    0xfd400051, 0xc00035c0001a, 0x5c40383013cf0, 0x2a000dc00049, 0xc10035c0001a, 0xfdc00051,
    0x2b6035dc13d50, 0x1820496013d90, 0x1ce4, 0x24003dc00019, 0xfe400051, 0x18000351]
  ++ [0xb5c00071, 0x13000431, 0x4590005413e50, 0x1cf4, 0xc70035c0001a, 0x390367813ed0, 0xb6400071,
    0x740000b1, 0xc1101f8413f10, 0x87e004dc13f30, 0x624000d1, 0x43400131, 0x3f60011c13f90,
    0x744000b1, 0x2c003dc00019, 0xcc0035c0001a, 0x4c5035b013ff0, 0x100000051, 0x8e400091,
    0x100400051, 0xcf0035c0001a, 0xbdf03474140b0, 0xd00035c0001a, 0x50400101, 0xd10035c0001a,
    0x8ec00091, 0x18400351, 0xe510166014170, 0x101400051, 0x298001f1, 0x630000d1, 0x132904bd0141d0,
    0xd50035c0001a, 0xd8801a7014230, 0x8f400091, 0x98c048b014270, 0x1ab03d7c14290,
    0x10b700d14142d0, 0x4df001f0142f0, 0xcf003640001a, 0x3130448414330, 0xecc03ebc14350,
    0x102c00051, 0x40b7, 0xd1003640001a, 0x13401764143b0, 0x103000051, 0x40c7, 0x118701ca4143f0,
    0x90000091, 0x103400051, 0xb9400071, 0xd4003640001a, 0x90400091, 0xcc501e44144b0, 0x40f7,
    0xc6001d58144d0, 0x104000051, 0xd7003640001a, 0xb4f036fc14530, 0x104400051, 0xd9003640001a,
    0xe36005d4145d0, 0x104c00051, 0x15000f400049, 0x23400251, 0x4147, 0x105400051, 0x1db4,
    0xbac00071, 0x105800051, 0x88502fac146f0, 0x7620052c14710, 0x770000b1, 0x1dc4, 0x64c000d1,
    0x4187, 0xbb400071, 0x13000451, 0x106400051, 0x91c00091, 0x35000dc00049, 0x2d4001d1,
    0xd0003740001a, 0x108f023a814870, 0x130040c00019, 0x11f80510014890, 0x140040c00019,
    0x2ef0467c148d0, 0xeb504710148f0, 0x52400101, 0x107400051, 0xd4003740001a, 0x1df4, 0xbc400071,
    0xd5003740001a, 0x107c00051, 0x41f7, 0xd6003740001a, 0x108000051, 0x45b0411c14a10,
    0x3ce0008014a50, 0xd9003740001a, 0x131603db014ab0, 0x1c0040c00019, 0xda003740001a, 0x52c00101,
    0xdb003740001a, 0x5a003dc00019, 0x93400091, 0x1e24, 0xd3301e1c14b90, 0xd40037c0001a,
    0x70010400049, 0xbdc00071, 0xe000373014c30, 0x68b018b814c50, 0x5f003dc00019, 0x4287,
    0x20e03f2014cb0, 0x240040c00019, 0x10a400051, 0x9380169814cf0, 0x94000091, 0x2fc0225814d10,
    0xda0037c0001a, 0x12b0514814d70, 0x63003dc00019, 0x94400091, 0x26302b2814db0, 0x64003dc00019,
    0x10af0041c14dd0, 0x1d000f400049, 0xdd0037c0001a, 0x1e64, 0xde0037c0001a, 0x95102e5c14e70,
    0x19400351, 0x10bc00051, 0x42f7, 0xf7a01acc14ed0, 0x10c000051, 0xcd0038c0001a, 0x10c400051,
    0xcf0038c0001a, 0xd7801e1014fb0, 0x95400091, 0x10cc00051, 0x54000101, 0xd10038c0001a,
    0x307047fc15050, 0x10e704db815070, 0xd30038c0001a, 0x340040c00019, 0xd40038c0001a, 0x1ea4,
    0x54400101, 0xd50038c0001a, 0x10dc00051, 0x13000471, 0xc0c00071, 0xa0502c5415190,
    0x74003dc00019, 0x10e400051, 0x680000d1, 0x96400091, 0xc1400071, 0x1d50417015250, 0x47400131,
    0x77003dc00019, 0xdb0038c0001a, 0x107052ac152b0, 0x78003dc00019, 0x684000d1, 0x10f400051,
    0x96c00091, 0x164003d1, 0x5de03d6815370, 0xdf0038c0001a, 0x9f0050e4153b0, 0x7c003dc00019,
    0xe00038c0001a, 0xc2400071, 0x23000f400049, 0x3d1045c415410, 0x110400051, 0x1ef4,
    0xa0c0170815490, 0x103101660154d0, 0x4f05404154f0, 0x7c0000b1, 0x1f04, 0x19c00351, 0x4447,
    0x97c00091, 0x111400051, 0xfdd02230155b0, 0xde003940001a, 0x3890475c155f0, 0x85003dc00019,
    0xef9054d815610, 0xe0003940001a, 0x10e02b6015670, 0x98400091, 0x4c0040c00019, 0x112400051,
    0xc4000071, 0xff0485815710, 0x48400131, 0xe4003940001a, 0x3ce049c815770, 0xe5003940001a,
    0x8c003dc00019, 0x404045e8157d0, 0x6c404774157f0, 0x130010400049, 0x113400051, 0x86012a815850,
    0x7d4000b1, 0x25400251, 0x44f7, 0x99400091, 0x114000051, 0xdd052d415910, 0xc5400071,
    0x114400051, 0x3c300db015970, 0xd9003a40001a, 0xa2053e8159b0, 0x94003dc00019, 0xda003a40001a,
    0x29000f400049, 0xc5c00071, 0x2fc001d1, 0x5a0040c00019, 0x4547, 0x115400051, 0x13000491,
    0xde003a40001a, 0xbed02bd015af0, 0x2a000f400049, 0x9a400091, 0x14ef0031415b30, 0x97601c8c15b50,
    0x5f0040c00019, 0x14c00431, 0x116400051, 0x2b000f400049, 0x4500230815c10, 0x9ac00091,
    0xe4003a40001a, 0x116c00051, 0x630040c00019, 0x6b4000d1, 0xc7400071, 0xa0003dc00019]
  ++ [0x3760266815cd0, 0x57400101, 0x9d20135415d10, 0x91d0531415d30, 0x9b400091, 0x890553c15d70,
    0xe9003a40001a, 0xa4003dc00019, 0x304001d1, 0x7f4000b1, 0x118000051, 0xe1003ac0001a,
    0x144e01a8c15e30, 0x118400051, 0xc8400071, 0xe3003ac0001a, 0x127103c2415eb0, 0xa8003dc00019,
    0xe4003ac0001a, 0xe8c0229015ef0, 0x1a0010400049, 0xe5003ac0001a, 0xef60511c15f50,
    0x3220386415f70, 0xab003dc00019, 0x119400051, 0xac003dc00019, 0x6c4000d1, 0x150007c00089,
    0xf010222816010, 0x119c00051, 0x720040c00019, 0xea003ac0001a, 0x17a01ff016090, 0x804000b1,
    0x740040c00019, 0x59f05224160d0, 0x7f504ae4160f0, 0x58400101, 0x43400151, 0x32404bc016130,
    0x4200b9016150, 0x2024, 0xb3003dc00019, 0xd1003c40001a, 0x48304188161b0, 0xb4003dc00019,
    0x9d400091, 0xca400071, 0x31000f400049, 0x1802c5416210, 0xd4003c40001a, 0xd5003c40001a,
    0x11bc00051, 0x46f7, 0xcb103d50162d0, 0x9dc00091, 0x11c000051, 0xd7003c40001a, 0x1cb0477016330,
    0x11c400051, 0xd96025cc16390, 0xcb400071, 0xda003c40001a, 0x1f0010400049, 0x9e400091,
    0x8580166016430, 0x7fb0392c16450, 0x400154816490, 0x14b601064164b0, 0xde003c40001a,
    0xd5d023cc164f0, 0x59400101, 0xdf003c40001a, 0xe0003c40001a, 0x156300bfc16570, 0x2084,
    0xc4003dc00019, 0x11e400051, 0x14c00451, 0x35000f400049, 0xe3003c40001a, 0x4170493416630,
    0xccc00071, 0x15d50194416670, 0x25d0269416690, 0x8c0040c00019, 0xc42028b0166d0,
    0x47f05698166f0, 0x36000f400049, 0x11f400051, 0x15f0143016730, 0x90f054a816750, 0x9fc00091,
    0xad6050c416790, 0xdd802290167b0, 0x47f7, 0xea003c40001a, 0x120000051, 0x9f500a2016810,
    0x987007d816850, 0xa0400091, 0x31c001d1, 0x940040c00019, 0xee003c40001a, 0x120c00051,
    0x5a400101, 0x1b400351, 0x49402c8c16930, 0x23400291, 0xce800071, 0x121400051, 0xa0c00091,
    0xd4003dc00019, 0xde003d40001a, 0x1805a20169f0, 0x250010400049, 0xdf003d40001a,
    0x121f03cf816a30, 0xe0003d40001a, 0xd60575016a90, 0xcf400071, 0xd8003dc00019, 0x122400051,
    0x4897, 0x5a502c5816b10, 0x122800051, 0xe4003d40001a, 0xdb003dc00019, 0x45400151, 0x844000b1,
    0xdc003dc00019, 0x5210467416bd0, 0x1d0010c00049, 0x123400051, 0x7b2045f016c30, 0x324001d1,
    0xd0400071, 0x160e0095016c90, 0xe0003dc00019, 0x704000d1, 0xe1201cf816cf0, 0x124000051,
    0xa2400091, 0x2134, 0x124400051, 0xed003d40001a, 0x5030476416db0, 0xd1000071, 0x2144,
    0x4fa0479816df0, 0x180003d1, 0x101047c016e10, 0xd1400071, 0x529046f416e50, 0x16700251c16e70,
    0xab0040c00019, 0x125400051, 0xac0040c00019, 0x36200c2416ed0, 0x4d400131, 0x5bc00101,
    0xf3003d40001a, 0xa3400091, 0x2bb050fc16f90, 0x1bc00351, 0x126400051, 0xd2400071,
    0x2b0010400049, 0x714000d1, 0x14c00471, 0x126c00051, 0xb30040c00019, 0x2184, 0xf0003dc00019,
    0x46400151, 0xa4000091, 0x905c2417110, 0x864000b1, 0x116102a4417150, 0xa4400091, 0x127c00051,
    0x49f7, 0x1299043a4171d0, 0x21a4, 0x128000051, 0xe340507c17210, 0x317055d817230, 0x128400051,
    0x720000d1, 0x254014f417290, 0xe4003ec0001a, 0xd4000071, 0xe5003ec0001a, 0x6bf05abc17350,
    0xd4400071, 0x129400051, 0x4e400131, 0xa5400091, 0x8600a78173f0, 0x250010c00049,
    0x44004f6c17410, 0x28400251, 0xeb003ec0001a, 0x16400431, 0xc40040c00019, 0xec003ec0001a,
    0x5d400101, 0xed003ec0001a, 0xb060536817530, 0xee003ec0001a, 0x13340120817590, 0x49904b14175d0,
    0x159700abc175f0, 0x310010400049, 0x12b400051, 0x1c400351, 0xec5029c817690, 0x15cb016d8176b0,
    0xf4003ec0001a, 0xd6400071, 0x5dc00101, 0x4b07, 0x8b05bac17750, 0x41f05ca417770,
    0xf7003ec0001a, 0x2a005370177b0, 0xf8003ec0001a, 0xd10040c00019, 0x95502a1817810,
    0x7f70248017830, 0xa7400091, 0x12d400051, 0xd7400071, 0xd40040c00019, 0x2244, 0xee504094178f0,
    0x740000d1, 0xf3003f40001a, 0x15b10565c17950, 0xa7c00091, 0x4b87, 0xd9901acc179b0,
    0xd80040c00019, 0x12e400051, 0xd8000071, 0xf7003f40001a, 0x2264, 0xf8003f40001a, 0x12ec00051,
    0xdb0040c00019, 0xa8400091, 0x14c00491, 0xdc0040c00019, 0x89c000b1, 0x234002b1]
  ++ [0x5ec00101, 0x12f400051, 0x48400151, 0x133c0421817b90, 0xe00040c00019, 0xea004040001a,
    0x9a00184417bf0, 0x130000051, 0xeb004040001a, 0xd9400071, 0x130400051, 0xed004040001a,
    0xd9800071, 0x2bb0544417cb0, 0xa9400091, 0x22a4, 0x5f400101, 0x5e203a0817d10, 0x50400131,
    0x41004f1817d50, 0x131400051, 0x25400291, 0x131800051, 0xda400071, 0xf3004040001a, 0x22c4,
    0x34c001d1, 0x2ec053f817e90, 0x132400051, 0x8b4000b1, 0x5fc00101, 0xaa400091, 0x3fc04fe017f30,
    0xdb000071, 0xf8004040001a, 0xf9004040001a, 0x29a05b8017fb0, 0xf00040c00019, 0x16400451,
    0x29800251, 0x310010c00049, 0x133400051, 0xaac00091, 0x10da036fc18050, 0x22f4, 0x5930033c18070,
    0xfd004040001a, 0x6d04af4180b0, 0xab000091, 0xfe004040001a, 0x134000051, 0xdd5028f418110,
    0xa1c0013818130, 0x134400051, 0xadc05e3c18170, 0xf70040c00019, 0x31c001f1, 0x8c4000b1,
    0xf80040c00019, 0xf80040c0001a, 0x134c00051, 0x18004c000019, 0xf90040c0001a, 0x4d47,
    0x12600489c18290, 0x770000d1, 0xfc0040c0001a, 0x1031015bc182f0, 0xac000091, 0xfd0040c0001a,
    0xdd400071, 0xfe0040c0001a, 0xf8e0378418370, 0xac400091, 0x1000040c00019, 0x136400051,
    0x3f0010400049, 0x1010040c0001a, 0x18f05ad418430, 0x1020040c0001a, 0x136c00051,
    0x1030040c00019, 0x23103ab418490, 0xacc00091, 0x12805c98184d0, 0xde400071, 0x61400101,
    0x137400051, 0x2364, 0x8ec052c818550, 0x324001f1, 0xf30041c0001a, 0x137c00051, 0x4df7,
    0xdec00071, 0x138000051, 0x4e07, 0x9cd04c9818650, 0xf630243018670, 0x2384, 0xdf400071,
    0x784000d1, 0x138c00051, 0x2c004c000019, 0xf90041c0001a, 0x8e4000b1, 0x4e47, 0x139400051,
    0xfc0041c0001a, 0x6ed04268187f0, 0xe0000071, 0xae400091, 0x139c00051, 0x53403e0018850,
    0xe0400071, 0x5a060c018890, 0xc2a04e20188b0, 0x13a400051, 0x62400101, 0x14b8052a418910,
    0xe0c00071, 0x1030041c0001a, 0x10f05e3c189d0, 0x8f4000b1, 0x1d0012400049, 0xc89014a818a10,
    0xe1400071, 0x14c004c1, 0xaf400091, 0x21a05a3818a70, 0x1070041c0001a, 0xfe004240001a,
    0x16400471, 0x3c0010c00049, 0xe1c00071, 0x13c400051, 0x23f4, 0xafc00091, 0x101004240001a,
    0xbac0487418bb0, 0x102004240001a, 0x9f501a3418bf0, 0x900000b1, 0x154104b6018c10, 0x4f47,
    0x13d400051, 0x148c017b418cb0, 0x106004240001a, 0x63400101, 0x107004240001a, 0x16700400418d30,
    0x108004240001a, 0x33d0567418d90, 0xe3400071, 0xec805da018dd0, 0x3f0010c00049, 0xed0043c0001a,
    0xee0043c0001a, 0x17070407c18e90, 0xb1400091, 0xddb01cfc18ef0, 0x63c00101, 0x13f400051,
    0xf20043c0001a, 0xe4400071, 0xf30043c0001a, 0x10620341018fb0, 0x4ff7, 0x480401818fd0,
    0x140000051, 0xf50043c0001a, 0x54400131, 0x140400051, 0x254002b1, 0x374001d1, 0x91c000b1,
    0x64400101, 0xb2400091, 0x173103cc419130, 0x420635019150, 0x141400051, 0x553010f0191b0,
    0xfc0043c0001a, 0x18000431, 0xfd0043c0001a, 0x141c00051, 0x294013d019250, 0x5a004c000019,
    0x5087, 0xb3000091, 0x142400051, 0xe6400071, 0x7c0000d1, 0x1010043c0001a, 0x43d053dc19330,
    0xb3400091, 0x5ef04d2419370, 0x1030043c0001a, 0x5f004c000019, 0x13bf050c8193d0, 0x310011c00049,
    0x143400051, 0x37c001d1, 0x6750171019450, 0x1070043c0001a, 0x143c00051, 0x50f7,
    0x1080043c0001a, 0x12005174194f0, 0x144000051, 0x25905be419510, 0x144400051, 0x16700022c19570,
    0xe7c00071, 0x2bc05a80195b0, 0xca701360195d0, 0x68004c000019, 0x16400491, 0xf910575819630,
    0x5147, 0x24f4, 0xe8400071, 0xb440389819690, 0xfc0044c0001a, 0x940000b1, 0x7d4000d1,
    0x7e102b2819750, 0x119901f8419790, 0x944000b1, 0x146400051, 0x350011c00049, 0x110004400001a,
    0xe9400071, 0x1020044c0001a, 0x2524, 0x72004c000019, 0x1030044c0001a, 0x130c023ec198d0,
    0xb5c00091, 0x66400101, 0x147400051, 0x13bc041d819930, 0x1060044c0001a, 0x25005d2019970,
    0x4250480019990, 0x147c00051, 0x77004c000019, 0x532, 0x400532, 0x10000400533, 0x4c00532,
    0x7400532, 0xac00532, 0x14000532, 0x14400532, 0x13000532]
  ++ [0x10c00532, 0xbac00091, 0x150400051, 0x1214033e81a470, 0x115004640001a, 0x8a0009ac1a4d0,
    0x69400101, 0x117004640001a, 0xbb400091, 0xf01025481a570, 0x6fd010701a590, 0x1100046c0001a,
    0x10af0115c1a5f0, 0xa8004c000019, 0x1110046c0001a, 0x11110470c1a630, 0x3a4001d1, 0xbbc00091,
    0xbac03af81a690, 0x21047fc1a6b0, 0x164004c1, 0x152400051, 0x148a001801a6f0, 0xac004c000019,
    0x3d5020701a710, 0x1bc003d1, 0xc3b069c41a750, 0x152c00051, 0xbc400091, 0x24069681a7d0,
    0xf2400071, 0x450011c00049, 0x1190046c0001a, 0x9a4000b1, 0x11a0046c0001a, 0x9df042a41a870,
    0x7ed012401a890, 0x153c00051, 0x54f7, 0xc0901bbc1a8d0, 0xeec030141a8f0, 0x154000051,
    0x1090047c0001a, 0x81068541a950, 0x29800291, 0x5fb003f01a990, 0x13bf0072c1a9b0,
    0x10c0047c0001a, 0x18000471, 0x103004840001a, 0x26c4, 0x1051029f41aa70, 0x155400051,
    0x1100047c0001a, 0xbdc00091, 0xf4000071, 0x1110047c0001a, 0x1120047c0001a, 0xf4400071,
    0x5a000131, 0x3c202be01ab90, 0x26e4, 0x174705ea41abd0, 0x3f0012400049, 0xbe400091, 0x374001f1,
    0xf4c00071, 0x1170047c0001a, 0x99602c0c1acb0, 0x55c7, 0x6b400101, 0x157400051, 0xf5400071,
    0x11a0047c0001a, 0x3d705c041ad70, 0x11b0047c0001a, 0x157c00051, 0x55f7, 0x844000d1,
    0x158000051, 0x11d0047c0001a, 0x8cf0036c1ae30, 0x158400051, 0xc8901dc01ae70, 0x14c00531,
    0x1c4003d1, 0xf6400071, 0x6bc00101, 0x117004840001a, 0xc2a01aa01af50, 0xb8f0259c1af90,
    0xf6c00071, 0x2f90601c1aff0, 0x430012400049, 0x17c5034e01b010, 0xf7000071, 0x11c004840001a,
    0x9d4000b1, 0xc0400091, 0xf7400071, 0x15a400051, 0x6c400101, 0x854000d1, 0x2764,
    0x120004840001a, 0x16f200ef41b170, 0x7f04ba41b190, 0xc0c00091, 0x540000ac1b1d0, 0x20c00351,
    0xf8000071, 0x15b400051, 0x141e04e381b250, 0xf8400071, 0x2784, 0x56f7, 0xc1400091, 0x15c000051,
    0x37005f081b310, 0x9e4000b1, 0x15c400051, 0x19400451, 0xbfa03d081b3b0, 0x5e0043801b3d0,
    0x15cc00051, 0xe0004c000019, 0x117004940001a, 0xd75052a41b430, 0x864000d1, 0x15d400051,
    0x3c4001d1, 0x43d05c4c1b4f0, 0x480012400049, 0xf9c00071, 0xf9a0259c1b530, 0x27c4,
    0x6606bd01b590, 0x15e400051, 0x25400c881b5f0, 0x18000491, 0x191501f781b610, 0xc2c00091,
    0x120004940001a, 0x121004940001a, 0x27e4, 0x57c7, 0x6dc00101, 0x15f400051, 0x4f30659c1b730,
    0xc3400091, 0x27f4, 0x592, 0x400592, 0x10000400593, 0x15fc00051, 0x4c00592, 0x7400592,
    0xac00592, 0x14000592, 0x14400592, 0x13000592, 0x14c00592, 0x1ff068141c030, 0x3bf0619c1c250,
    0x28f4, 0x10301cb81c270, 0xc8400091, 0xf46033981c2b0, 0xe2048081c2d0, 0x168c00051, 0xa40000b1,
    0x118f04ac41c310, 0x14702a941c330, 0x169000051, 0x3e4001d1, 0x3a4001f1, 0x169400051,
    0xc8c00091, 0x11f004c00001a, 0x8a500d141c3f0, 0x120004c000019, 0x120004c00001a, 0x4005a400019,
    0x121004c00001a, 0x5f400131, 0x8b4000d1, 0xd78035881c4b0, 0x16a400051, 0x71400101,
    0x124004c00001a, 0x103000071, 0x125004c00001a, 0x185a00ff81c570, 0x126004c00001a, 0x103400071,
    0x2944, 0x128004c000019, 0xe0022901c610, 0x8bc000d1, 0x129004c00001a, 0x1a90007601c670,
    0x4a703ebc1c690, 0x5fc00131, 0x3ec001d1, 0x16c000051, 0xca400091, 0x16c400051, 0x104400071,
    0x12e004c00001a, 0x8c4000d1, 0xc9d03f141c7f0, 0x72000101, 0x52e03ac41c810, 0xcac00091,
    0x14005a400019, 0x104c00071, 0xc6d00aec1c870, 0x16d400051, 0x12e004c40001a, 0x72400101,
    0x553041401c910, 0xc8e054b81c930, 0x18005a400019, 0xcb400091, 0x785054541c990, 0x105800071,
    0x16e400051, 0x490013400049, 0x57400151, 0x1ca06b681ca30, 0x1c005a400019, 0x58002fd81ca50,
    0x16ec00051, 0x12b004cc0001a, 0x5bc7, 0x106400071, 0x4a0013400049, 0x16f400051, 0x29c4,
    0x21d06a6c1cb70, 0xcc400091, 0x171f058001cbb0, 0x43e065581cbd0, 0xa74000b1, 0x3c0014000049,
    0x131004cc0001a, 0x31c00251, 0x24005a400019, 0x170400051, 0x22c00351, 0x496027fc1cc90,
    0x107400071, 0x184004c1, 0x6b04ed41ccd0, 0x73400101, 0x121004dc0001a]
  ++ [0x1720016d81cd50, 0x29f4, 0x50903e4c1cd90, 0x16400531, 0xcd400091, 0x61400131, 0x108000071,
    0x2a04, 0x2c005a400019, 0x8e4000d1, 0x14520320c1ce70, 0x5c87, 0xd49006841ceb0, 0x62b05b0c1ced0,
    0xcdc00091, 0x73c00101, 0x129004dc0001a, 0x48f061941cf30, 0x58400151, 0x130a02dbc1cf70,
    0xd2b024201cf90, 0x66c06c381cfd0, 0x295034241cff0, 0x74000101, 0x173400051, 0x90e0606c1d030,
    0x34005a400019, 0x12e004dc0001a, 0x12f004dc0001a, 0xce800091, 0x5cf7, 0x32400251, 0x174000051,
    0x9d9037301d110, 0x4dc055801d150, 0xa94000b1, 0x8f4000d1, 0x5b005db01d1b0, 0x404001d1,
    0x174c00051, 0x420014000049, 0x135004dc0001a, 0x2a64, 0xcf400091, 0x175400051, 0x5d57,
    0x62400131, 0x556061f41d2d0, 0x175800051, 0x9069301d2f0, 0x430014000049, 0x23400351,
    0x40005a400019, 0x14bf03ea01d350, 0x4a0062681d390, 0x176400051, 0x900000d1, 0x133004e40001a,
    0xaa4000b1, 0x134004e40001a, 0x10bc00071, 0x100a017b41d4d0, 0x2aa4, 0x10c000071, 0x177400051,
    0x971009781d530, 0x138004e40001a, 0x10c400071, 0xaac000b1, 0x2ab4, 0x126004f40001a,
    0x13cf015cc1d5f0, 0x460014000049, 0x1b400451, 0xd1000091, 0x178400051, 0x129004f40001a,
    0xd1400091, 0xab4000b1, 0x470014000049, 0x84e01ea81d710, 0xa6073401d750, 0x652068e81d770,
    0x179400051, 0x12e004f40001a, 0x480014000049, 0x10dc00071, 0x78e057d81d830, 0x54005a400019,
    0x130004f40001a, 0x2af4, 0x5a000151, 0x597014481d890, 0x132004f40001a, 0x10e400071, 0xac0000b1,
    0xd2400091, 0x1c400431, 0x1286020241d950, 0x135004f40001a, 0xac4000b1, 0x5a005a400019,
    0x63c00131, 0x4a0014000049, 0x8d3016601da10, 0x138004f40001a, 0x373068d41da70, 0x139004f40001a,
    0x3ab0010c1dab0, 0x5ef7, 0x13a004f40001a, 0x17c000051, 0xdee072cc1db10, 0x143056101db30,
    0x17c400051, 0x5b1050e41db90, 0x2b44, 0x77000101, 0x135004fc0001a, 0x983031b01dc30,
    0x64005a400019, 0x7d075241dc50, 0x110400071, 0x17d400051, 0x138004fc0001a, 0xd4000091,
    0x139004fc0001a, 0x2b64, 0x68005a400019, 0x492020e01dd50, 0x789048dc1dd70, 0xd4400091,
    0x144a041d01ddd0, 0x4e0014000049, 0x13d004fc0001a, 0x111400071, 0x13e004fc0001a,
    0x17fb017b41de70, 0x1cbc048401de90, 0x1bc00451, 0x5fc7, 0x612, 0x400612, 0x10000400613,
    0xae4000b1, 0x4c00612, 0x7400612, 0xa400612, 0xac00612, 0x14000612, 0x18000612, 0x18400612,
    0x17c00612, 0x16c00612, 0x43c001d1, 0xa0005a400019, 0x5c6011041eb50, 0x87904f901eb90, 0x2cb4,
    0xcbb016e41ebb0, 0x142005240001a, 0x189800051, 0x4d0014c00049, 0xaf4015c81ec10, 0x189c00051,
    0xb30000b1, 0x2cc4, 0x1bc00471, 0xdb000091, 0x18a400051, 0xb34000b1, 0x4e0014c00049,
    0x119c00071, 0xadc04f281ed30, 0xa8005a400019, 0xdb400091, 0x15d040041ed70, 0x25400351,
    0xf0803f581edd0, 0xe710756c1edf0, 0x68000131, 0x18b400051, 0xac005a400019, 0x1420052c0001a,
    0x2cf4, 0x14d607a501ee90, 0x62f7, 0x984000d1, 0x18c000051, 0x16400591, 0x68400131, 0x18c400051,
    0xdc400091, 0x8f2008ec1efb0, 0x98605c9c1efd0, 0x7c000101, 0x1490052c0001a, 0xb4005a400019,
    0x6347, 0x18d400051, 0x1380053c0001a, 0x25a077341f0f0, 0x11c000071, 0x1390053c0001a,
    0x5ef041bc1f130, 0x133d002681f150, 0x11c400071, 0x6387, 0x6400630c1f1b0, 0x18e400051,
    0x404001f1, 0x18000531, 0x56d02edc1f210, 0x13e0053c0001a, 0x18ec00051, 0x63b7, 0x13f0053c0001a,
    0x652, 0x400652, 0x10000400653, 0x4c00652, 0x7400652, 0xac00652, 0x13000652, 0x18000652,
    0x19400652, 0x14000652, 0x17c00652, 0x122800071, 0x5400672, 0x4000672, 0x7c00672, 0xac00672,
    0x672, 0x10000400673]

def stageA1 : List (Nat × List Nat) :=
  [(4096, opsA4096)]

def opsA8192_0 : List Nat :=
  [0x5400672, 0x4000672, 0x7c00672, 0xac00672, 0x672, 0x10000400673, 0x18000672, 0x14000672,
    0x18c00672, 0x14c00672, 0x10c005a400019, 0x19c00672, 0x118005a400019, 0x144a0646c20990,
    0xbdc000b1, 0x4d0016400049, 0x700676020a10, 0x11c005a400019, 0x158005740001a, 0x8d40714820a70,
    0x5a0064000019, 0xe8400091, 0x1a2400051, 0x82c00101, 0x15b005740001a, 0x346075b820b30,
    0x120005a400019, 0x15c005740001a, 0x1a2c00051, 0x68b7, 0x114600cb420b90, 0x12b400071,
    0x1a3000051, 0x484001d1, 0x19400531, 0x450016c00049, 0x1a3400051, 0x124005a400019,
    0x2ec00acc20c50, 0x7be0041c20c90, 0x68f7, 0xe9400091, 0x38c00251, 0x1a4000051, 0xab1082dc20d10,
    0x128005a400019, 0x3380767820d50, 0x134f048e820d70, 0x151005840001a, 0x152005840001a,
    0x1a4c00051, 0x680064000019, 0x1490058c0001a, 0x93001ea420e30, 0x64400151, 0x1a5400051,
    0x156005840001a, 0x1073041f420ef0, 0x480016c00049, 0xea400091, 0x1c470565c20f30, 0x1bc004c1,
    0xa24000d1, 0x6987, 0x3ce073bc20fb0, 0x1a6400051, 0x530016400049, 0x3004, 0x134005a400019,
    0x15c005840001a, 0x1a6c00051, 0x720064000019, 0x15d005840001a, 0x16e9071c4210b0,
    0x140068c00019, 0xc108134210d0, 0x12e400071, 0x84400101, 0xff40562021110, 0x138005a400019,
    0xeb400091, 0x3024, 0x11ee0297421190, 0x1a7c00051, 0x770064000019, 0x12ec00071,
    0x1be4002d4211f0, 0x1a8000051, 0xc0c000b1, 0x1a8400051, 0xa34000d1, 0x12f400071,
    0x1c0068c00019, 0x3044, 0x7c0064000019, 0x15d0058c0001a, 0x140005a400019, 0x3df0755c21350,
    0xc14000b1, 0x1a9400051, 0x1600058c0001a, 0x130000071, 0x1610058c0001a, 0x18370805021430,
    0x144005a400019, 0x1620058c0001a, 0x130400071, 0xdd01fa021490, 0x240068c00019, 0x1aa400051,
    0x3e5056b8214f0, 0xa40000d1, 0x1510059c0001a, 0x70400131, 0x850064000019, 0x28400351, 0x3084,
    0x1b6105d88215b0, 0xed400091, 0x18000591, 0x1ab400051, 0x131400071, 0x14c005a400019,
    0x19c00531, 0x1570059c0001a, 0x131800071, 0x2c0068c00019, 0x31c002b1, 0x30a4, 0x8c0064000019,
    0x1590059c0001a, 0xeed02c1c21730, 0x1ac400051, 0xa1b06b9421790, 0x15c0059c0001a, 0x1acc00051,
    0x900064000019, 0xee400091, 0x154005a400019, 0x450074d821850, 0x1ad400051, 0xa4028c4218b0,
    0x1c4004c1, 0x66400151, 0x190402230218f0, 0x86400101, 0xda7030b021910, 0x1adc00051,
    0x158005a400019, 0x1620059c0001a, 0xb62012d421970, 0x234003d1, 0x133400071, 0x81f065fc219d0,
    0x71400131, 0x530016c00049, 0x1650059c0001a, 0x6d2, 0x4006d2, 0x100004006d3, 0x7480501c21a70,
    0x4c006d2, 0x74006d2, 0xac006d2, 0x140006d2, 0x184006d2, 0x180006d2, 0x194006d2, 0x1b4006d2,
    0x2af0772c227b0, 0x56007480227f0, 0x4d0017c00049, 0x153c005d422810, 0x74400131, 0xd10064000019,
    0x162005cc0001a, 0x1610445022870, 0x69400151, 0x740068c00019, 0x1ba400051, 0x8a400101,
    0x165005cc0001a, 0xaa4000d1, 0x1bac00051, 0x770068c00019, 0x167005cc0001a, 0x780068c00019,
    0x36807cd8229d0, 0xd80064000019, 0x1bb400051, 0x5020066822a50, 0x16b005cc0001a, 0x1bbc00051,
    0x6ef7, 0x16c005cc0001a, 0xaac000d1, 0x1bc000051, 0x6f07, 0x13d400071, 0x1bc400051,
    0x191c048cc22b70, 0x3284, 0xf7000091, 0x170005cc0001a, 0xe00064000019, 0x1b670047022c10,
    0xca4000b1, 0xf7400091, 0x4cc001d1, 0x1bd400051, 0x16a005d40001a, 0x1db300e1022cf0, 0x8b400101,
    0x16b005d40001a, 0x10120569822d30, 0x15b00256822d50, 0xf7c00091, 0x3300635422d90,
    0x111803c1c22db0, 0x1be400051, 0x712, 0x400712, 0x10000400713, 0x4c00712, 0x7400712, 0xac00712,
    0x14000712, 0x1bc00712, 0x1c000712, 0x1b400712, 0x18000712, 0x1c400712, 0x113400a8023c30,
    0x2c0070400019, 0xa0d07ad823c50, 0x1908ec423c90, 0x147400071, 0xc40068c00019, 0x1ca400051,
    0x19c00591, 0x8f400101, 0x179005fc0001a, 0x170006040001a, 0x1cac00051, 0x147c00071,
    0x12107fac23dd0, 0x1280064000019, 0x1cb400051, 0x3434, 0x25a04f2423e30, 0x340070400019,
    0xff400091, 0x174d01ac023e70, 0x17f005fc0001a, 0xd10000b1, 0x3444]
  ++ [0x7a054dc23ef0, 0x460019400049, 0x177006040001a, 0x1cc400051, 0xd14000b1, 0x179006040001a,
    0xdd5065f423fb0, 0x3e400251, 0x1f7b0680423ff0, 0x100000091, 0x8a00460424010, 0x149400071,
    0x10e08be024050, 0x1cd400051, 0xd40068c00019, 0x17e006040001a, 0x90400101, 0x17f006040001a,
    0x400070400019, 0x180006040001a, 0xa920662024190, 0xd80068c00019, 0x100302380241d0,
    0x4006638241f0, 0x1380064000019, 0x16f006140001a, 0xd24000b1, 0x1161003f824250, 0xdb0068c00019,
    0x171006140001a, 0xdc0068c00019, 0x14ac00071, 0x4a0019400049, 0x1cf400051, 0xb24000d1,
    0x175006140001a, 0x1cfc00051, 0xe00068c00019, 0xb2a0878c243d0, 0x101c00091, 0x1400064000019,
    0xa5a067a024410, 0x4c0070400019, 0x1d0400051, 0xcdf03e4424470, 0x179006140001a,
    0x1700061c0001a, 0x1d0c00051, 0x14c000071, 0x102400091, 0x4c507e4424550, 0x14c400071,
    0x1ef90158424590, 0x38c00291, 0xb30000d1, 0x504001d1, 0x7c707264245f0, 0x18400601,
    0xcb006f6c24610, 0x102c00091, 0x540070400019, 0x254049e424650, 0x34f4, 0x16830310824670,
    0xb34000d1, 0x103000091, 0x1d2400051, 0xd40000b1, 0x81a05a5c24710, 0x1ecb0156424730,
    0x103400091, 0x170b081b824770, 0x36c044bc24790, 0xd44000b1, 0xf00068c00019, 0x7c0072f8247d0,
    0x2e103278247f0, 0x450019c00049, 0x1d3400051, 0x118003ed024850, 0x103c00091, 0x17f0061c0001a,
    0x3ab08384248b0, 0x74f7, 0x1800061c0001a, 0x1d2000ed4248f0, 0x1d4000051, 0x1810061c0001a,
    0x1d4400051, 0xf70068c00019, 0x104400091, 0xcb705f94249b0, 0xf80068c00019, 0x1f7a04c84249d0,
    0x1d4c00051, 0x1580064000019, 0x1850061c0001a, 0x1c400531, 0x640070400019, 0x7547,
    0x150507b6424a70, 0x1d5400051, 0x14f400071, 0xfc0068c00019, 0x8fc0867c24ad0, 0x82090b824af0,
    0x15c0064000019, 0x1750062c0001a, 0x10cb024fc24b30, 0x680070400019, 0x1f81069d024b50, 0x7587,
    0x1000068c00019, 0x1d6400051, 0x530019400049, 0x141d0483024c10, 0x170006340001a, 0x105800091,
    0x1d6c00051, 0x1030068c00019, 0x3584, 0x1040068c00019, 0x6a90789424cd0, 0x93400101,
    0x1d7400051, 0xd64000b1, 0x70400151, 0x7740759024d70, 0x257084e824d90, 0x1080068c00019,
    0x1800062c0001a, 0xa1d00b7424df0, 0x550019400049, 0x106400091, 0x215608ee824e30,
    0x1690064000019, 0x1d8400051, 0x23400431, 0x1830062c0001a, 0xb5c000d1, 0x10c0068c00019,
    0x1840062c0001a, 0xd5b016d824ef0, 0x16c0064000019, 0x111105c2824f10, 0x106c00091,
    0x780070400019, 0x34d086a424f50, 0x1d9400051, 0x1880062c0001a, 0x152400071, 0x94000101,
    0x1890062c0001a, 0x1d9c00051, 0x7677, 0x107400091, 0x1da000051, 0x24150215c25090,
    0x1140068c00019, 0x1cb0036a4250d0, 0x94400101, 0x183006340001a, 0xf95055fc25130,
    0x184006340001a, 0x35f4, 0x1dac00051, 0x76b7, 0x185006340001a, 0x1db000051, 0x76c7, 0x374002b1,
    0x108000091, 0x16a203a0025210, 0x40400251, 0x96706f0425270, 0x850070400019, 0x153c00071,
    0xd84000b1, 0x11c0068c00019, 0x7aa03e14252d0, 0x7d400131, 0x154000071, 0x54507fb425310,
    0x1dc400051, 0x15c50288825370, 0x22c7006a425390, 0x1200068c00019, 0x17f006400001a,
    0x1800064000019, 0x180006400001a, 0x8c0070400019, 0x524001d1, 0x1dd400051, 0x65a03310254b0,
    0x1240068c00019, 0x109400091, 0x75e077c8254f0, 0x95400101, 0x3a400291, 0x1ddc00051,
    0x900070400019, 0x185006400001a, 0xd94000b1, 0x3654, 0x7787, 0xa6607a2c255b0, 0x1280068c00019,
    0x1de400051, 0x109c00091, 0x5d0019400049, 0x188006400001a, 0xd98000b1, 0x3664, 0x940070400019,
    0x189006400001a, 0x1dec00051, 0x72000151, 0x194503b1025690, 0x4d4001f1, 0x1df000051,
    0x1db300398256d0, 0xc9501e78256f0, 0x18c0064000019, 0x1df400051, 0x16e60120825750, 0x22c00451,
    0x2d400351, 0xb1200314257b0, 0x18f0064000019, 0x72400151, 0x52c001d1, 0x1900064000019,
    0x29a041b825810, 0x10ac00091, 0x1e0400051, 0x62304a4825870, 0x18d006440001a, 0x157400071,
    0x1340068c00019, 0x11cd03038258d0, 0x36a4, 0x96400101, 0x18f006440001a, 0x53a0452825930,
    0xa00070400019, 0x7847, 0x1e1400051, 0x36b4, 0x1380068c00019, 0x1880064c0001a, 0x1e1800051,
    0xb2007d24259f0, 0x158000071, 0xb94000d1, 0xdb0000b1, 0x36c4]
  ++ [0x158400071, 0x8e001bb025a90, 0x33a04ed825ab0, 0x240076c00019, 0x1e2400051, 0x13bb0401825af0,
    0x10c000091, 0x10500355c25b10, 0xa80070400019, 0x18e0064c0001a, 0x720951825b70, 0x130077c00019,
    0x10c400091, 0x1400068c00019, 0x1340922825bd0, 0xab0070400019, 0x266045a425c10, 0xc50100825c30,
    0xac0070400019, 0x1920064c0001a, 0x36f4, 0x7f400131, 0x1930064c0001a, 0x1e3c00051, 0x78f7,
    0x1800065c0001a, 0x112502d8425cf0, 0x1e4000051, 0x73400151, 0x1e4400051, 0x1830065c0001a,
    0x1c110272c25db0, 0x1c0077c00019, 0x1840065c0001a, 0xb7607b0025df0, 0x19400601,
    0x1850065c0001a, 0xb40070400019, 0x1b400591, 0x4e4001f1, 0x1e5400051, 0x14c0068c00019,
    0x16f2090fc25ed0, 0x10dc00091, 0x97c00101, 0x1890065c0001a, 0x1e5c00051, 0x18a0065c0001a,
    0x6bf079d025f90, 0x15b400071, 0x240077c00019, 0x1e6400051, 0x5d0019c00049, 0x10e400091,
    0x18e0065c0001a, 0xdd4000b1, 0xbb4000d1, 0x13b602b40260b0, 0x1540068c00019, 0x79c7,
    0x15c000071, 0x1e7400051, 0x80400131, 0x1920065c0001a, 0x15c400071, 0x1930065c0001a,
    0x105d01fac261b0, 0x1580068c00019, 0x1940065c0001a, 0x5f0019c00049, 0x38c002b1,
    0x11f80221026230, 0xc40070400019, 0x1e8400051, 0x1270041426290, 0x15c0068c00019, 0x544001d1,
    0x600019c00049, 0x18f006640001a, 0x15d400071, 0x1670933c26350, 0x10fc00091, 0x244e07ccc26390,
    0x8510698c263b0, 0x340077c00019, 0xbc4000d1, 0x6fe07d08263f0, 0x610019c00049, 0x1fff0515426410,
    0x135b0668026450, 0x110400091, 0x1640068c00019, 0x1ea400051, 0x15e400071, 0x99400101,
    0x197006640001a, 0x13b0946426530, 0x37c4, 0xdb023e426570, 0xd10070400019, 0x71000eec26590,
    0x110c00091, 0x284003d1, 0xdf4000b1, 0x1690068c00019, 0x1eb400051, 0xd40070400019,
    0x37c08de026650, 0x189006740001a, 0x10a802b28266b0, 0x16c0068c00019, 0x111400091,
    0x640019c00049, 0x7b07, 0xd80070400019, 0x1ec400051, 0x37f4, 0x1bc5082e826770, 0x15fc00071,
    0xbe506a5c267b0, 0x18e006740001a, 0xe00000b1, 0x3804, 0x41804a3826830, 0xdc0070400019, 0x7b47,
    0x160400071, 0x1ed400051, 0xe04000b1, 0x1740068c00019, 0x13bf05be0268d0, 0xe9f05fc4268f0,
    0x9a400101, 0x112400091, 0x7b77, 0x194006740001a, 0x1bc00591, 0x1ee000051, 0xfa0529826990,
    0x170c027a0269b0, 0x4c0077c00019, 0x1ee400051, 0x19c00601, 0xe0c000b1, 0x161400071,
    0x210000ab426a50, 0x7bb7, 0x199006740001a, 0x1c830927826ab0, 0x1ef000051, 0x5ca0018c26ad0,
    0x9ac00101, 0x1ef400051, 0x113400091, 0xe14000b1, 0x19d006740001a, 0x1800068c00019,
    0x1940067c0001a, 0xdb403fb826bf0, 0x3c001c000049, 0x1950067c0001a, 0x3864, 0x1f0400051,
    0x1970067c0001a, 0x1480961026cb0, 0x1840068c00019, 0xe1c000b1, 0x1d460911c26cf0, 0x114000091,
    0x17180179026d10, 0xf00070400019, 0x6eb07fac26d50, 0x400088c26d70, 0x1f1400051, 0x163400071,
    0x19c0067c0001a, 0x504001f1, 0x4d001b400049, 0x43400251, 0x2e30997826e30, 0x20c004c1,
    0x19e0067c0001a, 0x5f0077c00019, 0x16740226826e90, 0x18c0068c00019, 0xb6c004e026ed0,
    0x164000071, 0x18d0068c0001a, 0xf80070400019, 0x22660834c26f50, 0x1f2c00051, 0x18f0068c00019,
    0x18f0068c0001a, 0x1f3000051, 0x115400091, 0x25400431, 0x40001c000049, 0x1f3400051,
    0xfc0070400019, 0x38c4, 0x190a01c3c27070, 0x1930068c0001a, 0x20570704c270b0, 0x77000151,
    0x10e7005a0270d0, 0x115c00091, 0x1950068c0001a, 0x24e404eec27130, 0x1000070400019, 0x1f4400051,
    0x4650105027190, 0x23400471, 0x1980068c00019, 0x1980068c0001a, 0x1030070400019, 0x165c00071,
    0x3a4002b1, 0x1040070400019, 0x25430078c27250, 0xc0c000d1, 0x1f5400051, 0x12a07a64272b0,
    0x19c0068c00019, 0x19c0068c0001a, 0x166400071, 0x850076c00019, 0x3904, 0x1f5c00051,
    0x1080070400019, 0x19e0068c0001a, 0x5ee03a4c27370, 0x7d87, 0xe44000b1, 0x1a00068c00019,
    0x234007010273d0, 0x53001b400049, 0xc14000d1, 0x84400131, 0x10c0070400019, 0x117400091,
    0x81007ce027470, 0x7db7, 0x1c400591, 0x167400071, 0x1f7000051, 0x78e07f00274d0, 0x9d400101,
    0x1f7400051, 0x17540498427550, 0x19d006940001a, 0x1f7c00051, 0x7df7, 0x3944, 0x1f8000051,
    0x19f006940001a, 0x1140070400019]
  ++ [0x17d3082a827650, 0x258504b1827670, 0x118400091, 0x1c809690276b0, 0x940076c00019,
    0x1a9d04d7c276d0, 0x9dc00101, 0x1a3006940001a, 0x1380601c27730, 0x1180070400019, 0x168c00071,
    0x1f9400051, 0x118c00091, 0x169000071, 0x192006a40001a, 0x1105059ec277f0, 0x850077c00019,
    0x193006a40001a, 0x1f9c00051, 0x11c0070400019, 0x21e30824427850, 0x574001d1, 0x2fc00351,
    0x24007cc00019, 0x1fa400051, 0x298003d1, 0x103105f68278f0, 0x9e400101, 0x197006a40001a,
    0xe64000b1, 0x1200070400019, 0x198006a40001a, 0x13007dc00019, 0x199006a40001a, 0xa00076c00019,
    0x8a007bf8279d0, 0x16a400071, 0x59001b400049, 0xbd0302827a10, 0x237e07c7427a30,
    0x1240070400019, 0x19c006a40001a, 0x10db05b3427a70, 0x222b05f3427a90, 0xa40076c00019,
    0x23b003d5027ad0, 0x291047c427af0, 0x46001c400049, 0x11a400091, 0x1280070400019, 0x1fc400051,
    0x1a1006a40001a, 0xc3a0394427bb0, 0xa80076c00019, 0x1a2006a40001a, 0x1fcc00051, 0x5b001b400049,
    0x5c604a9427c10, 0x5a90887427c50, 0xab0076c00019, 0x1fd400051, 0x39e4, 0xac0076c00019,
    0x1a6006a40001a, 0x16c000071, 0x1a7006a40001a, 0x1300070400019, 0x11b400091, 0x16c400071,
    0x148a04d4027d90, 0x86400131, 0x24007dc00019, 0x1323018b827dd0, 0x5d001b400049, 0x3e400291,
    0x7b1080cc27e30, 0x1340070400019, 0x180306cac27e50, 0x1fec00051, 0x7fb7, 0x1a3006ac0001a,
    0xe84000b1, 0x1ff000051, 0x7fc7, 0x11c000091, 0x1ff400051, 0x16d400071, 0x1380070400019,
    0x30400351, 0x3990815427f70, 0x11c400091, 0xa40077c00019, 0x584001d1, 0xa0000101,
    0x1db30827028010, 0x200400051, 0x1ef008c5028090, 0x26400431, 0xa80077c00019, 0x3a44,
    0x16e400071, 0xa0400101, 0xc54000d1, 0x1400070400019, 0x3e9019c028150, 0xe94000b1,
    0xab0077c00019, 0x201400051, 0xac0077c00019, 0x16ec00071, 0x2aa095d8281f0, 0x61001b400049,
    0xbbf01f8c28210, 0x1440070400019, 0x19e006bc0001a, 0x20390894428270, 0x25400451, 0x16f400071,
    0xc40076c00019, 0x202400051, 0xa0c00101, 0x1a1006bc0001a, 0x12c1055cc28330, 0x23400491,
    0x202c00051, 0xb30077c00019, 0x5e20580028390, 0xb40077c00019, 0xb0a074d0283d0,
    0x11d400194283f0, 0x63001b400049, 0x203400051, 0xea4000b1, 0x14c0070400019, 0xc64000d1,
    0x170400071, 0x1a7006bc0001a, 0x54007cc00019, 0x1a8006bc0001a, 0xa1400101, 0xa65077b428510,
    0x11ec00091, 0x204400051, 0x1ab006bc0001a, 0x5a0a008285b0, 0x1c007fc00019, 0xb08069b8285d0,
    0xd10076c00019, 0x1ad006bc0001a, 0x27a703e4c28630, 0x1540070400019, 0x11f400091, 0x205400051,
    0xd40076c00019, 0x832, 0x400832, 0x10000400833, 0x594001d1, 0x4c00832, 0x5400832, 0xac00832,
    0x14000832, 0x1e400832, 0x18000832, 0x1f400832, 0x20c00832, 0x1c000832, 0xf70077c00019,
    0x1900070400019, 0x13000dc00099, 0xfc0077c00019, 0x1940070400019, 0x5f007fc00019,
    0x1140076c00019, 0x67001c000049, 0xb5c06fec29710, 0x1980070400019, 0x1b6006ec0001a,
    0x1111028e429770, 0x84b7, 0x1b7006ec0001a, 0x14ad01660297b0, 0x213000051, 0x1bc502584297d0,
    0x68001c000049, 0x213400051, 0x1ba20631029830, 0x19c0070400019, 0x127400091, 0x530a4d429870,
    0x21560308429890, 0x11c0076c00019, 0x3d500238298d0, 0xae088a4298f0, 0x214000051,
    0x1b3006f40001a, 0x5bc001d1, 0x1a00070400019, 0x214400051, 0x17c400071, 0x3c84,
    0x10a0a248299b0, 0x1200076c00019, 0x32400351, 0x21a101ffc299f0, 0x128000091, 0x16a0684429a10,
    0xf24000b1, 0x1a40070400019, 0x8547, 0xab007cc00019, 0x215400051, 0x1240076c00019,
    0x1ba006f40001a, 0x3ca4, 0x66001c400049, 0x27db02dd829b10, 0x215c00051, 0x1a80070400019,
    0x1bc006f40001a, 0x1b3503a1429b90, 0x1280076c00019, 0x1c1a03fa029bd0, 0x2e906de429bf0,
    0x6c001c000049, 0x7f400151, 0x340a64029c30, 0x48400251, 0x216c00051, 0xb3007cc00019,
    0x1ad007040001a, 0x26e40574829cb0, 0x1180077c00019, 0x129400091, 0x8580719829cf0, 0xa7400101,
    0x22c301c3c29d10, 0x3e4002b1, 0x1b00070400019, 0x1b0007040001a, 0xcac074b029d70,
    0x1b1007040001a, 0x9c3026f029db0, 0x234004c1, 0xf0776429dd0, 0x218000051, 0x269b09c3829e10,
    0x16f90139c29e30, 0x1b40070400019, 0x218400051, 0x3cf4, 0x1b5007040001a, 0x17f400071,
    0x1340076c00019, 0x1b6007040001a, 0x218c00051]
  ++ [0xf40000b1, 0x3d04, 0xce8000d1, 0x8647, 0xab007dc00019, 0x8dd05fa829f90, 0xf44000b1,
    0x1380076c00019, 0x1ba007040001a, 0x180000071, 0x729057882a010, 0x1bc0070400019,
    0x1bc007040001a, 0x180400071, 0x8687, 0x1280077c00019, 0x21a400051, 0x1bc00611, 0xa8400101,
    0xf4c000b1, 0x1038067702a130, 0x1c00070400019, 0x180c00071, 0x21ac00051, 0x86b7, 0xcf4000d1,
    0x21b000051, 0xb7607aa02a1d0, 0x6d001c400049, 0x21b400051, 0x181400071, 0xd20072542a250,
    0x21b800051, 0x12bc00091, 0x14b703a582a290, 0x1440076c00019, 0x1bc0070c0001a, 0x46001e400049,
    0x1bd0070c0001a, 0xa9007e982a350, 0x12c400091, 0x8e400131, 0x1340077c00019, 0x1c00070c0001a,
    0x21cc00051, 0xd1007cc00019, 0x5d4001d1, 0x176809a982a430, 0x8747, 0x21d400051,
    0x14c0076c00019, 0x182c00071, 0x36c09b902a4f0, 0xa9400101, 0x27400451, 0xf64000b1,
    0x4b60406c2a550, 0x8787, 0x6210a51c2a5b0, 0xd8007cc00019, 0x21e400051, 0x3da4, 0x1c400601,
    0x1232007882a610, 0x1b60071c0001a, 0xdb007cc00019, 0x183c00071, 0x3db4, 0x1540076c00019,
    0x3af041982a6d0, 0x26400471, 0x184000071, 0x21f400051, 0xf70000b1, 0x3dc4, 0x184400071,
    0x20c00531, 0x5dc001d1, 0x1580076c00019, 0x25400491, 0xf74000b1, 0x220000051, 0x12e400091,
    0x29ad064942a850, 0x8f400131, 0x1bf0071c0001a, 0x63098fc2a8b0, 0x15c0076c00019,
    0x1c00071c0001a, 0x24d5023f82a8f0, 0xaa400101, 0x1c10071c0001a, 0x185400071, 0x5a0083c00019,
    0x1b9802cac2a950, 0x3df4, 0x10fc0a2e02a970, 0xab007fc00019, 0x221400051, 0x14c0077c00019,
    0xb89019a42a9d0, 0xf80000b1, 0x3e04, 0x12f400091, 0x5f0083c00019, 0xe420a9002aa90, 0xf84000b1,
    0x1640076c00019, 0x222400051, 0x659049c82aaf0, 0xaac00101, 0x1bf007240001a, 0xd24000d1, 0x3e24,
    0xdb007dc00019, 0x1c1007240001a, 0x545066382abb0, 0x1540077c00019, 0x186c00071, 0x584001f1,
    0x130000091, 0x223400051, 0x1c4007240001a, 0x130400091, 0x223c00051, 0x16c0076c00019,
    0x13d2031242acd0, 0xab400101, 0x1c400611, 0x28d509ef02ad30, 0x224400051, 0xd75023e82ad70,
    0xf7007cc00019, 0x1f7308a882ad90, 0x15c0077c00019, 0x1b6007340001a, 0x224c00051,
    0x51001e400049, 0x1b7007340001a, 0x3e64, 0xa000ec00099, 0x8b2, 0x4008b2, 0x100004008b3,
    0x225400051, 0x4c008b2, 0x74008b2, 0xac008b2, 0x130008b2, 0x180008b2, 0x20c008b2, 0x214008b2,
    0x1c0008b2, 0x1e4008b2, 0x22c008b2, 0x1980077c00019, 0x1b00076c00019, 0x720086c00019,
    0x1b40076c00019, 0xafc00101, 0x191c00071, 0x3ff4, 0x130af942bf70, 0x1a30077c00019,
    0x1d5007540001a, 0x1a40077c00019, 0xeb0ac4c2bfd0, 0x192400071, 0x1000000b1, 0x233400051,
    0x94400131, 0x1c4007640001a, 0x1c5007640001a, 0x233c00051, 0x8cf7, 0x139400091, 0x234000051,
    0x614001d1, 0x1f3a041bc2c150, 0x1910041942c170, 0x1c9007640001a, 0x193400071, 0x1c00076c00019,
    0x1ca007640001a, 0x234c00051, 0x8d37, 0xd94000d1, 0xe970176c2c230, 0x235000051, 0x8d47,
    0x13000ec00099, 0x235400051, 0x1c40076c00019, 0x4044, 0xd98000d1, 0x9a0ae582c2f0, 0x194000071,
    0x13a400091, 0xb8a053642c330, 0x1c60076c00019, 0xceb0a9342c350, 0x194400071, 0x2200a8682c390,
    0xd9c000d1, 0x254004c1, 0x236400051, 0x67001e400049, 0xed10132c2c410, 0x4064, 0x1d4007640001a,
    0x1d5007640001a, 0x154007cc00019, 0x98108b342c4d0, 0x95400131, 0xb1400101, 0x252001482c510,
    0x19d8063442c530, 0x13b400091, 0xc30ae542c570, 0xa7708d542c590, 0x1bc0077c00019,
    0x11f4047102c5d0, 0x280b012e82c5f0, 0x69001e400049, 0x87400151, 0x8a502d5c2c630, 0x238400051,
    0x1d30076c0001a, 0x1d40076c00019, 0x1d40076c0001a, 0x238c00051, 0x8e37, 0x228c026d42c710,
    0x239000051, 0x8e47, 0xb7b0a5442c770, 0x239400051, 0x40b4, 0xdb0000d1, 0x2156015482c7d0,
    0x239800051, 0x57001f400049, 0x1d90076c0001a, 0x239c00051, 0x1030000b1, 0x624001d1,
    0x23a000051, 0x24dc009482c890, 0x197400071, 0x1c80077c00019, 0xd10aef42c8d0, 0x1034000b1,
    0xb2400101, 0x1c90077c0001a, 0x8f0b0142c930, 0x1c008d400019]
  ++ [0x1c400651, 0xdb0083c00019, 0x197c00071, 0x55b077742c9b0, 0x154007dc00019, 0x13d400091,
    0x198000071, 0x23b400051, 0xcc505f342ca50, 0x40f4, 0x198400071, 0x4d400251, 0x216017282cab0,
    0x8ef7, 0x1d00077c0001a, 0x13dc00091, 0x23c000051, 0x4104, 0x41c02dcc2cb30, 0x24008d400019,
    0x23c400051, 0x1d30077c0001a, 0x1044000b1, 0x1d40077c00019, 0xadc06c002cbd0, 0x29800451,
    0xb3000101, 0x13e400091, 0x199400071, 0x14008e400019, 0x18a80a2182cc50, 0x4124, 0xab0086c00019,
    0x67b07fd82cc90, 0x11a035242ccb0, 0x174007cc00019, 0x1d80077c0001a, 0x8d608fe82ccf0,
    0xb3400101, 0x199c00071, 0x25c004c1, 0x1da0077c0001a, 0x1db0077c00019, 0x8f87, 0x630001d1,
    0x23e400051, 0x19a400071, 0x71001e400049, 0x1dd0077c0001a, 0x1780ad802ce30, 0x1c008e400019,
    0x13f400091, 0x879075602ce70, 0x4154, 0x10b509cf82ce90, 0x17c007cc00019, 0x19ac00071,
    0x1970ac6c2cef0, 0x169007dc00019, 0x23f400051, 0x1058000b1, 0x13cf025682cf30, 0x34008d400019,
    0x1d8007840001a, 0x13fc00091, 0x634001d1, 0x23fc00051, 0x8ff7, 0x1da007840001a, 0x240000051,
    0x1eed038542d010, 0x24008e400019, 0x240400051, 0x20a05de42d070, 0xf70083c00019, 0x140400091,
    0x184007cc00019, 0x11f907e942d0d0, 0x19c000071, 0x22c00531, 0x1064000b1, 0x5a008bc00019,
    0x9047, 0x19c400071, 0x241400051, 0x174007dc00019, 0x1ce007940001a, 0x1390af9c2d1f0,
    0x850089c00019, 0x1cf007940001a, 0x254d01f5c2d230, 0x40008d400019, 0x19cc00071, 0x5f008bc00019,
    0x230133c2d290, 0x5d4001f1, 0x18c007cc00019, 0x242400051, 0x434002b1, 0x1d3007940001a,
    0x19d400071, 0xe3000e82d350, 0x242c00051, 0x90b7, 0x1d5007940001a, 0x243000051, 0x4e400251,
    0x141c00091, 0x63001f400049, 0x1b2f02e702d410, 0x63700bc42d430, 0x34008e400019,
    0x1d8007940001a, 0x1d9007940001a, 0x41e4, 0x194007cc00019, 0x1da007940001a, 0x2810018c82d4f0,
    0x244000051, 0x142400091, 0x4c008d400019, 0x5090a1342d550, 0x41f4, 0xdf4000d1, 0x198007cc00019,
    0x8a400151, 0x1080000b1, 0x13f0028842d610, 0x142c00091, 0x3240a9082d650, 0x245400051,
    0x20b5000802d6b0, 0x264004c1, 0x644001d1, 0xb5c00101, 0x1e3007940001a, 0x72008bc00019,
    0x143400091, 0x1c400671, 0x1e5007940001a, 0x1a0007cc00019, 0x246400051, 0xf01042042d7f0,
    0x1a0000071, 0x1dd0079c0001a, 0x166905c6c2d830, 0x2c9104bd02d850, 0x246c00051, 0x1a3007cc00019,
    0x1df0079c0001a, 0x20c00591, 0x1a4007cc00019, 0xe04000d1, 0x144000091, 0x247400051,
    0x1e20079c0001a, 0xd33081942d970, 0x144400091, 0x91f7, 0x1e40079c0001a, 0x248000051,
    0x2390ada42da10, 0x74007e802da30, 0x4c008e400019, 0x248400051, 0xe0c000d1, 0x10c901db02da90,
    0x198007dc00019, 0x9d909ad82dad0, 0x9237, 0x8b400151, 0x249000051, 0xc7b084ec2db50, 0x23400531,
    0xab0089c00019, 0x1d91040a42db90, 0x1b0007cc00019, 0x145400091, 0x1a2400071, 0x85008bc00019,
    0xe14000d1, 0x10a4000b1, 0x68008d400019, 0x1da007ac0001a, 0xe20b42c2dc70, 0x9287, 0x9a400131,
    0x1b4007cc00019, 0x24a400051, 0x42a4, 0xb7400101, 0x1dd007ac0001a, 0x34c0aa202dd30,
    0x1a3000071, 0x1de007ac0001a, 0x595010982dd70, 0x1a3007dc00019, 0xdac0a4a42dd90, 0x1a3400071,
    0x1a4007dc00019, 0x92c7, 0x6d001f400049, 0x24b400051, 0x1214063dc2de50, 0x28400491,
    0x9f0b5342deb0, 0x92f7, 0x1e4007ac0001a, 0x24c000051, 0x86608b582df10, 0x74008d400019,
    0x2e306f0c2df50, 0x16eb00d682df70, 0xf70086c00019, 0x1e7007ac0001a, 0x952, 0x400952,
    0x10000400953, 0x24cc00051, 0x4c00952, 0x7400952, 0xac00952, 0x14000952, 0x1e400952, 0x972,
    0x5400972, 0x9400972, 0x4000972, 0x1c000972, 0xdc00972, 0x24000972, 0x17c00972, 0x25400972,
    0x22c00972, 0x25c00972, 0x1ee007fc00019, 0x1ef007fc00019, 0x1b4000071, 0xd4008e400019,
    0x1f7007fc00019, 0x2cd5090282fc90, 0x284004c1, 0x1f8007fc0001a, 0x264000051, 0xbf0916c2fd10,
    0x1b5400071, 0xd8008e400019, 0x264400051, 0x3e900a3c2fd70, 0x154400091, 0x11a5078dc2fdb0,
    0x1340089c00019, 0xbad0b7e82fdd0, 0xa1400131, 0xdb008e400019, 0x1fd007fc0001a]
  ++ [0xf0008d400019, 0x324003d1, 0x1ff007fc00019, 0x49b0385c2fe90, 0x1b00083c00019,
    0x1ec0080c0001a, 0x1dd606ab42fef0, 0x700020c00049, 0x1ed0080c0001a, 0x265c00051, 0x630001f1,
    0xc3a0b9942ff50, 0x266000051, 0x37a0b2002ff90, 0x1b40083c00019, 0x266400051, 0x16e9001e02fff0,
    0xf7008d400019, 0x1f10080c0001a, 0xf8008d400019, 0x1f20080c0001a, 0x99b7, 0x1f30080c0001a,
    0x2c3f0bfb0300b0, 0x267000051, 0x34a0b310300d0, 0xc0400101, 0x267400051, 0x1d950564c30130,
    0xfc008d400019, 0x1f60080c0001a, 0x45f4, 0x850093400019, 0x16d60138830190, 0x1bc0083c00019,
    0x1c4006d1, 0x268000051, 0x156400091, 0x100008d400019, 0x268400051, 0x1b8400071,
    0x1fb0080c0001a, 0x1184000b1, 0x1c00083c00019, 0x1fc0080c0001a, 0xc7507704302f0, 0xc0c00101,
    0xed4000d1, 0x1c20083c00019, 0x61a08af830350, 0x41608b6030370, 0x269400051, 0x1c40083c00019,
    0x3a400351, 0x750020c00049, 0x2d410c07c30410, 0x269c00051, 0x1c60083c00019, 0x157400091,
    0x5f0095c00019, 0x2030080c0001a, 0x1c80083c00019, 0x270f016c4304d0, 0x25400531, 0xc1400101,
    0xa2c00131, 0x22c00591, 0x10c008d400019, 0x1fc008140001a, 0x26ac00051, 0x9ab7, 0x1fd008140001a,
    0x26b000051, 0x9ac7, 0x1ba400071, 0x158000091, 0x26b400051, 0x4664, 0x28c004c1, 0xee4000d1,
    0x119a07b3830670, 0x158400091, 0x98c0a6e8306b0, 0x9af7, 0x1bac00071, 0x26c000051,
    0x1d0304dbc30710, 0x9d2, 0x4009d2, 0x100004009d3, 0xa3400131, 0x4c009d2, 0x74009d2, 0xac009d2,
    0x140009d2, 0x1e4009d2, 0x23c009d2, 0x240009d2, 0x25c009d2, 0x1c0009d2, 0x26c009d2,
    0x1da0086c00019, 0x1a00089c00019, 0x14c008e400019, 0x1c6000071, 0x1e40086c00019, 0x161400091,
    0x1c6400071, 0x820021400049, 0x11079b831b10, 0x164008d400019, 0x27c400051, 0x1214000b1,
    0x205008540001a, 0x6dc001d1, 0x184008bc00019, 0x206008540001a, 0xd10094c00019, 0x207008540001a,
    0x4864, 0x154008e400019, 0x9f47, 0x169008d400019, 0x27d400051, 0x1c7400071, 0x1b00089c00019,
    0x243b0a9a031cd0, 0x129807ce031cf0, 0xc7400101, 0x162400091, 0x1558071f031d30, 0x1ee0086c00019,
    0x1650024f831d50, 0x1ef0086c00019, 0x4884, 0x18602f6431db0, 0x1b40089c00019, 0x27e400051,
    0x1c8000071, 0x1c400711, 0x1224000b1, 0x4894, 0x3c400351, 0x27ec00051, 0x9fb7, 0x211008540001a,
    0x27f000051, 0x3f20b7f031ed0, 0x1c8800071, 0x680022c00049, 0x208e092c031f10, 0x8070110831f30,
    0x174008d400019, 0x1c8c00071, 0xedf08c6431f70, 0x1f70086c00019, 0x215008540001a,
    0x1f80086c00019, 0x17280597031fd0, 0x5e90a23031ff0, 0x280000051, 0x20d0085c0001a, 0x1c9400071,
    0x164008e400019, 0x280400051, 0x163c00091, 0x20f0085c0001a, 0x1c00089c00019, 0x2100085c0001a,
    0x280c00051, 0x164000091, 0x11340271c32110, 0x1c20089c00019, 0x1df50508432150,
    0x1002015bc32170, 0x1ff0086c00019, 0x281400051, 0x1c40089c00019, 0x129c0ae60321d0, 0x1ca400071,
    0x570023c00049, 0x4e400291, 0x1c60089c00019, 0x2160085c0001a, 0x48f4, 0x5f009bc00019,
    0x7306ec032290, 0xf70000d1, 0x14360493c322d0, 0x1240000b1, 0x4904, 0xe330258432330,
    0x184008d400019, 0x72d069f032350, 0x2070086c00019, 0xf74000d1, 0x1cb400071, 0x2080086c00019,
    0x165400091, 0xa9400131, 0x6d0022c00049, 0x283400051, 0x174008e400019, 0x20a0086c0001a,
    0x6af0ae6432470, 0x99400151, 0x283c00051, 0xa0f7, 0xa32, 0x400a32, 0x10000400a33,
    0x12b307e7c32510, 0x4c00a32, 0x7400a32, 0xac00a32, 0x14000a32, 0x1e400a32, 0x24000a32,
    0x25c00a32, 0x1c000a32, 0x28c00a32, 0x2140089c00019, 0x1ee008bc00019, 0x28400a32, 0x293000051,
    0x1c4008e400019, 0x1f7008bc00019, 0xa4f7, 0x294000051, 0x1c8008e400019, 0x2f700166033950,
    0x9d400151, 0xe9e093f8339b0, 0x1340095c00019, 0x1983090fc339d0, 0xce800101, 0x2250089c0001a,
    0xb00751833a30, 0x16f400091, 0x1d8400071, 0x720001d1, 0x295400051, 0x14c0094c00019,
    0x21e008a40001a, 0x9e30a73433af0, 0x1c00a4000019, 0x21f008a40001a, 0x2d6802c4033b30,
    0x1e4008d400019, 0x324a0aa9433b50, 0x16fc00091, 0xc9409c9833b90, 0xae400131, 0xd8009ac00019,
    0x296400051, 0x850022c00049]

def opsA8192_1 : List Nat :=
  [0x17b90322033c10, 0x1d9400071, 0x1d4008e400019, 0x724001d1, 0x25b10438833c70, 0x207008bc00019,
    0x170400091, 0x208008bc00019, 0x25400591, 0xcf400101, 0x26ce07b8c33d10, 0x16270031c33d30,
    0x1740093400019, 0x228008a40001a, 0x1da000071, 0x23ff02f7833d90, 0xa5f7, 0x216008b40001a,
    0x1547036a433df0, 0x298000051, 0x217008b40001a, 0x2c0010400099, 0x298400051, 0x4d4002b1,
    0x20f008bc00019, 0x4b84, 0xd1009b7033eb0, 0x210008bc00019, 0x1dac00071, 0x2b4c037a833ef0,
    0xa637, 0xada0257c33f10, 0x12e4000b1, 0x299000051, 0xa647, 0x3ec00351, 0x213008bc00019,
    0x299400051, 0xf350b0d033fb0, 0x214008bc00019, 0xace0803433fd0, 0x4ba4, 0x1000000d1,
    0x21f008b40001a, 0x1f8008d400019, 0x30400451, 0x1e5e08d6c34070, 0x5a000251, 0x12ec000b1,
    0x218008bc00019, 0x29a400051, 0x26509f20340f0, 0xd0400101, 0x172400091, 0x3910c20c34130,
    0x1840093400019, 0x31c00431, 0x29ac00051, 0x21b008bc00019, 0x225008b40001a, 0x1540095c00019,
    0xa6c7, 0x12f4000b1, 0x22c00601, 0x29b400051, 0x172c00091, 0x228008b40001a, 0x229008b40001a,
    0x1fad051fc342b0, 0x220008bc00019, 0x55b03754342d0, 0x1ef008e400019, 0x1b0a08d0834310,
    0x1dd400071, 0x18c0093400019, 0x29c400051, 0x4bf4, 0xf7009ac00019, 0x734001d1, 0x15c0095c00019,
    0x1b1903db4343d0, 0x1300000b1, 0x1ddc00071, 0x29d000051, 0x32e0c46034450, 0x227008bc00019,
    0x29d400051, 0x1304000b1, 0x228008bc00019, 0x228008bc0001a, 0x1de400071, 0x174000091,
    0x229008bc0001a, 0x29dc00051, 0x20c008d400019, 0x22a008bc0001a, 0x18bb02da434570, 0x174400091,
    0x57a06afc345b0, 0x22c008bc00019, 0x29e400051, 0x20f008d400019, 0x22d008bc0001a,
    0xe050997c34630, 0x1df000071, 0x22e008bc0001a, 0x2ac05dc834670, 0xa7b7, 0x22f008bc0001a,
    0x1df400071, 0x29f000051, 0xb0d18c346d0, 0x6c4001f1, 0x213008d400019, 0x29f400051, 0x73c001d1,
    0x214008d400019, 0x30ff05dc834750, 0x1314000b1, 0x4c54, 0x1a1005d0834790, 0xa7f7, 0x175400091,
    0x25c00591, 0x2a0000051, 0xa120a9c034810, 0x1318000b1, 0x218008d400019, 0x2a34023e434850,
    0x175800091, 0x1e0400071, 0xf7009bc00019, 0x223008cc0001a, 0x3200c5b0348b0, 0x1840094c00019,
    0x224008cc0001a, 0x102c000d1, 0xd2400101, 0x225008cc0001a, 0x4e4002b1, 0x208008e400019,
    0xa0400151, 0x130011c00099, 0x2a1400051, 0x32400431, 0x1030000d1, 0x228008cc0001a,
    0x10ef09ea4349f0, 0x8500a1c00019, 0x176400091, 0x2a1c00051, 0x220008d400019, 0x3c80246834a50,
    0x5a00a4000019, 0x1034000d1, 0x1e1800071, 0xff201ab834ab0, 0x18c0094c00019, 0x2a2400051,
    0x20f008e400019, 0x52400291, 0x210008e400019, 0x30c70867434b50, 0x18f0094c00019,
    0x22f008cc0001a, 0x1900094c00019, 0xa8c7, 0x1e2400071, 0x227008d400019, 0x337606a3434c10,
    0x2d3d05f3434c30, 0x228008d400019, 0x177400091, 0x25e607bb434c90, 0x1940094c00019,
    0x7fd03a9434cd0, 0x1334000b1, 0x2a4000051, 0x22b008d40001a, 0x22c008d400019, 0x2a4400051,
    0x28c00531, 0x190d0277034db0, 0x1980094c00019, 0x1044000d1, 0x2a4c00051, 0x23400601,
    0x7430ccf434e10, 0x5a00a4c00019, 0x26e50716c34e50, 0x4cf4, 0x2a5400051, 0xb2400131,
    0x19c0094c00019, 0x232008d40001a, 0x1e4000071, 0x4d04, 0xd8809db034f30, 0x234008d400019,
    0x234008d40001a, 0x1e4400071, 0x235008d400019, 0x2d8a01dc034f90, 0x1344000b1, 0x1a00094c00019,
    0x2a6400051, 0x1a7104a5834ff0, 0xd4000101, 0x223008e40001a, 0x21a604d7835030, 0x1c00093400019,
    0x29c2001d035050, 0x4d24, 0x1c10093400019, 0x225008e40001a, 0x33c008e0c350b0, 0x2a7000051,
    0x179400091, 0xd4400101, 0x8790446435110, 0x1e5400071, 0x228008e400019, 0x228008e40001a,
    0x35902ad435170, 0x229008e40001a, 0x11704130351b0, 0xa9f7, 0x56408f3c351d0, 0x1058000d1,
    0x179c00091, 0x2a8000051, 0x1e5c00071, 0x4006ca035230, 0xb3000131, 0x2a8400051,
    0xd8b05bf035270, 0xf7009dc00019, 0x2cb801e1c35290, 0x1980095c00019, 0x22e008e40001a,
    0x2a8c00051, 0x22f008e400019, 0x26400591, 0x40400351, 0xb3400131, 0xab00a1c00019, 0x2a9400051,
    0x1b00094c00019, 0xa2400151, 0x610025c00049, 0x233008e40001a, 0x234008e400019, 0x1064000d1,
    0x235008e400019, 0x4d84, 0x1e7400071]
  ++ [0x1b40094c00019, 0x2aa400051, 0xd5400101, 0x237008e40001a, 0x1364000b1, 0x1d40093400019,
    0x17b400091, 0xe1909cfc35570, 0x239008e400019, 0x17fc01fac35590, 0x1a40095c00019, 0xaac7,
    0x31670133c355f0, 0x8b0023c00049, 0x2ab400051, 0xf000032835650, 0x1e8400071, 0x136c000b1,
    0x2abc00051, 0xaaf7, 0x23400611, 0x2ac000051, 0xcb50a2f435710, 0x2ac400051, 0xf6c029cc35770,
    0x17c400091, 0x580d490357b0, 0x1c00094c00019, 0x238008ec0001a, 0x2acc00051, 0x1df0093400019,
    0x239008ec0001a, 0x1ca909b6035830, 0x2ad000051, 0xab47, 0x7440744835870, 0x23e50469435890,
    0x4de4, 0x1c40094c00019, 0x228008fc0001a, 0x5720c078358f0, 0xd6400101, 0xa3400151,
    0x325e03e4c35930, 0x1e40093400019, 0x137c000b1, 0x4df4, 0xd960a01035990, 0x14350b4d0359b0,
    0x1c80094c00019, 0x2ae400051, 0x1ea400071, 0x1380000b1, 0x4e04, 0x31c00451, 0x22e008fc0001a,
    0x59f0199435a70, 0x22f008fc0001a, 0x138f0c1b035ab0, 0x154009ac00019, 0x10310429035ad0,
    0x860024400049, 0x13e604c9835b10, 0x232008fc0001a, 0x2340ce1035b70, 0x233008fc0001a,
    0x2afc00051, 0x2d4004c1, 0x234008fc0001a, 0x159e00b2435bf0, 0x1ef0093400019, 0x17e400091,
    0x7400a6400019, 0x2b0400051, 0x185702b2835c90, 0x1d40094c00019, 0x4e44, 0x2b0c00051,
    0xd7400101, 0x239008fc0001a, 0x29800531, 0x17ec00091, 0x2b1000051, 0xe0709f3c35d50,
    0x1ec400071, 0x2b1400051, 0x1c40095c00019, 0x23c008fc0001a, 0x1f70093400019, 0x2e5b0606c35e10,
    0x2b1c00051, 0xac77, 0x17f400091, 0x2b2000051, 0x5d400251, 0x504002b1, 0x770001d1,
    0x24670461c35ed0, 0x3db0d5e435ef0, 0xac00a4000019, 0x237009040001a, 0x1ed400071,
    0x1c00ab400019, 0xb5c00131, 0x2b2c00051, 0x1df0094c00019, 0x54400291, 0x2f380373035fb0,
    0x154009bc00019, 0xacc7, 0x180000091, 0x2b3400051, 0x13a4000b1, 0x23c009040001a,
    0xb070ac0436070, 0x1ee000071, 0x180400091, 0x234007c90360b0, 0x1e40094c00019, 0x23e009040001a,
    0x1ee400071, 0xd8400101, 0x4910c60436110, 0x2400ab400019, 0x2b4400051, 0x38c003d1,
    0x241009040001a, 0x180c00091, 0x1d40095c00019, 0x22e009140001a, 0xad37, 0x22f009140001a,
    0x2b5000051, 0x4ec4, 0xab00a4c00019, 0x2b5400051, 0x1ef400071, 0x174009ac00019, 0x181400091,
    0x2f040c5fc362f0, 0x700025c00049, 0x213506ac836310, 0x2b5c00051, 0x20c0093400019,
    0x234009140001a, 0x35902cf836370, 0x2b6000051, 0xa5400151, 0x164009bc00019, 0x2b6400051,
    0x20f0093400019, 0x237009140001a, 0x2100093400019, 0x238009140001a, 0x31be0a0bc36470, 0xadb7,
    0x239009140001a, 0x2b7000051, 0x2fb0cd4c364d0, 0xf4000a40364f0, 0xd9400101, 0x2b7400051,
    0x2140093400019, 0x348f0b02836550, 0x1f70094c00019, 0x23d009140001a, 0x13c4000b1, 0xadf7,
    0x23e009140001a, 0x704001f1, 0x2b8000051, 0x263f0408c36610, 0x1f1400071, 0x2180093400019,
    0x2b8400051, 0x25a4006a436670, 0xf700a1c00019, 0x241009140001a, 0x115f09434366b0,
    0x184009ac00019, 0x242009140001a, 0x10c0000d1, 0x318d0b89436710, 0xa000a6400019, 0x183400091,
    0x2c0c06b5836770, 0x1ff0094c00019, 0x2b9400051, 0x174009bc00019, 0x10c4000d1, 0x1afe004e0367f0,
    0x8500a7c00019, 0x23d0091c0001a, 0x180f079d436830, 0x2200093400019, 0x23e0091c0001a,
    0x183c00091, 0x1ef0095c00019, 0xae87, 0x82a0d1b4368b0, 0x18c009ac00019, 0x2ba400051,
    0x184000091, 0x1d8f013fc36910, 0x4f64, 0x1f3000071, 0x27400591, 0x2bac00051, 0xaeb7,
    0x184400091, 0x1f3400071, 0x2bb000051, 0x167002c28369d0, 0x2270093400019, 0x1d5f09d9c36a10,
    0x2280093400019, 0x2460091c0001a, 0x1f70095c00019, 0x1888031d436a90, 0x2bbc00051, 0xaef7,
    0x2340092c0001a, 0x1218041cc36af0, 0x2bc000051, 0x2350092c0001a, 0x1db30994c36b30,
    0x22c0093400019, 0x2d540258836b50, 0x1f4400071, 0x20f0094c00019, 0x2370092c0001a,
    0x742011d436bb0, 0x2100094c00019, 0x185400091, 0xbf80512036bf0, 0xdb000101, 0x2390092c0001a,
    0x2bd000051, 0xaf47, 0x180007b8c36c70, 0x2130094c00019, 0x2bd400051, 0x10dc000d1,
    0x2140094c00019, 0x253a089d436cd0, 0x2bd800051, 0xdb400101, 0x23d0092c0001a, 0x1d0bb8836d30,
    0x2340093400019, 0x4fc4, 0x181703d7836d70, 0x2350093400019, 0x14920a6a836d90, 0x714001f1,
    0x2180094c00019]
  ++ [0x2be400051, 0x13f4000b1, 0x850025400049, 0x1f5c00071, 0xccb0a86436e30, 0x10e4000d1,
    0x2390093400019, 0x2430092c0001a, 0x4fe4, 0x2bf000051, 0xafc7, 0x3dc050ac36ef0,
    0x169009dc00019, 0x2bf400051, 0x186c00091, 0x23c0093400019, 0x335b0341036f50, 0x4ff4,
    0x15e0cc0436f70, 0x2470092c0001a, 0xaff7, 0xfeb0db2436fd0, 0xb9400131, 0x2c0000051,
    0xc900a9c837010, 0x7902b5c37030, 0x1f7000071, 0x2c0400051, 0x20f0095c00019, 0x33bf0b6a037090,
    0x1f7400071, 0x2100095c00019, 0x242009340001a, 0xdc400101, 0x5f400251, 0x2440093400019, 0xb047,
    0x187c00091, 0x2270094c00019, 0x2e0d0cc7c37190, 0x28bc08bf8371b0, 0x2280094c00019,
    0x246009340001a, 0x1f8000071, 0x247009340001a, 0x2480093400019, 0x248009340001a,
    0xff2082a837270, 0x2490093400019, 0x188400091, 0x79c001d1, 0x22c0094c00019, 0x2c2400051,
    0xfc00a4000019, 0x31c00471, 0x3466094d437330, 0x24c0093400019, 0xa8400151, 0x2c2c00051,
    0x720001f1, 0x11660ab1837390, 0x188c00091, 0x1a4009bc00019, 0xb0c7, 0xa07050cc373f0,
    0x10000a4000019, 0x2c3400051, 0x1f9400071, 0xd400a6400019, 0x4c80c34037450, 0x242009400001a,
    0x2c3c00051, 0x2340094c00019, 0x189400091, 0xdd400101, 0x1f9c00071, 0xd800a6400019,
    0x2dd10c56037550, 0x189800091, 0x2c3c00c3037570, 0xf700a4c00019, 0x5084, 0x5fc00251,
    0x1c0009ac00019, 0x13e90a68c375d0, 0x2c4c00051, 0x2390094c00019, 0x248009400001a, 0x1424000b1,
    0x2c5000051, 0xb147, 0xd18042f837670, 0x2270095c00019, 0x2c5400051, 0x23c0094c00019,
    0x24b009400001a, 0x50a4, 0x10c00a4000019, 0x18a400091, 0x2c5c00051, 0x1c6009ac00019,
    0x24d009400001a, 0x1510089a837790, 0x304b0ceac377b0, 0x2400094c00019, 0x2c6400051,
    0x8f0025400049, 0x1114000d1, 0x18ac00091, 0x3a4003d1, 0xb1b7, 0xa9400151, 0x2c7000051,
    0x1e3606560378d0, 0x1434000b1, 0xde400101, 0x2c7400051, 0x3400af400019, 0x18b400091,
    0x1fc400071, 0x8500ab400019, 0x21a60de4837990, 0x50e4, 0x2480094c00019, 0x2480094c0001a,
    0x7ac001d1, 0x2490094c00019, 0x23400651, 0x7400ac400019, 0x98c02a9c37a50, 0x50f4,
    0x24b0094c0001a, 0x10b309be437ab0, 0x24c0094c00019, 0x24c0094c0001a, 0x16b1083fc37af0,
    0x18c000091, 0x43400351, 0x1fd400071, 0x23a0095c00019, 0x1124000d1, 0xab00a9c00019,
    0x2c9400051, 0x1444000b1, 0x23c0095c00019, 0x17d605cbc37bd0, 0x32400471, 0x12000a4000019,
    0x2510094c0001a, 0x2c9c00051, 0xb277, 0x2520094c0001a, 0x376e0d23037c70, 0x2ca000051,
    0xfa30a09c37c90, 0x2400095c00019, 0xb300ad1437cd0, 0x33070389c37cf0, 0xdf400101,
    0x2410095c0001a, 0x262e0d6a837d30, 0xf800a6400019, 0x325c0c29037d50, 0x2430095c00019,
    0x2430095c0001a, 0xb52, 0x400b52, 0x10000400b53, 0x4c00b52, 0x5400b52, 0xac00b52, 0x14000b52,
    0x1e400b52, 0x24000b52, 0x29800b52, 0x2bc00b52, 0x2d400b52, 0x2c000b52, 0x21400b52,
    0x190a09e9439370, 0x63000251, 0x2fa20ab3c393d0, 0x2610098c0001a, 0x23a009ac00019,
    0x2e6a0bc0439470, 0x227009bc00019, 0x2dd400051, 0x304004c1, 0x25a009940001a, 0x20c000071,
    0x32400491, 0x15800a6400019, 0x13602edc39550, 0x20c400071, 0x45400351, 0x1f1203388395b0,
    0x240009ac00019, 0x2de400051, 0xc1400131, 0x198000091, 0x26e301e7839610, 0x15c00a6400019,
    0x260009940001a, 0x243009ac00019, 0x198400091, 0x244009ac00019, 0x1eb08750396d0,
    0x18c00a4000019, 0x2df400051, 0xd7504d8039730, 0xfc00ab400019, 0x264009940001a, 0x8500b1400019,
    0x265009940001a, 0xb7f7, 0x252009a40001a, 0x53a4, 0x2e0000051, 0xaf400151, 0x16400a6400019,
    0x2e0400051, 0x20f009dc00019, 0x180617039890, 0x84b01dcc398b0, 0x24c009ac00019, 0x199400091,
    0x211002038398f0, 0xe6400101, 0x294d0a26c39910, 0x23a009bc00019, 0x4e00d2d839950,
    0x213009dc00019, 0x2e1400051, 0x23c009bc00019, 0x296008644399d0, 0x199c00091, 0x19800a4000019,
    0x25b009a40001a, 0x2e1c00051, 0x20f000071, 0x25c009a40001a, 0x5a000291, 0x7f4001d1,
    0x20f400071, 0x254009ac00019, 0xc70021a039ad0, 0x11c0000d1, 0x19a400091, 0xb210ba4c39b30,
    0x10c00ab400019, 0x260009a40001a, 0x29800591, 0x257009ac00019, 0x1a0209fdc39b90,
    0x22e30688039bb0, 0x258009ac00019]
  ++ [0x11c4000d1, 0x210000071, 0x2e3400051, 0x19ac00091, 0x17400a6400019, 0x264009a40001a,
    0x85f006d839c70, 0x265009a40001a, 0x2e3c00051, 0xb8f7, 0x134b0d9e439cd0, 0x2e4000051,
    0x164700a3439d10, 0x20c00711, 0x11400ab400019, 0x2e4400051, 0x37400431, 0x269009a40001a,
    0x260009ac00019, 0x260009ac0001a, 0xb937, 0x261009ac0001a, 0x211400071, 0x2e5000051,
    0xee00ac1839e50, 0x227009dc00019, 0x2e5400051, 0x25c306f7839eb0, 0x264009ac00019, 0x5444,
    0xc10e4bc39ef0, 0x19c000091, 0x285d0b5bc39f10, 0x2e5c00051, 0x266009ac00019, 0x24240af0039f50,
    0x1c1103a9839f70, 0x267009ac00019, 0x19c400091, 0x268009ac00019, 0x2e6400051, 0x212400071,
    0x1b000a4000019, 0x269009ac0001a, 0xbcd0b8dc3a030, 0x18400a6400019, 0x26a009ac0001a,
    0xe870ae043a070, 0x26b009ac00019, 0x26b009ac0001a, 0x19cc00091, 0x258009bc00019,
    0x1111007b83a0d0, 0xe8400101, 0x2e7400051, 0x213000071, 0x153d0bb843a150, 0x5484, 0x2e7c00051,
    0xb9f7, 0x19d400091, 0x2e8000051, 0xba07, 0x1524000b1, 0x18c00a6400019, 0x1bc502d083a250,
    0x2246075403a270, 0xf700adc00019, 0xb1400151, 0x5a20d2283a2b0, 0x260009bc00019, 0x46400351,
    0x2e8c00051, 0x214000071, 0x261009bc0001a, 0x23a009dc00019, 0xba47, 0x214400071,
    0x3b0011c00099, 0x2c91036a43a390, 0x264009bc00019, 0x264009bc0001a, 0x27c10cc7c3a3f0,
    0x1c000a4000019, 0x19e400091, 0x16340b82c3a430, 0x266009bc00019, 0x550c6783a450,
    0x267009bc00019, 0xba87, 0xf510a7043a4b0, 0x268009bc00019, 0x2ea400051, 0xe9400101,
    0x1437041a83a510, 0x215400071, 0x19800a6400019, 0x26a009bc0001a, 0x2eac00051, 0x26b009bc00019,
    0x11f4000d1, 0x54e4, 0x26c009bc00019, 0x1983069243a5d0, 0x1c800a4000019, 0x29f30cbf03a610,
    0x19c00a6400019, 0x19f400091, 0x54f4, 0xe8d0af6c3a670, 0x26f009bc00019, 0xfe505c703a690,
    0x248009dc00019, 0x266009c40001a, 0xb680a3cc3a6f0, 0x1540000b1, 0x5504, 0x28d20348c3a730,
    0x1a000a6400019, 0x280e0d6903a750, 0x269009c40001a, 0xb230bd643a7b0, 0x24c009dc00019,
    0x216c00071, 0x1a0000091, 0x26b009c40001a, 0x2ed000051, 0x210f065dc3a850, 0xdfa029803a870,
    0x1ff00a1c00019, 0x2ed400051, 0x2b200a20c3a8b0, 0x1c400a4c00019, 0x321003de43a8d0, 0xc5400131,
    0xea400101, 0x26f009c40001a, 0x252009dc00019, 0x270009c40001a, 0x253009dc00019,
    0x12220ace03a990, 0x254009dc00019, 0xd0609b443a9d0, 0x2e95001e83a9f0, 0x218000071,
    0x25f009d40001a, 0x13400ac400019, 0x5e09d043aa50, 0x2eec00051, 0x257009dc00019,
    0x261009d40001a, 0x258009dc00019, 0x1a1400091, 0x2d400531, 0x16900a9c00019, 0x2ef400051,
    0x1b000a6400019, 0x218c00071, 0x17e508b4c3ab70, 0x265009d40001a, 0x310049b43abb0, 0xb3000151,
    0x266009d40001a, 0x2f0000051, 0x1214000d1, 0x11420e5f83ac30, 0x1b400a6400019, 0x2f0400051,
    0x17140771c3ac70, 0x20f00a1c00019, 0x25400651, 0x260009dc00019, 0x26a009d40001a,
    0xf7c0ad503acf0, 0xeb400101, 0x1a2400091, 0x1ca00c9983ad30, 0x15400ab400019, 0x181508b043ad50,
    0x21300a1c00019, 0x2f1400051, 0x121f006a43adb0, 0x264009dc00019, 0x26e009d40001a, 0x21a400071,
    0x27400601, 0x29606c043ae10, 0x2f1c00051, 0x266009dc00019, 0x270009d40001a, 0x267009dc00019,
    0xbc87, 0x1a3000091, 0x15fd00d143aed0, 0x8a0028400049, 0xbf2, 0x400bf2, 0x10000400bf3,
    0x1a3400091, 0x4c00bf2, 0x5400bf2, 0xac00bf2, 0x13000bf2, 0xa400c12, 0x4000c12, 0xdc00c12,
    0x2e400bf2, 0x14000c12, 0x17c00c12, 0x14400c12, 0x2c000c12, 0x22c00c12, 0x30400c12, 0x29800c12,
    0x2fc00c12, 0x24000c12, 0x26b00a4000019, 0x26c00a4000019, 0x28400611, 0x30d000051,
    0x22700a7c00019, 0x26400a4c00019, 0xf4400101, 0x26600a4c00019, 0x9f503d903d150,
    0x27600a4000019, 0xbb30c59c3d190, 0x58e4, 0x27700a4000019, 0x30e400051, 0x28c00601,
    0x11f055203d210, 0x234006f1, 0x22f000071, 0x10e504ee03d250, 0x58f4, 0x10fd0a0e43d270,
    0x26b00a4c00019, 0x28900a340001a, 0x22f400071, 0x26c00a4c00019, 0x60108a143d2d0, 0x38c00451,
    0x1640000b1, 0x1c470ecfc3d310, 0x2fcf08e5c3d330, 0x19c00af400019, 0x1b3400091, 0x7570d7843d370,
    0x26f00a4c00019, 0x28d00a340001a, 0x30fc00051, 0x27f00a4000019, 0x404003d1, 0x7380c6b83d3f0,
    0x310000051]
  ++ [0x28500a3c0001a, 0x25400a6400019, 0x310400051, 0x230400071, 0x20f00a9c00019, 0x874001d1,
    0x37400471, 0x27400a4c00019, 0x28800a3c0001a, 0xce800131, 0x392a0dc443d4f0, 0x1b4000091,
    0x28900a3c0001a, 0x311000051, 0xc447, 0x5fc00291, 0x27700a4c00019, 0x311400051, 0x22c00711,
    0x28700a4000019, 0x5944, 0x28800a4000019, 0x28d00a3c0001a, 0x311c00051, 0x25c00a6400019,
    0x12e4000d1, 0x3b38091e83d670, 0xc72, 0x400c72, 0x10000400c73, 0x312400051, 0x4c00c72,
    0x5400c72, 0x4000c72, 0x2e400c72, 0x29800c72, 0x2c000c72, 0x23c00c72, 0x31c00c72, 0x1c000c72,
    0x2f400c72, 0x25400ab400019, 0x27400a9c00019, 0x236a0994c3edd0, 0x27600a9c00019, 0x29800611,
    0x29f00a7c00019, 0x23f400071, 0x27800a9c00019, 0xfbc00101, 0x16e4000b1, 0x25c00ab400019,
    0x38c00471, 0x24900ac400019, 0x23fc00071, 0x22c00adc00019, 0x326400051, 0x5ba4, 0x240000071,
    0x29b00a840001a, 0xd4400131, 0x26000ab400019, 0x1364000d1, 0x22a03f643f070, 0x27f00a9c00019,
    0x1c0400091, 0x28000a9c00019, 0x6e603e8c3f0d0, 0xfc400101, 0x2ac089103f110, 0x11ec0a1ac3f130,
    0x26400ab400019, 0xc0400151, 0x28b9071e83f170, 0x8500c3400019, 0x8b4001d1, 0x28400a9c00019,
    0x28e00a940001a, 0x16f4000b1, 0x26700ab400019, 0x28f00a940001a, 0x241400071, 0x1c1000091,
    0x328400051, 0x28700a9c00019, 0x29100a940001a, 0x176e0f5803f2b0, 0x28800a9c00019, 0x1c1400091,
    0x26b00ab400019, 0x254d0f8043f310, 0x26c00ab400019, 0x230b3f03f350, 0x2b2051643f370,
    0x21300afc00019, 0x329400051, 0x28c00a9c00019, 0x29600a940001a, 0x242400071, 0x26f00ab400019,
    0x5c04, 0xca77, 0x29800a940001a, 0x32a000051, 0x29900a940001a, 0x1704000b1, 0x29000a9c00019,
    0x2c230e7d43f4d0, 0x365701e183f4f0, 0xfd400101, 0x1c2400091, 0x137c000d1, 0x243000071,
    0x2d910f4343f550, 0x29300a9c00019, 0x29d00a940001a, 0x800a3c3f5b0, 0x29400a9c00019, 0xcac7,
    0x1380000d1, 0x32b400051, 0x27800ab400019, 0x2a000a940001a, 0x1ace092683f670, 0x8500c4400019,
    0xc1400151, 0x63000291, 0xb0e8b83f6d0, 0x32c000051, 0x254006d1, 0x3dde0c9983f730,
    0x26800ac400019, 0x32c400051, 0x509010243f770, 0x6fd075703f790, 0x24c00adc00019,
    0x29c00a9c0001a, 0x1d82087f83f7f0, 0x29d00a9c00019, 0x29d00a9c0001a, 0x10240309c3f830,
    0x28000ab400019, 0x28400651, 0x1c3c00091, 0x29f00a9c00019, 0x27690b4d03f890, 0x2a000a9c00019,
    0x8c4001d1, 0x4cc00351, 0x1c4000091, 0x2a100a9c0001a, 0x32dc00051, 0x28400ab400019,
    0x33802ae03f950, 0x19830a4603f970, 0x25300adc00019, 0x1c4400091, 0xd6400131, 0x2a400a9c00019,
    0x32e400051, 0x28700ab400019, 0x1394000d1, 0xbf40cec03fa30, 0x28800ab400019, 0x2a600a9c0001a,
    0x291c0f1483fa70, 0x2a700a9c00019, 0x1c710bcb03fa90, 0x1c4c00091, 0x27600ac400019,
    0x4320edf03fad0, 0x246400071, 0x27700ac400019, 0x32f400051, 0x28c00ab400019, 0x29600aac0001a,
    0x3001044e83fb90, 0x2467059b83fbb0, 0xcbf7, 0x246c00071, 0x330000051, 0x29900aac0001a,
    0x29000ab400019, 0x330400051, 0x29b00aac0001a, 0x247400071, 0x26000adc00019, 0xa5c018343fcd0,
    0x330c00051, 0xff400101, 0x29d00aac0001a, 0x20d306f243fd30, 0x331000051, 0x13a4000d1,
    0x1c6000091, 0x331400051, 0x26400adc00019, 0x2a000aac0001a, 0x248000071, 0x1c6400091,
    0x37720f2603fe30, 0x29800ab400019, 0x2a200aac0001a, 0x5cf4, 0x248400071, 0x29900ab400019,
    0xba60d1103fe90, 0x26800adc00019, 0x332400051, 0x1740000b1, 0x17520fa783ff10, 0x28800ac400019,
    0x2a600aac0001a, 0x332c00051, 0xccb7, 0x4d400351, 0x164f0b2903ffb0, 0x333000051,
    0x5a50e9643ffd0, 0x5f4002b1]

def opsA8192 : List Nat :=
  opsA8192_0 ++ opsA8192_1

def stageA2 : List (Nat × List Nat) :=
  [(8192, opsA8192)]

def opsA16384_0 : List Nat :=
  [0x100000101, 0x333400051, 0x2fdb01c1040030, 0x2a000ab400019, 0x1c7400091, 0x5d24,
    0x26f00adc00019, 0x13b4000d1, 0x27000adc00019, 0x2a200ab40001a, 0x844001f1, 0x334000051,
    0x174c000b1, 0x2a400ab400019, 0x334400051, 0x434003d1, 0x62a0d558401b0, 0x27400adc00019,
    0x5d44, 0x37590db40401f0, 0x1c8000091, 0xc1f008b840210, 0x2a800ab400019, 0x1e2d087e440250,
    0x1754000b1, 0x5d54, 0x335400051, 0x27800adc00019, 0x59507e9c402d0, 0x15c00bc000019,
    0x2ab00ab40001a, 0x1c8800091, 0xd8400131, 0x2ac00ab400019, 0x2ac00ab40001a, 0x2ad00ab400019,
    0x210207ce040390, 0x24b400071, 0x25400afc00019, 0x336400051, 0x1640be8c403f0, 0x99002bc00049,
    0x2a000ac00001a, 0x18000a11040430, 0x26000af400019, 0x19800e70440450, 0x29d00ac400019,
    0x255b0d9f040490, 0x11f608e10404b0, 0x28000adc00019, 0x1c9400091, 0x2f5e08f88404f0,
    0x24c000071, 0x337400051, 0x1764000b1, 0x2a000ac400019, 0x5fc002b1, 0x27a70b89440570,
    0x2a600ac00001a, 0xcdf7, 0x255e05c30405d0, 0x1c9c00091, 0x338000051, 0x187709fac40610,
    0x4dc00351, 0x2a400ac400019, 0x338400051, 0x28700adc00019, 0x2aa00ac00001a, 0x24d000071,
    0x2ab00ac00001a, 0x101c00101, 0x1ca400091, 0x24d400071, 0x2a800ac400019, 0x8e4001d1,
    0x21300b3c00019, 0x541009840790, 0x28c00adc00019, 0x2af00ac00001a, 0x1774000b1,
    0x26f00af400019, 0x24dc00071, 0x339c00051, 0x2ac00ac400019, 0x31c00531, 0x18930555c40870,
    0x2ad00ac400019, 0xce87, 0x1670067bc408b0, 0x29000adc00019, 0x33a400051, 0x24e400071,
    0x102400101, 0x2af00ac40001a, 0xd9800131, 0x230a0762840930, 0x27400af400019, 0x1cb400091,
    0x383a000e440970, 0x2b100ac400019, 0x2b100ac40001a, 0x254006f1, 0x29400adc00019, 0xcec7,
    0x3a400471, 0x27700af400019, 0x33b400051, 0x27800af400019, 0x1db30994c40a50, 0x26f00afc00019,
    0x2ab00acc0001a, 0x1a170f72440ab0, 0x29800adc00019, 0x2ac00acc0001a, 0x8ec001d1, 0x102c00101,
    0x262035fc40b10, 0x25400b1400019, 0x3b0a0acd840b50, 0x273c04e6040b70, 0xf700c2c00019,
    0x1cc400091, 0x38c00491, 0x27400afc00019, 0x36f0901440bd0, 0x103000101, 0x2b100acc0001a,
    0x28000af400019, 0xcf47, 0x250400071, 0x29f00adc00019, 0x33d400051, 0x1ccc00091,
    0x2a000adc00019, 0x4e400351, 0x103400101, 0x2a100adc0001a, 0x28400af400019, 0x13020fc1040d50,
    0x1794000b1, 0x13f4000d1, 0x10c508d5040db0, 0x2a400adc00019, 0x33e400051, 0x28700af400019,
    0x2a500adc0001a, 0x251400071, 0x28800af400019, 0x70400251, 0x2a700adc00019, 0x8f4001d1,
    0x2a800adc00019, 0xd750cde440ed0, 0x103c00101, 0x33f400051, 0x6640480c40f30, 0x28c00af400019,
    0x3c400451, 0x10340c31040f70, 0x252000071, 0x138703ea840f90, 0x2ac00adc00019, 0x2ac00adc0001a,
    0x3d50306840ff0, 0x340000051, 0x1ce400091, 0xdb000131, 0x340400051, 0x864001f1,
    0x28700afc00019, 0x2af00adc0001a, 0x4730f264410b0, 0x28800afc00019, 0x1404000d1,
    0x1b750966c410f0, 0x104400101, 0x6fd09b7441110, 0x341000051, 0xb0e0d82041150, 0x1a950693441170,
    0xab00c7c00019, 0x341400051, 0x1ff101510411b0, 0x28c00afc00019, 0xd32, 0x400d32, 0x10000400d33,
    0x2b500adc0001a, 0x4c00d32, 0x5400d32, 0xac00d32, 0x14000d32, 0x1e400d32, 0x34000d32,
    0x34400d32, 0x2c000d32, 0x34c00d32, 0x31c00d32, 0x24000d32, 0x20800bb400019, 0x1da000091,
    0x1840000b1, 0x355c00051, 0x2a400b3c00019, 0x21000bb400019, 0x2c400b240001a, 0x6124, 0xd5b7,
    0x68400291, 0x29800671, 0x357000051, 0x160b107a842cd0, 0x21300bb400019, 0x1d870952c42d10,
    0x21400bb400019, 0x1db400091, 0x15b00693042d70, 0x1f700bcc00019, 0x10af0984842d90, 0x357c00051,
    0x2ac00b3c00019, 0x6144, 0xe1400131, 0x358000051, 0x1494000d1, 0x21800bb400019, 0x358400051,
    0x1854000b1, 0x2c300b2c0001a, 0xbb048ac42eb0, 0x18400c2c00019, 0x2c400b2c0001a, 0x264000071,
    0xa890c11442f10, 0x2b200b3c00019, 0x7e00ec5842f50, 0x264400071, 0x1ff00bcc00019, 0x359400051,
    0x20f00bc000019, 0x2c800b2c0001a, 0x10c000101, 0x2c900b2c0001a, 0x2b600b3c00019, 0xe1c00131,
    0x2b700b3c00019, 0x35e50349443090, 0x2b800b3c00019, 0x1d910a51c430d0, 0x57a05d34430f0,
    0x10c400101, 0x2b900b3c0001a, 0x2aef0ab5843130, 0x1c000c0400019, 0x29880b8c843150]
  ++ [0x2bb00b3c00019, 0x30400591, 0x2bc00b3c00019, 0x1dd400091, 0x61a4, 0x2bd00b3c00019,
    0x2e76005f843210, 0x22800bb400019, 0x2be00b3c0001a, 0x2ec100f043270, 0x266000071, 0x186c000b1,
    0x9f50fc74432b0, 0xd6f7, 0x944001d1, 0x266400071, 0x35c000051, 0x2c100b3c0001a,
    0xdcd0c83c43330, 0x22c00bb400019, 0x35c400051, 0x20f00bcc00019, 0xc550eb0443390,
    0x21000bcc00019, 0x2c400b3c0001a, 0x35cc00051, 0x2c500b3c00019, 0x1de400091, 0x40400431,
    0x267000071, 0xd747, 0x2c700b3c00019, 0x35d400051, 0x267400071, 0x21400bcc00019,
    0x2c800b3c0001a, 0x6af0f284434f0, 0x18400c4000019, 0x2c900b3c0001a, 0x35dc00051,
    0x2ca00b3c00019, 0x3e0e0bb8043550, 0xe1f0ed1c43570, 0x23500bb400019, 0xcd400151,
    0x33f08fac435b0, 0x1df000091, 0x35e400051, 0x268000071, 0x6204, 0x38c004c1, 0x1df400091,
    0x268400071, 0x2cf00b3c00019, 0xc920f83443690, 0x1884000b1, 0x23a00bb400019, 0x18d70aa5c436d0,
    0x14c0000d1, 0x35f400051, 0x8b4001f1, 0x23c00bb400019, 0x2d209d9043750, 0x1dfc00091,
    0x2c900b440001a, 0x35fc00051, 0xd7f7, 0x14c4000d1, 0x360000051, 0x2585077f443810, 0x269400071,
    0x24000bb400019, 0x3e200b4843850, 0x1e0400091, 0x8140ede0438b0, 0x6244, 0x10e400101,
    0x269c00071, 0x3fe0596843930, 0x24400bb400019, 0xd847, 0x2540b1e043970, 0x6254,
    0x1cc409b5843990, 0x22800bcc00019, 0x1e25015c8439d0, 0x1d660d7f8439f0, 0x19800c4000019,
    0x954001d1, 0x1898000b1, 0x103108cc43a30, 0x24800bb400019, 0xc730644843a50, 0x3ec00451,
    0x24900bb400019, 0x90b0ea7c43a90, 0x22c00bcc00019, 0x362400051, 0x23c00bc000019,
    0x19960e5ac43b10, 0x26b000071, 0x2c400b540001a, 0x1e1800091, 0x24d00bb400019, 0x6284,
    0x26b400071, 0x15400c7c00019, 0x7210d3043bd0, 0x24000bc000019, 0x29210be8043c10, 0xce800151,
    0x18a4000b1, 0x1b000c3400019, 0x2c800b540001a, 0x132f0c26443c70, 0x98c032b443c90,
    0x25200bb400019, 0x2ca00b540001a, 0x131a0f07c43cf0, 0x364000051, 0x1e2400091, 0x25400bb400019,
    0x364400051, 0x26c400071, 0x3f0b0275843d90, 0x1c000c2c00019, 0x2ce00b540001a, 0x364c00051,
    0x2d400601, 0x2cf00b540001a, 0x1e2c00091, 0x25800bb400019, 0x12ae0389c43e50, 0xe520319043e70,
    0x365400051, 0x23c00bcc00019, 0x1cb9038e843ed0, 0x18b4000b1, 0x10fc00101, 0x2d300b540001a,
    0x215607f6043f30, 0x25c00bb400019, 0x1e3400091, 0x1e61085043f90, 0x394004c1, 0x366400051,
    0x14ec000d1, 0x1b000c4000019, 0x26dc00071, 0x26000bb400019, 0x2ce00b5c0001a, 0x62f4,
    0x366c00051, 0x25200bc000019, 0x2cf00b5c0001a, 0x25300bc000019, 0xd9c7, 0x5481055c440f0,
    0x1e4000091, 0x367400051, 0xd9d7, 0x274006f1, 0x26400bb400019, 0x964001d1, 0x367800051,
    0x71f0f3e444170, 0x1e4400091, 0x18c4000b1, 0xd9f7, 0x52400351, 0x368000051, 0x2d500b5c0001a,
    0x39105fa844230, 0x26f000071, 0x368400051, 0xb6a1041444290, 0x26f400071, 0x24c00bcc00019,
    0x2c400b6c0001a, 0x232c08410442f0, 0x110c00101, 0x2c500b6c0001a, 0x26c00bb400019, 0xda47,
    0xab00d1c00019, 0xcb10d4b044390, 0x316b0a53c443b0, 0x17400c7c00019, 0x1e5400091,
    0x6ea0f558443f0, 0x270000071, 0x2c900b6c0001a, 0x27000bb400019, 0x2ca00b6c0001a, 0x270400071,
    0x25300bcc00019, 0xda87, 0x25400bcc00019, 0x36a400051, 0x1e5c00091, 0x111400101,
    0x2cd00b6c0001a, 0x4b80fe7044530, 0x27400bb400019, 0x270c00071, 0x3c5e0343844570,
    0x26600bc000019, 0x64f0c7a444590, 0xe6400131, 0x27600bb400019, 0x37a70efc0445d0,
    0x27700bb400019, 0x36b400051, 0x269d0c54444630, 0x27800bb400019, 0x279d0407c44650, 0x34c00531,
    0x36bc00051, 0x26b00bc000019, 0x2d400b6c0001a, 0x26c00bc000019, 0x1a9c0fdd044710, 0x18e4000b1,
    0x21800c0400019, 0x36c400051, 0x2d700b6c0001a, 0x26f00bc000019, 0x2d800b6c0001a, 0x36cc00051,
    0x27f00bb400019, 0x1b80258444810, 0x15dc10a9444830, 0x28000bb400019, 0x1e7400091, 0x52c00351,
    0x36d400051, 0x63b4, 0x26400bcc00019, 0x284006d1, 0x155f0bcc4448f0, 0x112400101,
    0x2d300b740001a, 0x10440d14044930, 0x18f0000b1, 0x5b71104044950, 0x1e7c00091, 0x27600bc000019,
    0xdb87, 0x20e605c28449b0, 0x27700bc000019, 0x36e400051, 0x382b01578449f0, 0x28700bb400019,
    0x2b2f04ef044a10, 0x28800bb400019, 0x2d800b740001a]
  ++ [0x36ec00051, 0x26b00bcc00019, 0x273c00071, 0x26c00bcc00019, 0x6400f9b844ad0, 0x274000071,
    0x39a7071f044b10, 0x39ab0324844b30, 0x28c00bb400019, 0x1524000d1, 0x63f4, 0x274400071,
    0x26f00bcc00019, 0x1d3804ed444b90, 0xdbf7, 0x2ca00b840001a, 0x11a20a8f044bf0, 0x370000051,
    0x6404, 0x97c001d1, 0x29000bb400019, 0x370400051, 0x2cd00b840001a, 0x280e072f844cb0,
    0x77000251, 0x1e9400091, 0x31dc0762844cf0, 0x113400101, 0xdf2, 0x400df2, 0x10000400df3, 0xdc47,
    0x4c00df2, 0x5400df2, 0xac00df2, 0x14000df2, 0x1e400df2, 0x34000df2, 0x2ac00df2, 0x34400df2,
    0x2c000df2, 0x37c00df2, 0x4000e32, 0x11c00e32, 0x1c000e32, 0xdc00e32, 0x22c00e32, 0x24000e32,
    0x1c00e52, 0x1c000e52, 0x31c00e52, 0x2c000e52, 0x38c00e32, 0x38c00e52, 0x34000e52, 0x38400e52,
    0xfc00e92, 0x14000e92, 0x1bc00e92, 0x1c000e92, 0x25400e92, 0x31c00e92, 0x39c00e92, 0x34000e92,
    0x2c000e92, 0x39400e92, 0xd400e0c00019, 0x27400cc400019, 0x2cf00c7c00019, 0x2d000c7c00019,
    0x20c000091, 0x27800cc400019, 0x20c400091, 0x3afc00051, 0xebf7, 0x3dde0c2bc49bd0, 0x2a2400071,
    0x3b0000051, 0x31100c4c0001a, 0x22c00d0400019, 0x3b0400051, 0x1ad4000b1, 0x20f00d1c00019,
    0x22ee04ff849c90, 0x2d800c7c00019, 0x30000c5c0001a, 0x127400101, 0x30100c5c0001a, 0x6b64,
    0x3b1000051, 0x32c905c3449d50, 0x21300d1c00019, 0x3b1400051, 0x28e90e8d049db0, 0x21400d1c00019,
    0x20d400091, 0x14860d56849df0, 0x8500e5c00019, 0x9d2061c849e10, 0x28400cc400019,
    0x30600c5c0001a, 0x23500d0400019, 0xe1400151, 0x3e4004c1, 0x3b2400051, 0x2a4000071,
    0x30900c5c0001a, 0x372e04b1849f30, 0x28800cc400019, 0x30a00c5c0001a, 0x8609a2c49f70, 0xecb7,
    0xa34001d1, 0x3b3000051, 0x16c4000d1, 0x24d3052a449ff0, 0x128000101, 0x3b3400051,
    0x28c00cc400019, 0x2a4c00071, 0x43db0f1a44a090, 0x2e800c7c00019, 0x31000c5c0001a, 0x128400101,
    0xed07, 0x2a5400071, 0x29000cc400019, 0x3b4400051, 0x18030b1104a170, 0xf700e0c00019,
    0x31300c5c0001a, 0x67210ea84a1b0, 0x20f000091, 0x19160fd904a1d0, 0x3b4c00051, 0x2ed00c7c00019,
    0x181f11cc44a210, 0xf7211f284a230, 0x29400cc400019, 0x20f400091, 0x41d711a784a270,
    0x22700d1c00019, 0x3b5400051, 0x6be4, 0x2f000c7c00019, 0x30e00c640001a, 0x2a6400071,
    0x15c00dc000019, 0x16d4000d1, 0x3b5c00051, 0x29800cc400019, 0x22780737c4a350, 0x6bf4,
    0x20fc00091, 0x2f300c7c00019, 0x12be0ddf04a390, 0x3551071e84a3b0, 0x2f400c7c00019, 0x3b6400051,
    0x39400531, 0x210000091, 0x70019644a410, 0x2a7000071, 0x31400c640001a, 0x29d00cc400019,
    0x210400091, 0x1db30994c4a4b0, 0x2f800c7c00019, 0xedc7, 0x129400101, 0x3b7400051,
    0x2a000cc400019, 0x31800c640001a, 0x13050dd4c4a570, 0x20f4016b44a590, 0x2fc00c7c00019,
    0x30600c740001a, 0xf12, 0x400f12, 0x10000400f13, 0x4c00f12, 0x7400f12, 0xac00f12, 0x14000f12,
    0x1e400f12, 0x34000f12, 0x39c00f12, 0x2c000f12, 0x38c00f12, 0x37c00f12, 0x39400f12,
    0x2b7000071, 0x2a400d1c00019, 0x31500cc400019, 0x2a800d1c00019, 0x2c700d0400019, 0x3c400f12,
    0x31800cc400019, 0x6ee4, 0x77000291, 0xa84001d1, 0x25400831, 0x3d0000051, 0x2b9400071,
    0x31c00cc400019, 0x3d0400051, 0x6ef4, 0x2cd00d0400019, 0x32700cbc0001a, 0x16880d7104c4b0,
    0x404004c1, 0x32800cbc0001a, 0x3204000f84c4f0, 0x1bc0000b1, 0xd280a5704c510, 0x32000cc400019,
    0x50511d444c550, 0x1680c08c4c570, 0x3d1400051, 0x1bc4000b1, 0x28700d4000019, 0x32c00cbc0001a,
    0x2ba400071, 0x131800101, 0x32d00cbc0001a, 0x20c00ae904c630, 0x32400cc400019, 0x21f400091,
    0x2b700d1c00019, 0x4a44031f84c690, 0x2b800d1c00019, 0x319b0f7244c6d0, 0x28c00d4000019,
    0x32700cc40001a, 0x8711100c4c730, 0x2bb000071, 0x84400251, 0xf4b7, 0x32900cc40001a,
    0x1d5f0c9504c7b0, 0x3d3000051, 0x504003d1, 0x220000091, 0x3d3400051, 0x32c00cc400019,
    0x29b906afc4c850, 0x1bd4000b1, 0x2bf00d1c00019, 0x2bbc00071, 0x32a908cbc4c8b0, 0xf4f7,
    0x2282055944c8d0, 0x234008b1, 0x3d4000051, 0x32f00cc40001a, 0x104709a3c4c930]
  ++ [0x33000cc400019, 0x3d4400051, 0x1900a8d44c970, 0x720002b1, 0x1418124b84c990, 0x220c00091,
    0x1f700dc000019, 0x1e00072744c9d0, 0x2c500d1c00019, 0x1794000d1, 0x2e400d0400019,
    0x16eb0a8b84ca50, 0x9e4001f1, 0x2e500d0400019, 0x3d5400051, 0x30ff09e584cab0, 0x2bd000071,
    0x221400091, 0x1c00f4000019, 0xa94001d1, 0x3d5c00051, 0x2e800d0400019, 0x43400491, 0xf587,
    0x2bd800071, 0x3cad06f744cbb0, 0x29f00d4000019, 0x3d6400051, 0x2cd00d1c00019, 0x160b063d04cc10,
    0x1df40beb44cc30, 0x32800cd40001a, 0x1f170b6c44cc70, 0x2ed00d0400019, 0x32900cd40001a,
    0x2d000d1c00019, 0x19e12cc04ccd0, 0x2be400071, 0x133400101, 0x3d7400051, 0x43ba1012c4cd30,
    0x2f000d0400019, 0x37400591, 0x46e8112784cd90, 0x3d7c00051, 0xf5f7, 0xea400151,
    0x1e2c0a5544cdf0, 0x3d8000051, 0x7d9114244ce10, 0x2bf000071, 0x3d8400051, 0x3d510e5c04ce70,
    0x33100cd40001a, 0x2bf400071, 0x2d800d1c00019, 0x33200cd40001a, 0x133c00101, 0x33300cd40001a,
    0x10b80bfe44cf30, 0x3d9000051, 0x223400091, 0x6ff4, 0x103400131, 0x3d9400051, 0x20f00dc000019,
    0x32c00cdc0001a, 0x2c0000071, 0x7004, 0x11ca02bdc4d030, 0x2fc00d0400019, 0x63f0cf504d050,
    0x2c0400071, 0x2fd00d0400019, 0x1a9a0d4004d090, 0x21ff0ae184d0b0, 0x2e000d1c00019, 0x3da400051,
    0x134400101, 0x214a0a79c4d110, 0x30000d0400019, 0x33200cdc0001a, 0x30100d0400019, 0x224400091,
    0x2e400d1c00019, 0x251f06f704d1d0, 0x2e500d1c00019, 0x3db400051, 0x7034, 0x3912048404d230,
    0x30400d0400019, 0xaa4001d1, 0x3db800051, 0x205e0b3284d270, 0x56b059ec4d290, 0x3dbc00051,
    0x1c10000b1, 0x7044, 0x3dc000051, 0xeb400151, 0x30800d0400019, 0x3dc400051, 0x1c14000b1,
    0x5d400351, 0x2bf00d4000019, 0x225400091, 0x3dcc00051, 0x30b00d0400019, 0x588057f84d410,
    0x104400131, 0x1c200e0c00019, 0x16ae026404d450, 0x19830e4404d470, 0x30d00d0400019, 0x3dd400051,
    0x2f000d1c00019, 0x2c2c00071, 0x7074, 0x135400101, 0x32d00cec0001a, 0xf777, 0x32e00cec0001a,
    0x3de000051, 0x127130cc4d590, 0x2c3400071, 0x2f400d1c00019, 0x3de400051, 0xaac001d1,
    0x22800dc000019, 0x226400091, 0x106c08b8c4d630, 0x1c00f6400019, 0x33200cec0001a,
    0x31500d0400019, 0x2c3c00071, 0x2b370a9a04d6b0, 0x2f800d1c00019, 0xf7c7, 0x5c4080384d6f0,
    0x22c00dc000019, 0x3df400051, 0x226c00091, 0x31800d0400019, 0xfb2, 0x400fb2, 0x10000400fb3,
    0x33700cec0001a, 0x2c00fb2, 0x5400fb2, 0x4000fb2, 0x2d400fb2, 0x2f400fb2, 0x34000fb2,
    0x29800fb2, 0x24c00fb2, 0x32400fb2, 0x35c00fb2, 0x3dc00fb2, 0x2c000fb2, 0x2d4000071, 0xfd77,
    0x3f6000051, 0x3ec00fb2, 0x34100d4000019, 0xfdb7, 0x3f7000051, 0x1012, 0x10000401013,
    0x2c01012, 0x401012, 0x7401012, 0xac01012, 0x1c401012, 0x1c001012, 0x29801012, 0x35c01012,
    0x3dc01012, 0x40001012, 0x34001012, 0x40401012, 0x34401012, 0x10357, 0x10c00f6400019,
    0x31f00dc000019, 0x3e401012, 0x2d800dfc00019, 0x288040f0514d0, 0x26d311b6c51530,
    0x11800f6400019, 0x10447, 0x1d94000b1, 0x2c700e0c00019, 0x411400051, 0x26400e5c00019,
    0x62400351, 0x2e8000071, 0x3ec00531, 0x411c00051, 0x2ca00e0c00019, 0xdbc05fb851650,
    0x33070b89451670, 0x32a00dc000019, 0x10487, 0x112400131, 0x243000091, 0x446a0f1fc516d0, 0x7674,
    0x32c00dc000019, 0x36300d940001a, 0x412800051, 0x12000f6400019, 0x2e8c00071, 0x3a010f06c51770,
    0x1da0000b1, 0x1c3801ffc51790, 0x413000051, 0x104c7, 0x80701108517f0, 0x33000dc000019,
    0x413400051, 0x1547036a451830, 0x33100dc000019, 0x7f400291, 0x26f00e5c00019, 0x35f00d9c0001a,
    0x104f7, 0x36000d9c0001a, 0x76a4, 0x414000051, 0x21db05af451910, 0x12800f6400019,
    0x35741351851950, 0x6c406d8851970, 0xf700f8c00019, 0x244400091, 0x76b4, 0x191c000d1,
    0x2d800e0c00019, 0x36400d9c0001a, 0x414c00051, 0x33800dc000019, 0x36500d9c0001a,
    0xa8f0c37851a30, 0x415000051, 0x76c4, 0x27700e5c00019, 0x415400051, 0x2f000dfc00019,
    0x2eac00071, 0x2ce90931c51af0, 0x15c00f4000019, 0x35500dac0001a, 0x26600e6c00019, 0x1924000d1,
    0x113400131, 0x2f300dfc00019]
  ++ [0xb2211a6051b90, 0x12990cbf051bb0, 0x2f400dfc00019, 0x416400051, 0x34000dc000019,
    0x16330e90451c10, 0x34100dc000019, 0x35a00dac0001a, 0x27f00e5c00019, 0xf9400151,
    0x2f800dfc00019, 0x339f0487451cd0, 0x147400101, 0x417400051, 0x13800f6400019, 0x35e00dac0001a,
    0x4fb0790851d70, 0x26f00e6c00019, 0x35f00dac0001a, 0x417c00051, 0x34700dc000019,
    0x36000dac0001a, 0x34800dc000019, 0x246400091, 0x16900f4000019, 0x418400051, 0x28700e5c00019,
    0x1934000d1, 0x4e400431, 0x2ed000071, 0x36400dac0001a, 0x147c00101, 0x36500dac0001a,
    0x2ed400071, 0x419000051, 0x73412b0851f50, 0x27700e6c00019, 0x419400051, 0xa94001f1,
    0x63000351, 0x4a960392051fd0, 0x35000dc000019, 0x36900dac0001a, 0x419c00051, 0x25200e8c00019,
    0x247400091, 0x1dd4000b1, 0x2f300e0c00019, 0x4020d80852090, 0x30800dfc00019, 0x36c806d18520d0,
    0x3bea09b44520f0, 0x1940000d1, 0x254008d1, 0x1b110dc0c52130, 0x1c0105400019, 0x32640c63052150,
    0x41ac00051, 0x35600dc000019, 0x36500db40001a, 0x1792049a4521b0, 0x35700dc000019, 0x2eec00071,
    0x248000091, 0x41b400051, 0x14c00f6400019, 0x36800db40001a, 0x1ab01cec52270, 0x248400091,
    0xa905b48522b0, 0x31000dfc00019, 0x1de20f5f4522d0, 0x35c00dc000019, 0x63400351, 0x1de4000b1,
    0xd800fc400019, 0x41c400051, 0x28700e6c00019, 0x1a8e0d6a852390, 0x454004c1, 0x8e400251,
    0x44e203578523f0, 0x2f0000071, 0x36000dc00001a, 0x249000091, 0x6491145452450, 0x2f0400071,
    0x29f00e5c00019, 0x41d400051, 0x77b4, 0x115803980524b0, 0x31800dfc00019, 0x249400091,
    0x115400131, 0x149400101, 0x6d90634452510, 0x1df0000b1, 0x3b90ad5052550, 0x26700e8c00019,
    0x10787, 0xb5c001d1, 0x31c00dfc00019, 0x41e400051, 0x1df4000b1, 0x36800dc000019,
    0x36800dc00001a, 0x2f1400071, 0x31e00dfc00019, 0x36900dc00001a, 0x324a147d852670, 0x107b7,
    0x48400491, 0x77e4, 0x41f000051, 0x382806918526d0, 0x30d00e0c00019, 0x41f400051,
    0x340105400019, 0x3930031452750, 0xaa4001f1, 0x26f00e8c00019, 0x11b1097bc52790,
    0x427b08ce4527b0, 0x107f7, 0x36f00dc00001a, 0x45210c9a4527f0, 0x420000051, 0x92a1256052810,
    0x24ac00091, 0x16400f6400019, 0x420400051, 0x1d590f86c52870, 0xf700fbc00019, 0x36d00dc40001a,
    0x1e04000b1, 0x27400e8c00019, 0x36e00dc40001a, 0x14a400101, 0x36f00dc40001a, 0xa060c3a452930,
    0x2f3000071, 0x24b400091, 0x29f00e6c00019, 0x421400051, 0x2f3400071, 0x32c00dfc00019,
    0x36800dcc0001a, 0x7ea0add0529f0, 0x2b500e5c00019, 0x36900dcc0001a, 0x42e408de852a30,
    0x2b600e5c00019, 0x20c80357052a50, 0x24bc00091, 0x2b700e5c00019, 0x10887, 0x33000dfc00019,
    0x422400051, 0x2f4000071, 0x5f0a36852b10, 0x31e00e0c00019, 0xaac001f1, 0x422c00051, 0x7854,
    0x24c400091, 0x423000051, 0x108c7, 0x4cc00451, 0x2bd00e5c00019, 0x1ebd0f80052c10, 0x1e18000b1,
    0x17400f6400019, 0xfc400151, 0xf1e10ea852c70, 0x2bf00e5c00019, 0x37300dcc0001a, 0x24cc00091,
    0x108f7, 0x36000ddc0001a, 0x424000051, 0x8f400251, 0x2f5400071, 0x24d000091, 0x2521421052d50,
    0x28700e8c00019, 0x7884, 0x6bd1307c52db0, 0x28800e8c00019, 0x24d400091, 0x1fd07fec52df0,
    0x1980000d1, 0x2f5c00071, 0x1e24000b1, 0x32a00e0c00019, 0x31e00841852e50, 0x4b450f63852e70,
    0x2c700e5c00019, 0x425400051, 0x34000dfc00019, 0x1984000d1, 0x2f6400071, 0x34100dfc00019,
    0x36900ddc0001a, 0x425c00051, 0x2ca00e5c00019, 0x36a00ddc0001a, 0x2b700e6c00019,
    0x353f076ec52f90, 0x34400dfc00019, 0x1b750f9e052fd0, 0x2e520947452ff0, 0x14c000101,
    0x24e400091, 0x10d2, 0x4010d2, 0x100004010d3, 0x4c010d2, 0x54010d2, 0xac010d2, 0x140010d2,
    0x1e4010d2, 0x140010f2, 0x344010d2, 0x38c010d2, 0x23c010f2, 0x240010f2, 0x32c010f2, 0x400010f2,
    0x25c010f2, 0x3ec010f2, 0x43c010f2, 0x434010f2, 0x340010f2, 0x36400e5c00019, 0x32a00e8c00019,
    0x24c00f4000019, 0x1152, 0x401152, 0xa401152, 0x4001152, 0x10000401153, 0x14401152, 0x1c401152,
    0x29801152, 0x35c01152, 0x40001152, 0x37c01152, 0x2c01192, 0x150000401193, 0x11401192,
    0x90000401193, 0x1c001192, 0x1b401192, 0x24c01192, 0x44401192, 0x45c01192]
  ++ [0x40001192, 0x2bc01192, 0x2c001192, 0x43c01192, 0x34001192, 0x29801192, 0x27400fc400019,
    0x2f000f6400019, 0x2f800f6400019, 0x37b00efc00019, 0x37c00efc00019, 0x278000091,
    0x37e00efc00019, 0x37f00efc00019, 0x278400091, 0x37400671, 0x38000efc00019, 0x472400051,
    0x163c00101, 0x3b300ed40001a, 0x14a11a7858f30, 0x31e00f4c00019, 0x3b400ed40001a, 0x472c00051,
    0x38300efc00019, 0xc148b058f90, 0x278c00091, 0x38400efc00019, 0x2d36061c858fd0,
    0x23e10134c58ff0, 0x164000101, 0x473400051, 0x33100f4000019, 0x10240d84459050, 0x50400471,
    0x26f00fdc00019, 0x8184, 0x11cf7, 0x279400091, 0x32e400071, 0x474000051, 0x593078d459110,
    0x2064000b1, 0x30800f6400019, 0xae0437459150, 0x3b307cec59170, 0x3a900ee40001a,
    0x124911b4c591b0, 0x38c00efc00019, 0x4f4d12434591d0, 0x81a4, 0x33800f4000019, 0x3ab00ee40001a,
    0x134f0362459230, 0x32a00f4c00019, 0x11d47, 0xc4c001d1, 0x30d00f6400019, 0x475400051, 0x81b4,
    0x32f400071, 0x39000efc00019, 0x9a400251, 0x475800051, 0x1c011c000019, 0x27a400091,
    0x2070000b1, 0x8b400291, 0x52c00451, 0x39300efc00019, 0x17a80bfb059390, 0x6bc00351,
    0x39400efc00019, 0x476400051, 0x3ca076c0593f0, 0x330000071, 0x4e400491, 0x27ac00091,
    0x34100f4000019, 0x3b400ee40001a, 0x476c00051, 0x39700efc00019, 0x3b500ee40001a, 0x81e4,
    0x39800efc00019, 0x1f2212ab4594d0, 0x165400101, 0x477400051, 0x46ef09cf459530, 0x31800f6400019,
    0x330c00071, 0x81f4, 0x24415c5059570, 0x39b00efc00019, 0x40400591, 0x5dc003d1, 0x331000071,
    0x3b000eec0001a, 0x478000051, 0xc54001d1, 0x331400071, 0x31c00f6400019, 0x478400051,
    0x28700fdc00019, 0x3b300eec0001a, 0x25590d04c596b0, 0x36400f2c00019, 0x1b84000d1,
    0x12dd14b20596f0, 0x165c00101, 0x1de41589859710, 0x479000051, 0x3bc156e859750,
    0x2cab1261859770, 0x3a300efc00019, 0x479400051, 0x3a400efc00019, 0x42c20108c597d0, 0x332400071,
    0x35000f4000019, 0x3b900eec0001a, 0x32400f6400019, 0x3ba00eec0001a, 0x2f6c01cc859870,
    0x2f300f8c00019, 0xcef0841059890, 0x3a800efc00019, 0x47a400051, 0x38c00651, 0x166400101,
    0x3a900efc0001a, 0x333000071, 0x3aa00efc0001a, 0x47ac00051, 0x3ab00efc00019, 0x3ab00efc0001a,
    0x333400071, 0x3ac00efc00019, 0x27d400091, 0x35800f4000019, 0x47b400051, 0x32c00f6400019,
    0x6c400351, 0x2bf00fbc00019, 0x111400151, 0x4d890d25859ab0, 0x11ef7, 0x3b000efc0001a,
    0x27dc00091, 0x47c000051, 0x18241063859b10, 0x7b4101c059b30, 0x33000f6400019, 0x47c400051,
    0x334400071, 0x3b300efc00019, 0x1dde0041859b90, 0x12e400131, 0x37800f2c00019, 0x3b400efc0001a,
    0x11f37, 0x27e400091, 0x20a4000b1, 0x47d000051, 0x442c141d859c50, 0x28c008d1, 0x37b00f2c00019,
    0x38fd005e459c90, 0x37c00f2c00019, 0x3b800efc0001a, 0x45400531, 0x167400101, 0x8260169859d10,
    0x47dc00051, 0x3ba00efc00019, 0x1ba4000d1, 0xd470137059d70, 0x37f00f2c00019, 0x20ac000b1,
    0x27f000091, 0x47e400051, 0x36800f4000019, 0x12ec00131, 0x3db1582459e30, 0x2100105400019,
    0x27f400091, 0x26dd04ab859e70, 0x3bf00efc00019, 0x212f10fdc59e90, 0x38400f2c00019,
    0x5b9150d459ed0, 0x336400071, 0x30d00f8c00019, 0x47f400051, 0x34000f6400019, 0x1d1b0064459f50,
    0x34100f6400019, 0x3b900f040001a, 0x11ff7, 0x112400151, 0x480000051, 0x1c540f6b85a010,
    0x34400f6400019, 0x480400051, 0x82f4, 0x12f400131, 0x2cd00fc400019, 0x280400091, 0x337400071,
    0x38c00f2c00019, 0x3be00f040001a, 0x20c0000b1, 0x8304, 0x34800f6400019, 0x12047,
    0x29f00fec00019, 0x481400051, 0x280c00091, 0x39000f2c00019, 0x3ae00f140001a, 0x5a9151dc5a1f0,
    0x338000071, 0x3af00f140001a, 0x298008b1, 0x481c00051, 0x39200f2c00019, 0x3b000f140001a,
    0x338400071, 0x39300f2c00019, 0xbb6139d05a290, 0x39400f2c00019, 0x482400051, 0x1bc0000d1,
    0x3b300f140001a, 0x864002b1, 0x35000f6400019, 0x3b400f140001a, 0x482c00051, 0x39700f2c00019,
    0x3b500f140001a, 0x39800f2c00019, 0x1bc4000d1, 0x26400971, 0x169000101, 0x12f111d445a410,
    0x1a1e1342c5a430, 0x2280105400019, 0x3b800f140001a, 0x2e490affc5a470, 0x39b00f2c00019,
    0xc74001d1, 0x483c00051, 0x39c00f2c00019, 0x3ba00f140001a, 0x3d030bcb05a4f0, 0x484000051]
  ++ [0x339c00071, 0x130400131, 0x35800f6400019, 0x484400051, 0x24b7082e85a590, 0x2d115e2c5a5b0,
    0x37800f4c00019, 0x3be00f140001a, 0x24e403b045a5f0, 0x3c400601, 0x3bf00f140001a,
    0x35c00f6400019, 0x12147, 0x8e3075ac5a670, 0x3a300f2c00019, 0x485400051, 0x3a400f2c00019,
    0x5210034905a6d0, 0x38c00f4000019, 0x1bd4000d1, 0x31820a3c85a730, 0x37e00f4c00019, 0x283400091,
    0x37f00f4c00019, 0x3c500f140001a, 0x33b400071, 0x3a800f2c00019, 0x486400051, 0x83a4,
    0x39000f4000019, 0x3bd00f1c0001a, 0x36400f6400019, 0x375506e905a850, 0x486c00051, 0x121b7,
    0x3912ae05a890, 0x83b4, 0x4ec1151545a8b0, 0x487000051, 0x121c7, 0x284000091, 0x487400051,
    0x20f0000b1, 0x83c4, 0x3b0a0e09c5a970, 0x2bf00fec00019, 0x284400091, 0x29d007bb45a9b0, 0x121f7,
    0x419e0bbd85a9d0, 0x20f4000b1, 0x488000051, 0x2a169e05aa10, 0x22be05c345aa30, 0x2f400fc400019,
    0x488400051, 0x3b300f2c00019, 0x17a1023385aa90, 0x83e4, 0x39b00f4000019, 0x3b400f2c0001a,
    0x16ac00101, 0x3b500f2c0001a, 0x131800131, 0x33d400071, 0x489000051, 0x22410e1d45ab50, 0x83f4,
    0x2c700fec00019, 0x489400051, 0xf1d008945abb0, 0x39000f4c00019, 0x285400091, 0x2100000b1,
    0x8404, 0x3ba00f2c00019, 0x3ba00f2c0001a, 0x39300f4c00019, 0x5f4003d1, 0x2963027dc5acb0,
    0x3a300f4000019, 0x48a400051, 0x33e400071, 0x16b400101, 0x3bd00f2c0001a, 0xcf11378c5ad30,
    0x37800f6400019, 0x54400451, 0x3a115cdc5ad70, 0x3bf00f2c00019, 0x481a06d6c5ad90,
    0x3c000f2c00019, 0x122c7, 0x2ce715c985adf0, 0x3a800f4000019, 0x48b400051, 0x6dc00351,
    0x37c00f6400019, 0xdb90e4985ae50, 0x39b00f4c00019, 0x9d400251, 0x48bc00051, 0x122f7, 0x8444,
    0x48c000051, 0x1db40e98c5af10, 0x286c00091, 0x38000f6400019, 0x48c400051, 0x2114000b1,
    0x115400151, 0x36615e585afb0, 0x287000091, 0x3c800f2c0001a, 0x340000071, 0x3c900f2c0001a,
    0x8464, 0x48d000051, 0x287400091, 0x340400071, 0x3cb00f2c00019, 0x48d400051, 0x3b300f4000019,
    0x5a0713a2c5b0d0, 0x53c093c45b0f0, 0x16c400101, 0x3c300f340001a, 0x26c9020b05b130,
    0x38800f6400019, 0x1b7502e545b150, 0x287c00091, 0x35700f8c00019, 0x32a90a1c45b190, 0x46400531,
    0x341000071, 0x48e400051, 0x288000091, 0x8e400291, 0x341400071, 0x4cc004c1, 0x3c800f340001a,
    0x3ba00f4000019, 0x288400091, 0x341800071, 0x3ac00f4c00019, 0x123c7, 0xbc4001f1, 0x16cc00101,
    0x48f400051, 0x5420063445b330, 0x1c10000d1, 0x3cc00f340001a, 0x133400131, 0x26f0104c00019,
    0x4b1e007b85b390, 0x84b4, 0x3bf00f4000019, 0x3bf00f400001a, 0x342400071, 0x3c000f4000019,
    0x1c14000d1, 0x5fc003d1, 0x2130000b1, 0x490400051, 0x3b300f4c00019, 0x3c200f400001a,
    0x9c60a4fc5b4b0, 0x36400f8c00019, 0x342c00071, 0x490c00051, 0x16d400101, 0x1f1a125785b510,
    0x491000051, 0x38c00671, 0x1e390fcc05b570, 0x2770104c00019, 0x491400051, 0x343400071,
    0x36800f8c00019, 0x522c10b4c5b5d0, 0x3c800f4000019, 0x27400951, 0x12477, 0x3c900f400001a,
    0x84f4, 0x492000051, 0x29a052345b690, 0x3cb00f4000019, 0x4d89047485b6d0, 0x298008d1,
    0x344000071, 0x28a400091, 0x21cf0e6945b730, 0x2740105400019, 0x963118405b750, 0x492c00051,
    0x3bf00f4c00019, 0x3ce00f400001a, 0x2144000b1, 0x3c000f4c00019, 0x9e400251, 0x3d000f4000019,
    0x493400051, 0x134400131, 0x3a400f6400019, 0x3cc00f440001a, 0xb9907f9c5b870, 0x85011e400019,
    0x50400491, 0x59eb0d2305b8b0, 0x3c400f4c00019, 0x3ce00f440001a, 0x16e400101, 0x10fb12a5c5b910,
    0x345400071, 0x3a800f6400019, 0x494400051, 0x33100fc400019, 0x3d100f440001a, 0x3c800f4c00019,
    0x8544, 0x7111523c5b9f0, 0x3ab00f6400019, 0x117400151, 0x3ac00f6400019, 0xca4001d1,
    0x2154000b1, 0x3cb00f4c00019, 0x33e4091945ba90, 0x37c00f8c00019, 0x3cc00f4c0001a, 0x346400071,
    0x28c000091, 0x1fa202b485bb10, 0x8564, 0x3b000f6400019, 0x3ce00f4c0001a, 0x3b100f6400019,
    0x28c400091, 0x4d4004c1, 0x219c151605bbd0, 0x3b300f6400019, 0x3d100f4c0001a, 0x1c3c000d1,
    0x347000071, 0x8f400291, 0x3d300f4c00019, 0x1a7516afc5bc90, 0x347400071, 0x38400f8c00019,
    0x448f05cfc5bcd0, 0x5adb021f45bcf0, 0x1c40000d1, 0x497400051, 0x30f01e3c5bd30, 0x34000fc400019]

def opsA16384_1 : List Nat :=
  [0x190e033e05bd50, 0x34100fc400019, 0x3c300f5c0001a, 0x125f7, 0x28d400091, 0xcac001d1,
    0x498000051, 0x1a6d119685be10, 0x34400fc400019, 0x498400051, 0x42f1135ec5be70, 0x216c000b1,
    0x1a1a107485beb0, 0x38c00f8c00019, 0x3a400651, 0x498c00051, 0x16fc00101, 0x3c900f5c0001a,
    0x3c000f6400019, 0x118400151, 0x1eb7067885bf70, 0x29f0104c00019, 0x499400051, 0x39000f8c00019,
    0x3cc00f5c0001a, 0x4c9403db05bff0, 0x2b50103c00019, 0x28e400091, 0x3759006845c030, 0x12677,
    0x3ce00f5c0001a, 0x49a000051, 0x5f16eac5c090, 0xaf2002645c0b0, 0x39400f8c00019, 0x49a400051,
    0x170400101, 0x18b9097e05c110, 0x3c800f6400019, 0x9c31544c5c150, 0x85f4, 0x39700f8c00019,
    0xcb4001d1, 0x136400131, 0x39800f8c00019, 0x32510a7345c1d0, 0x34a400071, 0x2180000b1,
    0x49b400051, 0x149d046145c230, 0x2a00105400019, 0x28f400091, 0x50901104c5c270, 0x39b00f8c00019,
    0xcf106ad05c290, 0x49bc00051, 0x39c00f8c00019, 0x39430c0585c2d0, 0x2d1107085c2f0, 0x49c000051,
    0x3cf00f640001a, 0x3d000f6400019, 0x39de089605c350, 0x28fc00091, 0x1c60000d1, 0x3d100f640001a,
    0x54be146705c3b0, 0x36400fbc00019, 0x3d200f640001a, 0x37fe165c45c3f0, 0x290000091, 0x218c000b1,
    0x3d400f6400019, 0x1c64000d1, 0x1fae11f585c470, 0x3a300f8c00019, 0x49d400051, 0x3a400f8c00019,
    0x1860141385c4d0, 0x34c000071, 0x3d700f640001a, 0x49dc00051, 0x4dc004c1, 0x3d800f640001a,
    0x4c050813c5c570, 0x3d900f6400019, 0x3d900f640001a, 0x290c00091, 0x3a800f8c00019, 0x49e400051,
    0x33100fec00019, 0x3c700f740001a, 0x58400431, 0x36400fc400019, 0x2b8204ba45c650, 0x49ec00051,
    0x3ab00f8c00019, 0x2d5700eb05c690, 0x3ac00f8c00019, 0x291400091, 0x2bd0104c00019, 0x49f400051,
    0x34d400071, 0x36800fc400019, 0x3cc00f740001a, 0x20360f1085c770, 0x2bf0104c00019, 0x1c74000d1,
    0x127f7, 0x3ce00f740001a, 0x4a0000051, 0x3cf00f740001a, 0x21a4000b1, 0x2b80105400019,
    0x4a0400051, 0x3b300f8c00019, 0x1e2511c885c890, 0x37800fbc00019, 0x137c00131, 0x4a0c00051,
    0x172400101, 0x292400091, 0x4a1000051, 0x12847, 0x37b00fbc00019, 0x487f0506c5c990, 0x86b4,
    0x3ce0ff505c9b0, 0x37c00fbc00019, 0x11a400151, 0x3d92088805c9f0, 0x1c80000d1, 0x3d700f740001a,
    0x4a1c00051, 0x21b0000b1, 0x16d80d11c5ca50, 0x4bd0b8185ca70, 0x37f00fbc00019, 0x12887,
    0x34f400071, 0x293000091, 0x4a2400051, 0x21b4000b1, 0x172c00101, 0x614003d1, 0x3f7810fc05cb30,
    0x37800fc400019, 0x293400091, 0x3bf00f8c00019, 0x35d80668c5cb90, 0x21b8000b1, 0x3c000f8c00019,
    0x370f096bc5cbd0, 0x2c6b03d6c5cbf0, 0x350000071, 0x4a3400051, 0x37c00fc400019, 0x3d600f7c0001a,
    0x350400071, 0x2b50106400019, 0x3d700f7c0001a, 0x28450d21c5ccb0, 0x128f7, 0x3d800f7c0001a,
    0x4a4000051, 0x44b1621c5cd10, 0x38000fc400019, 0x252a042205cd50, 0x3a805de05cd70,
    0x2cd0105400019, 0x294400091, 0x23e30e3e45cdb0, 0x3c800f8c00019, 0xa50086105cdd0,
    0x38300fc400019, 0x1c94000d1, 0x351400071, 0x4a5000051, 0x12947, 0x8724, 0x3cb00f8c00019,
    0x1d2d10f985ce90, 0x4e4004c1, 0x3cc00f8c0001a, 0x51ab085605cef0, 0x2bf0106400019, 0x351c00071,
    0x2ae807ce05cf30, 0x39200fbc00019, 0x70400351, 0x39300fbc00019, 0x441162e45cf90,
    0x3c1e00a805cfb0, 0x3d000f8c00019, 0x4a6400051, 0x352400071, 0x174000101, 0xcd4001d1,
    0x38c00fc400019, 0x3d200f8c0001a, 0x4a6c00051, 0x3d300f8c00019, 0x3d300f8c0001a,
    0x3d400f8c00019, 0x352c00071, 0x295c00091, 0x174400101, 0x4a7400051, 0x171915d485d130,
    0x39000fc400019, 0x1ca4000d1, 0x768156c05d170, 0x39b00fbc00019, 0x3b9a089105d190, 0x4a7c00051,
    0x3d800f8c00019, 0x3d800f8c0001a, 0x43f8119fc5d1f0, 0x3d900f8c00019, 0x296400091, 0x34c00711,
    0x39400fc400019, 0x6fd0948c5d250, 0x2cd0106400019, 0x8784, 0x3dc00f8c00019, 0x3dc00f8c0001a,
    0xd0b065e85d2f0, 0x174c00101, 0x355e0c9345d310, 0x296c00091, 0x4a9000051, 0x12a47,
    0x5f7162005d370, 0x3a300fbc00019, 0x4a9400051, 0xcdc001d1, 0x3a400fbc00019, 0x3e000f8c0001a,
    0x39b00fc400019, 0x3e100f8c0001a, 0x4a9c00051, 0x3e200f8c00019, 0x354c00071, 0x3e300f8c00019,
    0x1cb4000d1, 0x13a400131, 0x3a800fbc00019, 0x4aa400051, 0x126033645d4f0, 0x175400101,
    0x3db00f940001a, 0x355400071, 0x2d80106400019, 0x87c4, 0x3ab00fbc00019]
  ++ [0x3dd00f940001a, 0x4731119a85d5b0, 0x3ac00fbc00019, 0xc0c001f1, 0x21f4000b1, 0x298000091,
    0x4ab400051, 0x3a400fc400019, 0x3e000f940001a, 0x3cf166645d670, 0x356000071, 0x298400091,
    0x3d7602f745d6b0, 0x3b000fbc00019, 0x18b115a405d6d0, 0x356400071, 0x3b100fbc00019,
    0x3e300f940001a, 0x3a800fc400019, 0x4ac400051, 0x87f4, 0x54400471, 0x3b300fbc00019,
    0x3e500f940001a, 0x298c00091, 0x38c00fdc00019, 0x1cc4000d1, 0x2200000b1, 0x8804, 0x4ad000051,
    0x43400591, 0x37b00fec00019, 0x2b150c63c5d890, 0x102a0caa05d8b0, 0x39000fdc00019, 0x299400091,
    0x8b4002b1, 0x176400101, 0x3d700fa40001a, 0xce8001d1, 0x3ba00fbc00019, 0x3d800fa40001a,
    0x2af114cc5d970, 0x3b100fc400019, 0x357c00071, 0xc14001f1, 0x39400fdc00019, 0x4ae400051,
    0x358000071, 0x24d51124c5da10, 0xc92144485da30, 0x31e0103c00019, 0x624003d1, 0x4aec00051,
    0x12bb7, 0x49730e5b05da90, 0x4af000051, 0x858155585dad0, 0x30d0104c00019, 0x4af400051,
    0x48400531, 0x3040105400019, 0x28400951, 0x2214000b1, 0x39b00fdc00019, 0x3e100fa40001a,
    0x12bf7, 0x3e200fa40001a, 0x3a400671, 0x4b0000051, 0x392d092545dc10, 0x359400071,
    0x3080105400019, 0x4cc6044005dc50, 0x71400351, 0x3c800fbc00019, 0xa2400251, 0x177400101,
    0x52400491, 0x8a1052385dd30, 0x3c000fc400019, 0x29b400091, 0x3cb00fbc00019, 0x4b1400051,
    0x3a400fdc00019, 0x3e000fac0001a, 0x38630a51c5ddf0, 0x2b50109c00019, 0x3e100fac0001a,
    0x2224000b1, 0x3c400fc400019, 0x191097105de50, 0x29bc00091, 0x39300fec00019, 0xcf4001d1,
    0x34f30a1985deb0, 0x3d000fbc00019, 0x4b2400051, 0x3310103c00019, 0x3e500fac0001a,
    0x3c800fc400019, 0x3e600fac0001a, 0x3d300fbc00019, 0x29c400091, 0x56bd0dcc85dfb0,
    0x3d400fbc00019, 0x10a9135545dfd0, 0x3cb00fc400019, 0x4b3400051, 0x12cd7, 0x3180105400019,
    0x88c4, 0x4b3800051, 0x134e12ae85e070, 0x39b00fec00019, 0x9f5090fc5e090, 0x12cf7,
    0x3d800fbc0001a, 0x2234000b1, 0x4b4000051, 0x57400451, 0x29d000091, 0x4b4400051, 0x35c400071,
    0x3b300fdc00019, 0x1cf4000d1, 0x8f1154ac5e1b0, 0x3dc00fbc00019, 0x29d400091, 0x4b4c00051,
    0x3ec00601, 0x25e6063f85e210, 0x4b5000051, 0x35cc00071, 0x3a300fec00019, 0x4b5400051,
    0x3a400fec00019, 0x148b0df505e2d0, 0x29dc00091, 0x3410103c00019, 0x8904, 0x4b5c00051,
    0x3e200fbc00019, 0x3e200fbc0001a, 0x43c00591, 0x5a000431, 0x101062f45e390, 0x2244000b1,
    0x3e400fbc00019, 0x4b6400051, 0x3310104c00019, 0x35dc00071, 0x3dc00fc400019, 0x31a809ce85e450,
    0x8924, 0x3e700fbc00019, 0x3e700fbc0001a, 0x3e800fbc00019, 0x1d04000d1, 0x35e400071,
    0x179400101, 0x11480c9985e510, 0x29ec00091, 0x32c0105400019, 0x4d0d12e545e550, 0x2ce16e285e570,
    0x2bf010ac00019, 0x3e400611, 0x159e122f85e5b0, 0x29f000091, 0xd04001d1, 0x4b8000051,
    0xa3400251, 0x205b01eec5e630, 0x3e400fc400019, 0x4b8400051, 0x2254000b1, 0x72000351,
    0x31c106d245e690, 0x35f400071, 0x3c800fdc00019, 0x3e600fc40001a, 0x4b8c00051, 0x179c00101,
    0x3e700fc40001a, 0x4b9000051, 0xd271453c5e750, 0x3cb00fdc00019, 0x2386072cc5e790,
    0x4a740fcc05e7b0, 0x3400104c00019, 0x3ea00fc40001a, 0x360000071, 0x4a970a6e85e810,
    0x3ec00fc400019, 0x3ec00fc40001a, 0x54e80e3585e870, 0x3570103c00019, 0x2a0400091,
    0x3d000fdc00019, 0x4ba400051, 0x3ef00fc400019, 0x3ef00fc40001a, 0x43ba046cc5e930,
    0x3f000fc400019, 0x120400151, 0x3f100fc400019, 0xaf901e785e990, 0x3d400fdc00019, 0x72400351,
    0x89a4, 0x30d0107c00019, 0x4bb400051, 0x1ba13d945ea30, 0x3400105400019, 0x3e000fd40001a,
    0x3410105400019, 0x1dc9004745ea90, 0x89b4, 0x25021573c5eab0, 0x3d800fdc00019, 0x2a1400091,
    0x3d900fdc00019, 0x299809c945eb10, 0x2270000b1, 0x4bc400051, 0x97d0b4e85eb70, 0x3310106400019,
    0x3e500fd40001a, 0x6ab160445ebb0, 0x3dc00fdc00019, 0x1332, 0x401332, 0x10000401333,
    0x3e700fd40001a, 0x4c01332, 0x7401332, 0xac01332, 0x14001332, 0x1e401332, 0x34001332,
    0x45401332, 0x4c001332, 0x50000001373]

def opsA16384 : List Nat :=
  opsA16384_0 ++ opsA16384_1

def stageA3 : List (Nat × List Nat) :=
  [(8192, opsA16384)]

def opsA24576 : List Nat :=
  [0x4c01332, 0x7401332, 0xac01332, 0x14001332, 0x1e401332, 0x34001332, 0x45401332, 0x4c001332,
    0x2c01372, 0x150000401373, 0x50000001373, 0x8c01372, 0x4001392, 0x2e401372, 0x2bc01392,
    0x2c001392, 0x31c01392, 0x34401372, 0x37c01392, 0x40001392, 0x4c001392, 0x47c01392, 0x44401392,
    0x4d401392, 0x3f80109c00019, 0x4e401392, 0x4cc01392, 0x8ff4, 0x3a4010e400019, 0x2b5011a400019,
    0x41310876c630b0, 0x13cf7, 0x249708cb8630d0, 0x4f4000051, 0x41f010840001a, 0x4d551508463130,
    0x4020109c00019, 0x4f4400051, 0x3ef010ac00019, 0x421010840001a, 0x4040109c00019,
    0x40e010940001a, 0x4f4c00051, 0x680003d1, 0x40f010940001a, 0x31810515063230, 0x3e8010b400019,
    0x13d47, 0x3f3010ac00019, 0x2b6035dc63290, 0x4080109c00019, 0x38ac00071, 0x44217bb8632f0,
    0x2bf011a400019, 0x7b710f9863310, 0x3f6010ac00019, 0x3a4006d1, 0x29800991, 0x2414000b1,
    0x40b0109c00019, 0x13d87, 0x279210984633b0, 0xdb0001d1, 0x3d0d098c4633d0, 0x3ef010b400019,
    0x417010940001a, 0x3fc17d2063430, 0x3f0010b400019, 0x418010940001a, 0x4f6c00051, 0x13db7,
    0x1e690a20c63490, 0x394006f1, 0x4f7000051, 0x2e540d3e8634d0, 0x10d112734634f0, 0x38c000071,
    0x4f7400051, 0x3680112400019, 0x41c010940001a, 0x38c400071, 0x4130109c00019, 0xdb4001d1,
    0x13df7, 0x684003d1, 0x4f8000051, 0x15041716c63610, 0x2c2c00091, 0x402010ac00019, 0x4f8400051,
    0x34a50855c63670, 0x3310115400019, 0x421010940001a, 0x7c902104636b0, 0x404010ac00019,
    0x422010940001a, 0x90a4, 0x18dc00101, 0x423010940001a, 0x5987182ec63730, 0x4f9000051,
    0x2c3400091, 0x3cb010dc00019, 0x2c2309f7c63790, 0x90b4, 0x408010ac00019, 0x41c0109c0001a,
    0x4f9800051, 0x3da17e98637f0, 0x2b5011bc00019, 0x12f400151, 0x2430000b1, 0x5fa91851463850,
    0x2c3c00091, 0x41f0109c00019, 0x4cc00531, 0x4200109c00019, 0x4fa400051, 0x3f6317444638f0,
    0x18e400101, 0x4210109c0001a, 0x404010b400019, 0x1ea4000d1, 0x4230109c00019, 0x2c4400091,
    0x944002b1, 0x4240109c00019, 0x1e5b187d8639d0, 0x3f3010c400019, 0x28130862c63a10,
    0x408010b400019, 0x4260109c0001a, 0x90f4, 0x4270109c00019, 0x50af1587863a90, 0x4fbc00051,
    0x414010ac00019, 0x414010ac0001a, 0x1eac000d1, 0x4fc000051, 0x2d4008d1, 0x2c5000091,
    0x4fc400051, 0x5f400431, 0x104d0d39863b90, 0x448007cf063bb0, 0x3dc010dc00019, 0x2c5400091,
    0x87e0f44063bf0, 0x390000071, 0x39700921463c10, 0x3fc010c400019, 0x6c41740863c50, 0x390400071,
    0x30d0118400019, 0x4fd400051, 0xd40134c00019, 0xdc4001d1, 0x2c5c00091, 0x18f400101,
    0x41d010ac0001a, 0x4fdc00051, 0x414010b400019, 0x130400151, 0x5a000471, 0x1bdb11ffc63d90,
    0x420010ac00019, 0x3f60a0e463dd0, 0x10a1114c063df0, 0x2cd011bc00019, 0x2c6400091,
    0x3ec20a61863e30, 0x404010c400019, 0x422010ac0001a, 0x4fec00051, 0x423010ac00019,
    0x423010ac0001a, 0x2a9304a4063eb0, 0x4ff000051, 0x13fc7, 0x29f011e400019, 0x4ff400051,
    0x408010c400019, 0x426010ac0001a, 0x1e2d0f7f463f70, 0x392000071, 0x427010ac0001a,
    0x2cc3175a063fb0, 0x2c7000091, 0x1ec4000d1, 0x392400071, 0x500000051, 0x96416a7864010,
    0x327e0c6c464030, 0x42a010ac00019, 0x500400051, 0xce8001f1, 0x42b010ac00019, 0x98d0bae464090,
    0x544004c1, 0x422010b40001a, 0x190400101, 0x423010b40001a, 0x2464000b1, 0x393000071,
    0x19221428c64150, 0x3f3010dc00019, 0x501400051, 0x4c3614e18641b0, 0x2640121c00019,
    0x426010b40001a, 0x46390b910641f0, 0x427010b400019, 0x427010b40001a, 0x428010b400019,
    0x428010b40001a, 0x12ac0e2ec64270, 0x429010b400019, 0x393c00071, 0x42a010b400019, 0x502400051,
    0x4d400531, 0x394000071, 0x1ed4000d1, 0x38c00711, 0x3f0010e400019, 0x91c4, 0xbdf0347464370,
    0x42d010b400019, 0xc1e0bc8064390, 0x2c8c00091, 0x3fc010dc00019, 0x5fc00431, 0x131800151,
    0x2474000b1, 0x3f3010e400019, 0x503400051, 0x3a40112400019, 0x1b9f11a2464450, 0x954002b1,
    0x2b5011e400019, 0x422010c00001a, 0x140f7, 0x2c9400091, 0x504000051, 0x1c21120c464510,
    0x395400071, 0x420010c400019, 0x504400051, 0x91f4, 0x1ee0000d1, 0x426010c00001a,
    0x404010dc00019, 0x4f9077c4645d0, 0x504c00051, 0x2480000b1]
  ++ [0x39dd070b864610, 0xcf4001f1, 0x424010c400019, 0x1ee4000d1, 0x2ca000091, 0x505400051,
    0x2484000b1, 0x408010dc00019, 0x42b010c00001a, 0x193709a2c646f0, 0x191c00101, 0x2ca400091,
    0x4a960166064730, 0x428010c400019, 0x42d010c00001a, 0x429010c400019, 0x48400591,
    0x42a010c400019, 0x506400051, 0x42b010c400019, 0x430010c00001a, 0x506800051, 0x397000071,
    0x42c010c40001a, 0x141b7, 0x5d400451, 0x397400071, 0x507000051, 0x16f18c7c648d0, 0x192400101,
    0x274604bd064910, 0xa5801ce864930, 0x408010e400019, 0x2cb400091, 0x4b4a0653864970,
    0x431010c400019, 0x1ef4000d1, 0x414010dc00019, 0x428010cc0001a, 0x2e540a9b0649f0, 0x398000071,
    0x429010cc0001a, 0x40c010e400019, 0x508400051, 0x398400071, 0x2cd011e400019, 0x58400491,
    0xd3915dcc64ab0, 0x31e011a400019, 0x42c010cc0001a, 0x508c00051, 0x419010dc00019,
    0x42d010cc0001a, 0x3c00112400019, 0xde4001d1, 0x1690130400019, 0x509400051, 0x304011bc00019,
    0xae400251, 0x413010e400019, 0x431010cc0001a, 0x98c048b064c30, 0x414010e400019,
    0x432010cc0001a, 0x41f010dc00019, 0x2a21704464c90, 0x399800071, 0x420010dc00019,
    0x29fd0dec464cd0, 0x92a4, 0x193400101, 0x133400151, 0x79c00351, 0x2cd000091, 0x4dc00531,
    0x423010dc00019, 0x58180354464d90, 0x36830a78864db0, 0x424010dc00019, 0x2cd400091, 0x39a400071,
    0x43400601, 0x50b400051, 0x3900115400019, 0x92c4, 0x3c520530464e70, 0x427010dc00019,
    0x427010dc0001a, 0x190e144e064eb0, 0x428010dc00019, 0x3aaf11c5464ed0, 0x2cdc00091, 0x154000131,
    0xaf11680464f10, 0x3db3064ac64f30, 0x39b000071, 0x50c400051, 0x42b010dc00019, 0x204714d2464f90,
    0x39b400071, 0x1d4012bc00019, 0x18a30c39c64fd0, 0x2b790e61c64ff0, 0x194000101, 0x2ce400091,
    0x60331524065030, 0x424010e400019, 0x9ce16ce065050, 0x92f4, 0x3a4006f1, 0x42f010dc00019,
    0x37361820c65090, 0x318011bc00019, 0x430010dc0001a, 0x4cbb14608650f0, 0x39c000071, 0x9304,
    0x50dc00051, 0x14377, 0x39400711, 0x58b50b56865170, 0x50e000051, 0x14387, 0x2e30b894651b0,
    0x2cf000091, 0x50e400051, 0x42b010e400019, 0x435010dc0001a, 0x3dc0112400019, 0x2cf400091,
    0x52200176465270, 0x143b7, 0xdf4001d1, 0x50f000051, 0x143c7, 0xca811544652f0, 0x42f010e400019,
    0x50f400051, 0x9334, 0x41f50195465330, 0x3a40115400019, 0x22c717a9065350, 0x431010e400019,
    0x431010e40001a, 0x628310f98653b0, 0x24d0000b1, 0x9344, 0x510000051, 0x39dc00071,
    0x434010e400019, 0x510400051, 0x24d4000b1, 0x2d0400091, 0x5b917e4c654b0, 0x1340134c00019,
    0x12a112f44654d0, 0x510c00051, 0x195400101, 0x211b147a065510, 0x3e7d07abc65530,
    0x438010e400019, 0x14447, 0x439010e400019, 0x511400051, 0xd14001f1, 0x1f30000d1, 0x39ec00071,
    0x31312f04655f0, 0x2b50121c00019, 0x9e400291, 0x3ec0112400019, 0x40400651, 0x3b10115400019,
    0x1f34000d1, 0x39f400071, 0x330011bc00019, 0x512400051, 0x3ef0112400019, 0x425d0fd4865710,
    0x24e4000b1, 0x3f00112400019, 0x42c010f40001a, 0x512c00051, 0x144b7, 0x135400151, 0x4e400531,
    0x513000051, 0xc1f018cc657d0, 0xe00001d1, 0x49470bfc065810, 0x205710c7865830, 0x37c0118400019,
    0x430010f40001a, 0x3a0400071, 0x2bf0121c00019, 0x431010f40001a, 0x3f60112400019,
    0x432010f40001a, 0x514000051, 0x2d2400091, 0x3f80112400019, 0x514400051, 0x435010f40001a,
    0x4cc1149f0659b0, 0x94013dc00019, 0x1f44000d1, 0x484808848659f0, 0x43c00601, 0x437010f40001a,
    0x3a1400071, 0x3fc0112400019, 0x38e1886065a50, 0x7ac00351, 0x30d011e400019, 0x515400051,
    0x340011bc00019, 0x43a010f40001a, 0x196c00101, 0x43b010f40001a, 0x4000112400019, 0x2d3400091,
    0x311011e400019, 0x8981748865b90, 0x4020112400019, 0x516400051, 0x51fb0893865bf0,
    0x340011c000019, 0x9404, 0x4040112400019, 0xb200c3a865c50, 0x347011bc00019, 0xe7a195d465c90,
    0x2504000b1, 0x348011bc00019, 0x136400151, 0x298009d1, 0x61400431, 0x2d4000091,
    0x36f00fa3065d10, 0x3a3000071, 0x31c00831, 0xe0c001d1, 0x2b50123400019, 0x2d4400091,
    0x517c00051, 0x145f7, 0x43c010fc0001a, 0x518000051, 0x53d708cec65e10, 0x17fb0028465e30,
    0x40c0112400019, 0x518400051, 0x157400131, 0x20f012bc00019, 0x43f010fc0001a, 0x2d4c00091]
  ++ [0x350011bc00019, 0x43400611, 0x3a4000071, 0x42d0110c0001a, 0x3d40115400019, 0x4165145c065f50,
    0x3a4400071, 0x2bd0123400019, 0x519400051, 0x1abe168c065fb0, 0x214012bc00019, 0x2d5400091,
    0x3bdc0a89065ff0, 0x198000101, 0x3ce10b2a866010, 0x9464, 0x4140112400019, 0x4a7d0701066050,
    0xb69123dc66070, 0x4150112400019, 0x14687, 0x358011bc00019, 0x51a400051, 0x9474, 0x198400101,
    0xe14001d1, 0x51a800051, 0x41ee0f82066130, 0x3dc0115400019, 0x4360110c0001a, 0x2520000b1,
    0x9484, 0x3de0115400019, 0xc72166b0661d0, 0x1fa101e9c661f0, 0x158000131, 0x51b400051, 0x146d7,
    0x3d509fd466230, 0x3a40118400019, 0x14b2, 0x4014b2, 0x100004014b3, 0x43b0110c0001a, 0x4c014b2,
    0x74014b2, 0xa4014b2, 0x40014b2, 0x298014b2, 0x40c014b2, 0x3dc014b2, 0x4c0014b2, 0x474014b2,
    0x340014b2, 0x4001512, 0x12401512, 0x1c001512, 0x24c01512, 0x2a401512, 0x24001512, 0x43c01512,
    0x34001512, 0x54001512, 0x4c401512, 0x7401572, 0x4001572, 0x4c001512, 0x13401572, 0x2bc01572,
    0x29801572, 0x34001572, 0x37c01572, 0x40c01572, 0x54001572, 0x55401572, 0x48401572, 0x40015d2,
    0x194015d2, 0x240015d2, 0x20c015d2, 0x264015d2, 0x37c015d2, 0x2ac015d2, 0x2c0015d2, 0x4c0015d2,
    0x7c01612, 0x10c01612, 0x13001612, 0x1c001612, 0x43c01612, 0xb401612, 0x4c001612, 0x54001612,
    0x37401612, 0x44401612, 0x4fc01612, 0x4c401612, 0xc001678, 0x14801678, 0x2bc01678, 0x29401678,
    0x23801678, 0x33c01678, 0x45801678, 0x16801678, 0x53c01678, 0x2f001678, 0x39001678, 0x4bc01678,
    0x4e801678, 0x55801678, 0x2924000b1, 0x52001678, 0x56d20aa5c713b0, 0x59c01678, 0x64016f2,
    0x40016f2, 0x124016f2, 0xd00004016f3, 0x18c016f2, 0x1f4016f2, 0x1c0016f2, 0x240016f2,
    0x5a0016f2, 0x52c016f2, 0x55c016f2, 0x1752, 0xb0000001753, 0xac01752, 0x14001752, 0x2e401752,
    0x40001752, 0x2bc01752, 0x47c01752, 0x4c001752, 0x55c01752, 0x40017b2, 0xc4017b2, 0x108017b8,
    0x17c017b8, 0x2c0017b2, 0x3fc017b8, 0x478017b8, 0x53c017b8, 0x180017f2, 0x5ec017b8, 0x264017f2,
    0x2c0017f2, 0x37c017f2, 0x400017f2, 0x47c017f2, 0x1852, 0xb0000001853, 0x10000001853,
    0x29801852, 0x19c01852, 0x34001852, 0x45401852, 0x45c01852, 0x5a001852, 0x24401852, 0x4dc01852,
    0x55c01852, 0x5f001852, 0x5bc01852, 0x2c018d2, 0x18d2, 0x94018d2, 0x40018d2, 0x100004018d3,
    0x1f4018d2, 0x298018d2, 0x19c01912, 0x18001912, 0x90000001913, 0x130001401913, 0x23c01912,
    0xd0000401913, 0x2f400c1b, 0x24000c1b, 0x30400c1b, 0x63001912, 0x63c01912, 0x57401912,
    0x5f001912, 0x63401912, 0x64001912, 0x10000401993, 0x28c01992, 0x24001992, 0x28401992,
    0x31c01992, 0x54001992, 0x30401992, 0x53c01992, 0x64001992]

def opsA32768 : List Nat :=
  [0x28c01992, 0x24001992, 0x28401992, 0x31c01992, 0x54001992, 0x30401992, 0x53c01992, 0x64001992,
    0x16400c7b, 0x17c00c7b, 0x1e400c7b, 0x13000c7b, 0x29800c7b, 0x30400c7b, 0x2c000c7b, 0x31c00c7b,
    0x2fc00c7b, 0x16a04a14818b0, 0x13000535, 0x55c015a400019, 0x14000535, 0x558015ac00019,
    0x55b015ac00019, 0x52400651, 0x2f34000b1, 0x67dc00051, 0x39b400091, 0xc14002b1, 0x4a3400071,
    0x560015ac00019, 0x15f10eec081df0, 0x561015ac0001a, 0x6565030a481e30, 0x562015ac0001a,
    0x67ec00051, 0x4d6303da481e90, 0x1a52, 0x11ec001d1, 0x401a52, 0xd0000401a53, 0x2c01a52,
    0x5401a52, 0x4001a52, 0x2bc01a52, 0x2f401a52, 0x34001a52, 0x64001a52, 0x5bc01a52, 0x68001a52,
    0x63c01a52, 0x58401a52, 0x5ec01a52, 0x63401a52, 0x4fc01a52, 0x4c01af2, 0x4001af2, 0x1401af2,
    0x10000401af3, 0xc401af2, 0xac01af2, 0x18001af2, 0x2bc01af2, 0x2c001af2, 0x1bc01b12,
    0x54001b12, 0x3e401af2, 0x6b401b12, 0x64001b12, 0x5ec01b12, 0xa401b72, 0x70000401b73,
    0x24001b72, 0x50000001b73, 0x63c01b72, 0x68001b72, 0x6ac01b72, 0x63001b72, 0x29401b72,
    0x4fc01b72, 0x64001b72, 0x59401b72, 0x4c01c12, 0x4001c12, 0xfc01c12, 0x10000401c13, 0x1b401c12,
    0x23401c12, 0x26c01c12, 0x24001c12, 0x6dc01c12, 0x63001c12, 0x68001c12, 0x6ac01c12, 0x4a401c12,
    0x90000401c93, 0x2c01c92, 0x10c01c92, 0x10000401c93, 0x3d401c92, 0x40001c92, 0x22c01c92,
    0x54001c92, 0x5401cf2, 0x8801cf8, 0x2bc01cf8, 0x2c001cf2, 0x33c01cf8, 0x26801cf8, 0x71c01cf2,
    0x72001cf2, 0x65801cf8, 0x67c01cf8, 0x60c01cf2, 0x43801cf8, 0x73c01cf8, 0x6b801cf8, 0x6e401cf2,
    0x4000e3b, 0xac00e3b, 0xdc00e3b, 0x7400e3b, 0xe3b, 0x412800091, 0x2c000e3b, 0x26c00e3b,
    0x2bc00e3b, 0x34000e3b, 0x31c00e3b, 0x32c00e3b, 0x1400e5b, 0x2001df8, 0x8801df8, 0x3c01df8,
    0xf801df8, 0x18400e5b, 0x14001df8, 0x29401df8, 0x4bc01df8, 0x3d801df8, 0x47801df8, 0x59c01df8,
    0x60801df8, 0x22801df8, 0x3401e72, 0x130001401e73, 0x26c01e72, 0x2c001e72, 0x30401e72,
    0x40001e72, 0xdc01eb2, 0x1eb2, 0x18001eb2, 0x78c01e72, 0x53c01eb2, 0x34001eb2, 0x64001eb2,
    0x69401e72, 0x7ac01eb2, 0x78001eb2, 0x3c401eb2, 0x16c01f32, 0x10000401f33, 0x1c001f32,
    0x50000001f33, 0x90000401f33, 0x57401f32, 0x26401f32, 0x7c001f32, 0x6ac01f32, 0x74001f32,
    0x79c01f32, 0x72401f32, 0x7bc01f32, 0x78001f32, 0x20c01fd2, 0x2c001fd2, 0x31c01fd2, 0x34001fd2,
    0x28401fd2, 0x37c01fd2, 0x29801fd2, 0x7c001fd2, 0x53401fd2, 0x5ec01fd2, 0x76c01fd2, 0x77001fd2,
    0x61401fd2, 0x7bc01fd2, 0x79c01fd2, 0x71c01fd2]

def opsA40960 : List Nat :=
  [0x7c001fd2, 0x53401fd2, 0x5ec01fd2, 0x76c01fd2, 0x77001fd2, 0x61401fd2, 0x7bc01fd2, 0x79c01fd2,
    0x71c01fd2, 0xa402092, 0x130000402093, 0xc402092, 0x150000402093, 0xfc02092, 0x18002092,
    0x26c02092, 0x2a402092, 0x1c0020b2, 0x72402092, 0x7c002092, 0x6f4020b2, 0x780020b2, 0x4cc02092,
    0x7fc020b2, 0x40c02112, 0x40002112, 0x6b402112, 0x64002112, 0x82c02112, 0x77002112, 0x78002112,
    0x40101b, 0x3400101b, 0x38c0101b, 0x54021d2, 0x140021d2, 0x18c021d2, 0x1c0021d2, 0x180021d2,
    0x274021d2, 0x2e4021d2, 0x5a0021d2, 0x1f402232, 0x24002232, 0x70000002233, 0x32c02232,
    0xb0000002233, 0x40002232, 0x68002232, 0x6dc02232, 0x6ac02232, 0x7bc02232, 0x86c02232,
    0x5d402232, 0x40022d2, 0x124022d2, 0x1c0022d2, 0x31c022d2, 0x298022d2, 0x284022d2, 0x32c022d2,
    0x680022d2, 0x4e4022d2, 0x8b4022d2, 0x780022d2, 0x850022d2, 0xfc010fb, 0x8c010fb, 0x8c02392,
    0x10000402393, 0x1c002392, 0x2c023b2, 0x28c02392, 0x2c002392, 0xa4023b2, 0x2ac02392,
    0x54002392, 0x86c02392, 0x50000402413, 0x6dc023b2, 0x10000002413, 0xb0000402413, 0x1c002412,
    0x2d40115b, 0x8c002412, 0x43c0115b, 0x8dc02412, 0x8d4023b2, 0x82c02412, 0x90002412, 0x3c402412,
    0x84402412, 0x85002412, 0x67c02412, 0x3a40119b, 0x3dc0119b, 0x4000119b, 0x45c0119b, 0x3400119b,
    0x4440119b, 0x2980119b, 0x44c0119b, 0x78c01e8c00019, 0x926000051, 0x70000402513, 0x2c02512,
    0x6402512, 0x150000402513, 0x18002512, 0x22c02512, 0x2c002512, 0x80c02512, 0x94002512,
    0x10000002593, 0xd0000402593, 0x70000002593, 0x23c02592, 0x2c002592, 0x38c02592, 0x34002592,
    0x700000025f3, 0x2c0025f2, 0xd00000025f3, 0x584025f2, 0x400025f2, 0x47c025f2, 0x180025f2,
    0x640025f2, 0x10000002653, 0x70000002653, 0x40002652, 0x62402652, 0x4c002652, 0x54002652,
    0x96c02652, 0x90000402693, 0x130000002693]

def opsA49152 : List Nat :=
  [0x40002652, 0x62402652, 0x4c002652, 0x54002652, 0x96c02652, 0x90000402693, 0x130000002693,
    0x90002692, 0x82c02692, 0x8ac02692, 0x94002692, 0x88402692, 0x94402692, 0x8c002692, 0x964026b2,
    0x13002772, 0x70000002773, 0x18c02772, 0x1c002772, 0x18002772, 0xdc02772, 0x5402772,
    0x52c02772, 0x5a002772, 0x97c02772, 0x94002772, 0x2f402772, 0x97402772, 0x90002772, 0x4002812,
    0x130000002813, 0x43c02832, 0x40002832, 0x45c02832, 0x24c02812, 0x8c002812, 0x8ec02812,
    0x9a402812, 0xa0002812, 0x500004028d3, 0x1300000028d3, 0x1000004028d3, 0x700004028d3,
    0x164028d2, 0x640028d2, 0x28c028d2, 0x1c02952, 0x50000402953, 0x90000002953, 0x24002952,
    0x50000002953, 0x32c02952, 0x64002952, 0x23402952, 0xa0c02952, 0xa4002952, 0x9c402952,
    0x94002952, 0x71c02952, 0x36402952, 0xd0000002a13, 0x2c002a12, 0x26c02a12, 0x54002a12,
    0x10c02a52, 0x5ec02a12, 0x14002a52, 0x1bc02a52, 0x26c02a52, 0x5a002a52, 0x6dc02a52, 0x12002ab8,
    0x4bc02ab8, 0x56002ab8, 0x59c02ab8, 0x60802ab8, 0x53c02ab8, 0x31c02ab2, 0x50000002b33,
    0x10000402b33, 0x24002b32, 0xb0000002b33, 0x70000402b33, 0x18c02b32, 0x1c402b32, 0xac002b32,
    0xa3c02b32, 0x3402bd2, 0x4002bd2, 0x70000002bd3, 0x150000402bd3, 0x31c02b32, 0xdc02c52,
    0x13002c52, 0x100000402c53, 0xd0000402c53, 0xa3c02bd2, 0x50000402c53, 0x34002bd2, 0x2140157b,
    0xac002c52, 0x9fc02c52, 0xaac02c52, 0xa8002c52, 0x1c00157b, 0x10002cf8, 0x33c02cf8, 0x11802cf8,
    0x71002cf8, 0x29402cf8]

def opsA57344 : List Nat :=
  [0xac002c52, 0x9fc02c52, 0xaac02c52, 0xa8002c52, 0x10002cf8, 0x33c02cf8, 0x11802cf8, 0x71002cf8,
    0x29402cf8, 0x402d72, 0x13002d72, 0x2c002d72, 0x2bc02d72, 0x25402d72, 0x4c002d72, 0x94c02d72,
    0xb4002d72, 0xa7402d72, 0xb5c02d72, 0x24002dd2, 0xa8002d72, 0x7fe230fbce4fb0, 0x90002dd2,
    0x50000002e33, 0x70000002e33, 0x40002e32, 0x4cc02dd2, 0x30402e32, 0xb7402dd2, 0x5f002e32,
    0x79c02e32, 0xb4002e32, 0x45402e32, 0x1c02ef2, 0xd0001402ef3, 0x50000002ef3, 0x13002ef2,
    0x2fc02ef2, 0x10000002ef3, 0x78002ef2, 0xbac02ef2, 0x25c02ef2, 0xb4002ef2, 0x70000002f93,
    0x18002f92, 0x1c402f92, 0xb0000402f93, 0x5cc02f92, 0xa4002f92, 0x17c03012, 0x1c003012,
    0x9a402f92, 0xbbc02f92, 0x50000403013, 0x50000003013, 0x10000403053, 0x1c0175b, 0x340175b,
    0x1300175b, 0xbb403012, 0xb3003012, 0x94003012, 0x1d40175b, 0x94c03012, 0xb3003052, 0x5940175b,
    0xbdc03052, 0xbec03052, 0xc0c03052, 0x3132, 0xd0000003133, 0x1bc03132, 0x29803132, 0x64c03132,
    0x24403132, 0x68003132, 0x31d3, 0x700000031d3, 0xd00000031d3, 0x340031d2, 0x454031d2,
    0x298031d2, 0x2f4017fb, 0x28c031d2, 0x3293, 0x2c03292, 0x100000403293, 0xd0000403293,
    0xa74031d2, 0x150001c03293, 0x100000003293, 0xb7c03292, 0x94003292, 0x900000032b3, 0xb3003292,
    0xa7403292, 0x5a00185b, 0x3353, 0x130000003353, 0x150000403353, 0xc8c03292, 0x3c033d8,
    0x90033d8, 0x79403352]

def opsA65536 : List Nat :=
  [0x3353, 0x130000003353, 0x150000403353, 0x3c033d8, 0x8c018db, 0x188033d8, 0x90033d8, 0x79403352,
    0xcac03352, 0xc8403352, 0xb3003352, 0xc4003352, 0x850033d2, 0x8ec033d2, 0x940033d2, 0xdc03492,
    0x978033d8, 0x84c033d8, 0x8fc033d8, 0x13003492, 0xce4033d8, 0xce0033d8, 0x82c03492, 0x85003492,
    0x97c03492, 0x28403492, 0xab003492, 0xafc03492, 0xb0403492, 0xcf803492, 0x90000003553,
    0x68003552, 0x2c03552, 0x7d403552, 0x85003552, 0xb8c03552, 0xa8003552, 0x208035f8, 0x2bc035f8,
    0x590035f8, 0xccc03592, 0x53c035f8, 0xd1003592, 0x638035f8, 0x9f8035f8, 0x18c036d2,
    0x500004036d3, 0x124036d2, 0x1300004036d3, 0x1c0036d2, 0x274036d2, 0x26c036d2, 0x2c003712,
    0xafc036d2, 0xd98036d2, 0xd04036d2, 0xdb0036d2, 0x5cc036d2, 0xb54036d2, 0xdac036d2, 0xdb4036d2,
    0xdc003712, 0xa9403712, 0xc8c03712, 0xd9803712, 0xac01afb, 0x14401afb, 0x1c001afb, 0x26c01afb,
    0x34001afb, 0x45c01afb, 0x5a001afb, 0x24401b1b, 0x38c01afb, 0x34001b1b, 0x4cc01b1b, 0x62401afb,
    0x5f001b1b, 0x64c01b1b, 0x6ac01b1b, 0x40038f2, 0xac038f2, 0x100004038f3, 0x114038f2,
    0x17c038f2, 0x400038f2, 0x7f4038f2, 0x23c038f2, 0xd80038f2, 0xcac038f2, 0xcf8038f2, 0xdac038f2,
    0xc34038f2, 0xab0038f2, 0x7c03a12, 0x40003a12, 0x1d403a12, 0x47c03a12]

def opsA73728 : List Nat :=
  [0xd80038f2, 0xdac038f2, 0x7c03a12, 0x40003a12, 0x1d403a12, 0x47c03a12, 0x5a003a12, 0x5dc03a12,
    0x5f003a12, 0x6dc03a12, 0x85003a12, 0x88c03a12, 0xe6c03a12, 0xd9803a12, 0xe0003a12, 0x31c03a92,
    0x9b403a12, 0x100000403ad3, 0x7c003a92, 0xd3c03a92, 0xd9803a92, 0x76403a92, 0x90000003b93,
    0xb0000403b93, 0xd0001403b93, 0x100002c03b93, 0xc1403a92, 0xdac03b92, 0x85003b92, 0x11c01cdb,
    0xb4003b92, 0x1b401cdb, 0xce803b92, 0xe6c03b92, 0x130000403c73, 0x13403c72, 0x100001c03c73,
    0x72003c72, 0x7ac03c72, 0xafc03c72, 0xab003c72, 0xc4003c72, 0xd9c03c72, 0x10000003cb3,
    0x130000003d13, 0xd9803c72, 0xa8003cb2, 0xec403c72, 0xf0003cb2, 0xf1c03c72, 0xe8c03cb2,
    0xd9803cb2, 0xd0000003df3, 0xd803df8, 0x29403df8, 0x18003df8, 0x56003df8, 0x59c03df8,
    0x5f003df8, 0x53c03df8, 0x5d003df8, 0x70000003e53, 0xd4003df2, 0xeec03df2, 0xf4003df2,
    0xf1c03df2, 0xb0000003f13, 0x70000403f13, 0xd0000403f13, 0x100000403f13, 0x68003f12,
    0x70000003f53, 0xa9c03f12, 0xb3003f12, 0x10000003f53, 0xcf803f12, 0xf6c03f12, 0x90000003fd3,
    0xd0001403fd3, 0x68001ebb, 0x75401ebb, 0x130000404073, 0x130000004073, 0x10000004073,
    0xd0000404073, 0xb0000004073]

def opsA81920 : List Nat :=
  [0x68001ebb, 0x75401ebb, 0x130000404073, 0x130000004073, 0x10000004073, 0xd0000404073,
    0xb0000004073, 0x4d8040f8, 0x62c040f8, 0x120040f8, 0x63c040f8, 0x5c8040f8, 0x73c040f8,
    0x6a8040f8, 0x77c040f8, 0x850040f8, 0x67c040f8, 0xccc040f2, 0xd98040f2, 0xcf4040f8, 0xe00040f2,
    0x102c040f2, 0x1000040f2, 0x1028040f8, 0xf74040f2, 0x14401fdb, 0x4253, 0xd9c04192,
    0x10000404253, 0x10000004253, 0x150000004253, 0xf7c04192, 0x1040041b2, 0xb0000004273,
    0x1044041b2, 0x1058041b2, 0x82c04252, 0x85004252, 0x1054041b2, 0x105804252, 0x64404252,
    0xf4c04252, 0xf7004252, 0x8a404252, 0xad404252, 0x109404252, 0x100004043f3, 0x500000043f3,
    0x4c043f2, 0x40043f2, 0x1b4043f2, 0x180043f2, 0x94043f2, 0x298043f2, 0xccc043f2, 0xd0000404433,
    0x900043f2, 0x90000004433, 0x48044f8, 0x3c044f8, 0x63c043f2, 0x160044f8, 0x13c044f8,
    0x3fc044f8, 0x478044f8, 0x62c044f8, 0x4a40211b, 0x108044f8, 0xb0000404553, 0xb0000004553,
    0x105804492, 0x93c044f8, 0xb50044f8, 0x3d404552, 0x45d3, 0xd00000045d3, 0xc5c04552, 0xfc004552,
    0xd9804552, 0x14c021db, 0x70000404633, 0x214021db, 0x240021db, 0x2ac021db, 0x4c0021db,
    0x71c021db, 0x4693, 0x100001c04693, 0x130000004693, 0x1140045d2, 0x1084045d2, 0x116c045d2,
    0x1058045d2, 0x114004632]

def opsA90112 : List Nat :=
  [0x71c021db, 0x4693, 0x100001c04693, 0x130000004693, 0x1140045d2, 0x1084045d2, 0x116c045d2,
    0x1058045d2, 0x19c0223b, 0x114004632, 0x2740223b, 0x3400223b, 0x3840223b, 0x4000223b,
    0x25c0223b, 0x3c047f8, 0x70047f8, 0x100000047f3, 0xd8047f8, 0x12c047f8, 0x188047f8, 0x294047f8,
    0x780047f2, 0x26c022db, 0x2d4022db, 0xd80047f2, 0xcdc047f2, 0xcbc047f2, 0xd98047f2,
    0x10000004933, 0xd0000404933, 0x100001c04933, 0x130000404933, 0x50000004933, 0xce804932,
    0x72404932, 0x100000049d3, 0xd00004049d3, 0x100001c049d3, 0x900004049d3, 0x2a40239b,
    0xf1c04932, 0x8c00239b, 0x8740239b, 0x8bc0239b, 0x240023bb, 0x400023bb, 0x4a40239b, 0x844049d2,
    0xd0000404b13, 0x100002c04b13, 0x190000004b13, 0x90000404b13, 0xd0001404b13, 0x70000404b13,
    0x50000004b13, 0x150001c04bd3, 0x190000004bd3, 0x1f0000004bd3, 0x150000404bd3, 0x5f004b12,
    0x130000004bd3, 0x126404b12, 0x10000404c13, 0xd0000004c13, 0x70000404c13, 0x70000004c13,
    0x100000004c13, 0x14804cf8, 0x17c04cf8, 0xc004cf8, 0x1bc04cf8, 0xf4c04bd2, 0x18004cf8,
    0x150000004cd3, 0x55804cf8, 0x59c04cf8, 0xbdc04cd2, 0xcf804cd2, 0x190000004d53, 0xda404cd2,
    0xdb004cd2]

def opsA98304 : List Nat :=
  [0x14804cf8, 0x17c04cf8, 0xc004cf8, 0x1bc04cf8, 0x18004cf8, 0x150000004cd3, 0x55804cf8,
    0x59c04cf8, 0xbdc04cd2, 0xcf804cd2, 0x190000004d53, 0xda404cd2, 0xdb004cd2, 0x4e13,
    0x100001c04e13, 0x50000004e13, 0x10000404e13, 0x190000004e13, 0x7200259b, 0x4d40259b,
    0x9440259b, 0x55c0259b, 0x9000259b, 0x4c00259b, 0x9400259b, 0x5d404e12, 0x94004e12, 0x54025fb,
    0x2c0025fb, 0x28c025fb, 0x120004e12, 0x115c04e12, 0x45c025fb, 0x47c025fb, 0x53c025fb,
    0x7fc025fb, 0x900025fb, 0x50000004fd3, 0x9004ff8, 0xd404ff2, 0x5a004fd2, 0x3fc04ff8,
    0x48404ff2, 0x39804ff8, 0xa8004fd2, 0xadc04fd2, 0xd0000405093, 0x50000005093, 0x70000005093,
    0x7c0026bb, 0x934026bb, 0x128004fd2, 0x105404ff8, 0x131804fd2, 0x13cc04fd2, 0x10000405113,
    0x10000005113, 0xb0000405113, 0x89c05092, 0xa6405092, 0xf0005092, 0xb2c05092, 0x137c05092,
    0x130005092, 0x90000005153, 0x131805092, 0x114405092, 0x139405092, 0x26c0277b, 0x3400277b,
    0x3c40277b, 0x10000405293, 0x50000005293, 0x70000405293, 0x130000005293, 0x50000405293,
    0x440052f8, 0x76c052f8, 0x648052f8, 0x294052f8, 0x2bc052f8, 0x48052f8, 0x3400283b, 0x2340281b,
    0x6e0052f8, 0xb3c052f8, 0xba8052f8, 0x9d40281b, 0xa000281b, 0xcf4052f8, 0x9b40281b, 0xc60052f8,
    0x103c052f8, 0x12fc052f8, 0x1224052f8, 0x13d0052f8, 0x14bc052f8, 0x14b0052f8]

def opsA106496 : List Nat :=
  [0x76c052f8, 0x648052f8, 0x3400283b, 0x2340281b, 0x6e0052f8, 0xb3c052f8, 0xba8052f8, 0x9d40281b,
    0xa000281b, 0xcf4052f8, 0x9b40281b, 0xc60052f8, 0xa000283b, 0x103c052f8, 0x12fc052f8,
    0x9000283b, 0x1224052f8, 0x9dc0283b, 0x8c00283b, 0x2c0010d5, 0x13d0052f8, 0x14bc052f8,
    0x14b0052f8, 0x8c010f5, 0x384010d5, 0x364010d5, 0xdc010f5, 0xf100004010d6, 0x130010f5,
    0x344010d5, 0x3a4010d5, 0x2d0001c010f6, 0x4500004010f6, 0xf900004010d6, 0x50000405513,
    0x405512]

def stageA4 : List (Nat × List Nat) :=
  [(8192, opsA24576), (8192, opsA32768), (8192, opsA40960), (8192, opsA49152), (8192, opsA57344),
    (8192, opsA65536), (8192, opsA73728), (8192, opsA81920), (8192, opsA90112), (8192, opsA98304),
    (1105, opsA106496)]

def opsB107601 : List Nat :=
  [0x14405512, 0x13005512, 0x14c05512, 0x14005512, 0x16c05512, 0x18005512, 0x26c05512, 0x40005512,
    0x45405512, 0x4c005512, 0x5ec05512, 0x740055d2, 0x82c055d2, 0x152405512, 0xa00055d2,
    0x11c05652, 0x14005652, 0x20c05652, 0xe8c055d2, 0xf00055d2, 0xa2c05652, 0x131805652,
    0x13b405652, 0x14405772, 0x34005772, 0x45405772, 0x40005772, 0x52c05772, 0x54005772,
    0x5dc05772, 0x72005772, 0xafc05772, 0x11c005772, 0xe7405812, 0xf0005812, 0xf4405812,
    0x103005812, 0x10c058f2, 0x180058f2, 0x1c4058f2, 0x7c005992, 0x91405992, 0x1540058f2,
    0xf4c05952, 0xb9405992, 0x108005952, 0x10fc05992, 0x144005992, 0x94405ab2, 0xa8005ab2,
    0x94005ad2, 0x96405ad2, 0xa2c05ad2, 0x40005b32, 0xe3405ad2, 0x94005bf2, 0xa0c05bf2,
    0x166405b32, 0xa8005bf2, 0xaac05bf2, 0xa0005bf2, 0x5c92, 0x2c05c92, 0x66405d52, 0x63005d52,
    0x55c05d52, 0x130005cb2, 0xbdc05d12, 0x72405d52, 0xd9805d12, 0x94405d52, 0x9fc05d52,
    0x78005e72, 0x7bc05e72, 0x65c05e72, 0x7c005e72, 0x8f405e72, 0xa4005e72, 0xb2c05e72, 0xb3005e72,
    0xbec05e72, 0xfc005e72, 0x45c05fb2, 0x63005fb2, 0x80405fb2, 0x86c05fb2, 0x8c005fb2, 0xa7c05fb2,
    0xc9405fb2, 0xd9805fb2, 0x13cc05fb2, 0x2c0060d2, 0xb0c060d2, 0xb40060d2, 0x70c06112,
    0xce8060d2, 0xa7c06112, 0xf8006112, 0x10a406112, 0x1e406232, 0x70c061f2, 0x740061f2,
    0xf40061f2, 0x70c062b2, 0x131806232, 0xf6c062b2, 0x1094062b2, 0x10c0062b2, 0x143c062b2,
    0x5a0063d2, 0x16c06412, 0x6472, 0x8c406412, 0x52c06492, 0xf0006412, 0x334064d2, 0x10c006472,
    0x110c064d2, 0x189806492, 0x7fc065b2, 0xf7006552, 0x940065b2, 0xbbc065b2, 0xe44065b2,
    0x128006652, 0x154406652, 0x15c006652, 0x163c06652, 0x16c006652, 0x16dc06652, 0x175806652,
    0x1bc06792, 0x77406852, 0x80c06852, 0x90006852, 0x175806792, 0x9e406852, 0x9fc06852,
    0xa4006852, 0xb5c06852, 0xcf406852, 0xd8006852, 0x7c06a12, 0x5a0069d2, 0x70c069d2, 0x740069d2,
    0x3dc06a12, 0x47406a12, 0xa9c069d2, 0xac0069d2, 0xa3c06a12, 0x1440069d2, 0xcbc06ad2,
    0xd9806ad2, 0xf7006ad2, 0x19406b92, 0x38406bb2, 0x68006bb2, 0x2a406c52, 0xab006c52, 0x2d406cd2,
    0x29806cd2, 0x2f406cd2, 0x118006c52, 0x10406d32, 0x5dc06d32, 0x1a0006c52, 0x7e406df2,
    0x174006d32, 0x134006d92, 0xd0406df2, 0xee406df2, 0x108006df2, 0x1a0406d92, 0x152406df2,
    0x14006f12, 0x45406f12, 0xa4006f72, 0x76c06fd2, 0x78006fd2, 0x11f406f72, 0xbe406fd2,
    0x154406f72, 0x68007092, 0x18c07132, 0x34007132, 0x3c407132, 0x63007132, 0xd3c07132,
    0x148407132, 0x175807132, 0x17c007132, 0xa7c07272, 0xab007272, 0xe0407272, 0x105807272,
    0x196c07272, 0x19b407272, 0x1c8007272, 0x1c8c07272, 0x7c007452, 0xa7407452, 0x340074b2,
    0xc1407452, 0x3dc07512, 0x4007572, 0x2bc07572, 0x94007552, 0xc1407572, 0x128007572, 0x73407612,
    0xb3007612, 0xdec07612, 0x630076d2, 0x2c07792, 0x11c0076d2, 0x67c07792, 0x79407792,
    0x1758076d2, 0x1c4c076d2, 0x40078d2, 0xce4078d2, 0x1000078b2, 0x10a4078b2, 0xe00078d2,
    0xee4078d2, 0x1080078d2, 0x20c079d2, 0xe00079d2, 0x15d4079f2, 0x1640079f2, 0x16fc079f2,
    0x1980079d2, 0x1834079f2, 0x18f0079f2, 0x1d407c92, 0x18007c92, 0x94007c32, 0xa7407c32,
    0xab007c32, 0x38407c92, 0x34007c92, 0x3ec07c92, 0x4cc07e12, 0x4c007e12, 0xc4007db2, 0xc8407db2,
    0x52407e12, 0x54007e12, 0x66407e12, 0xf8007db2, 0x96c07e12, 0x154007ed2, 0x162407ed2,
    0x172c07ed2, 0x184007ed2]
  ++ [0x189807ed2, 0x1a2c07ed2, 0x1a4007ed2, 0x48408152, 0x65c08152, 0x68008152, 0x72008152,
    0x1b3c08052, 0x1c8808052, 0x1eac08052, 0xb4008152, 0x66408212, 0x18ec08212, 0x105808292,
    0x1a3008212, 0x12e408292, 0x131808292, 0x139c08292, 0x140008292, 0x14e408292, 0x8532,
    0xa408532, 0x16d408412, 0x34008512, 0x42408512, 0x1a80083f2, 0x52c08512, 0x1d40083f2,
    0x2ac085f2, 0x72008692, 0x80408692, 0x8dc08692, 0x1400085f2, 0x4008712, 0xfc08712, 0x24008712,
    0xee408712, 0xa0008832, 0xae408832, 0x218408712, 0x21b008712, 0xdf408832, 0x118008832,
    0x124c08832, 0x34008a52, 0x54408a52, 0x5dc08a52, 0x1280089b2, 0x71408a52, 0x7bc08a52,
    0xa4008a52, 0xafc08bd2, 0xb4008bd2, 0x1e1808ad2, 0xc3408bd2, 0xe0c08bd2, 0xee408bd2,
    0xfc008bd2, 0x14408cb2, 0x90008cb2, 0x7fc08dd2, 0xa4008dd2, 0x5a408e12, 0x21b008cb2,
    0x89c08e12, 0x90008e12, 0x11408ef2, 0x1f408f52, 0x184008ef2, 0x115c08f52, 0xd1008f92,
    0x10c09052, 0x4009072, 0x79c09072, 0x15c009052, 0x714091d2, 0x7ac091d2, 0x23c009072,
    0xa40091d2, 0x34c09252, 0x55409252, 0x1080092b2, 0x112409352, 0x1898092f2, 0x2c09432,
    0x1b40092f2, 0x30409432, 0x77009492, 0x634094d2, 0x114009552, 0xcac09592, 0xcf809592,
    0xd3c09592, 0xe0409592, 0xf0009592, 0xfbc09592, 0x780096b2, 0x15e409712, 0x15dc09712,
    0x16c009712, 0x17bc09712, 0x1f70096b2, 0x18a409712, 0x1c009852, 0x39c09852, 0x9a32,
    0x205c09892, 0xfc09a32, 0x29809a32, 0x31c09a32, 0x34009a32, 0x71409a32, 0xb4009ad2,
    0x1d6409ad2, 0x21b809a92, 0x1d5c09ad2, 0x1df009ad2, 0x202409ad2, 0x18009c72, 0x3a409c72,
    0x24009e32, 0x32c09e32, 0x104009d92, 0x6ac09e32, 0x26f409c72, 0x8c009e32, 0xdc09eb2,
    0x17c009d92, 0x65409eb2, 0x1a0009f52, 0x107c09fd2, 0x124409fd2, 0x1c8809f52, 0x12e409fd2,
    0x1a4009f72, 0x150409fd2, 0x1ef009fd2, 0xe0c0a212, 0xd980a212, 0x10580a1f2, 0xf640a212,
    0x10c00a212, 0x120c0a212, 0x12740a212, 0x12400a212, 0x64c0a492, 0x6800a492, 0x71c0a492,
    0x8500a492, 0x9b40a492, 0x9ac0a492, 0x18980a3d2, 0x1ee00a392, 0xda40a492, 0x10800a492,
    0x12c40a632, 0x4000a6f2, 0x15400a612, 0x6840a6f2, 0xf40a752, 0x26400a572, 0x5840a752,
    0x400a812, 0x3d40a932, 0x400a972, 0x58c0a932, 0x17400a852, 0x1f40a972, 0x8c00a932, 0x5f40ab52,
    0x12400aab2, 0x6800ab52, 0x73c0ab52, 0x8740ab52, 0x94c0ab52, 0x15c00aab2, 0x4000abd2,
    0x4440abd2, 0x14000acf2, 0x14440acf2, 0xa400ad92, 0xb5c0ad92, 0xcf40ad92, 0xcf80ad92,
    0xd540ad92, 0xfbc0ad92, 0x1c00ae52, 0x18740af32, 0x18400af32, 0x18980af32, 0x1b440af12,
    0x19ac0af32, 0x1a400af32, 0x1d640af32, 0x1a800b152, 0xa2c0b232, 0xa400b232, 0x37c0b292,
    0x4340b292, 0x4c00b292, 0xfc0b2d2, 0x1800b2d2, 0x45c0b2d2, 0x2bc00b2d2, 0x40b512, 0x2c4c0b2d2,
    0x2bd80b2d2, 0x1c40b512, 0x2400b512, 0x63c0b512, 0x2c500b512, 0x1e7c0b5d2, 0x1f3c0b5d2,
    0x15fc0b652, 0x1f800b5d2, 0x16b40b652, 0x21000b5d2, 0x23980b5d2, 0x260c0b5d2, 0x1e40b892,
    0x2400b9b2, 0x5140b992, 0x5400b992, 0x5840b992, 0x7f40b992, 0x5940b9b2, 0x6300b9b2,
    0x1db00b8d2, 0x2e040b892, 0x2980bc32, 0x2e1c0b892, 0x2d900b9b2]

def stageB0 : List (Nat × List Nat) :=
  [(131072, opsB107601)]

def opsB238673 : List Nat :=
  [0xc8c0bc32, 0x18400bb92, 0xc940bc32, 0xc400bc32, 0xccc0bc32, 0xd100bc32, 0xd940bc32, 0xe640bc32,
    0x10c00bc32, 0x139c0bc32, 0xd400be92, 0xdc40be92, 0x187c0be12, 0x18c00be12, 0x10580be92,
    0x1b8c0be12, 0x20800bdd2, 0x6940bf52, 0x400bfb2, 0xfdc0c112, 0x2f800be92, 0x11140c112,
    0x1e240c072, 0x20c00c072, 0x15c00c112, 0x24b40c072, 0x27000c072, 0x6240c412, 0x9fc0c412,
    0xac00c412, 0x1ff00c312, 0xc840c412, 0xd100c412, 0x23980c312, 0x18ec0c412, 0x1c0c732,
    0x1df00c5b2, 0x8500c6d2, 0xd40c732, 0x16c0c732, 0xa400c6d2, 0xa540c772, 0x26000c612,
    0x86c0c952, 0x9540c952, 0x31500c732, 0x2f400c772, 0x2d40c9d2, 0xdc00c9d2, 0x1d9c0c952,
    0x7800cb32, 0x14c0cc72, 0x2c00cc72, 0x3240cc72, 0x45c0cc72, 0x5400cc72, 0x1e180cbb2,
    0x143c0cc72, 0x28c0cf12, 0xa2c0ceb2, 0xb300ceb2, 0x4c00cf12, 0x58c0cf12, 0x11800ceb2,
    0x13b40cf12, 0x25700d012, 0x14740d0f2, 0x14cc0d0f2, 0x24300d032, 0x400d212, 0xafc0d212,
    0x2980d2b2, 0x4e40d2d2, 0xf000d3f2, 0x10540d3f2, 0x18000d3d2, 0x16b40d3f2, 0x6340d552,
    0x96c0d552, 0xa140d552, 0x25c00d3f2, 0xb300d552, 0x1340d872, 0x13180d792, 0x4540d852,
    0x9400d812, 0x47c0d852, 0x25c0d872, 0x5a00d852, 0x6640d872, 0x15800da32, 0x15dc0da32,
    0x31100d8d2, 0xc540dab2, 0xf400dab2, 0x1c40db72, 0x20c0db72, 0x1d400da32, 0x76c0ddb2,
    0x18c00dcd2, 0x7800ddb2, 0x35e40db72, 0x22c00dc92, 0x20c0de52, 0x7800de72, 0x6040e092,
    0x23500df32, 0x15540dff2, 0x9a40e092, 0xb300e092, 0xd340e092, 0x1a800dff2, 0xfbc0e092,
    0xd100e352, 0x7cc0e3b2, 0x34800e172, 0x8940e3b2, 0x9400e3b2, 0x11540e352, 0x2ad00e212,
    0xc840e3b2, 0x7200e6b2, 0x7640e6b2, 0x540e712, 0x19000e5d2, 0x10c0e712, 0x1800e712, 0x1c40e712,
    0x26c0e712, 0x4440e712, 0x5f00e9b2, 0x7440e9b2, 0xf000e952, 0xf440e952, 0x7f40e9b2, 0x9400e9b2,
    0x9e40e9b2, 0x1d400eb92, 0x240ed12, 0x1c0ed12, 0x286c0eb12, 0x3a400e9b2, 0x2400ed12,
    0x2e40ed12, 0x3400ed12, 0xccc0ed12, 0x1800ef92, 0xa7c0ef92, 0x36780ed52, 0xccc0ef92,
    0x1bc00eed2, 0xd840ef92, 0x4240f072, 0xcf80f292, 0x39c0f312, 0xd800f292, 0x3e40f312,
    0xdc00f292, 0x44c0f312, 0xcc40f5b2, 0xc400f5b2, 0xf400f592, 0xf840f592, 0xd440f5b2, 0xd800f5b2,
    0xe1c0f5b2, 0xac0f672, 0x1400f672, 0x32c0f952, 0x3c000f672, 0x3940f952, 0x3400f952, 0x6040f952,
    0x6300f952, 0x6bc0f952, 0x22000f7f2, 0x15c00fbb2, 0x15cc0fbb2, 0x1d400fb52, 0x1d840fb52,
    0x16440fbb2, 0x1df00fb52, 0x18740fbb2, 0x18dc0fbb2, 0xac00fd32, 0x1ca40fe92, 0x4000ffd2,
    0x37f00fd32, 0x5ec0ffd2, 0x6540ffd2, 0x7400ffd2, 0xacc0ffd2, 0x184010212, 0x14ac10252,
    0x3040100f2, 0x152410252, 0x160410252, 0x164010252, 0x10410392, 0x2c010392, 0x18c10692,
    0x1c010692, 0x3570103f2, 0x2ac10692, 0x224c10512, 0x79410692, 0x260010512, 0xf4010932,
    0x4ec109d2, 0x122810932, 0x624109d2, 0x680109d2, 0x88c109d2, 0x974109d2, 0x10a52, 0x18dc10c12,
    0x11c010c92, 0x331010af2, 0x351410af2, 0x15c410c92, 0x15c010c92, 0x16fc10c92, 0x37e010af2,
    0x191410c92, 0x770110b2, 0x7ac110b2, 0xf7011052, 0x8a4110b2, 0x10c411052, 0xa80110b2,
    0xb54110b2, 0x4c011452, 0x35c11472, 0x2b1011272, 0x42411472, 0x74011452, 0x55c11472,
    0x5a011472, 0x77411472, 0x11832, 0x27411812, 0x24011812, 0x6411832, 0x44411812, 0x1c011832,
    0x4c011812, 0x3a411832, 0x63011812, 0x70411812, 0x1bc011a72, 0x1c4411a72, 0x1ef011a52,
    0x1e2c11a72, 0x3e40118d2, 0x1ee411a72, 0x266011a12]
  ++ [0x1f7c11a72, 0xa8011ef2, 0xb9411ef2, 0x4c011f52, 0x57411f52, 0x5cc11f52, 0xe0011ef2,
    0x72411f52, 0x78011f52, 0x1b411fb2, 0x128011ef2, 0x47bc11ef2, 0x475811ef2, 0x477411ef2,
    0x128012292, 0x479011ef2]

def opsB369745 : List Nat :=
  [0x90412412, 0x1c2012312, 0x156412372, 0x154012372, 0x158412372, 0x9b412412, 0x277012292,
    0xb0412412, 0x19c012372, 0x86c127d2, 0xd8012792, 0x8c4127d2, 0x154012732, 0xa34127d2,
    0x194012712, 0xf8012792, 0x112c12792, 0x90012b92, 0xa2412b92, 0x3e30128f2, 0xfc12c12,
    0x14012c12, 0x2f412c12, 0x128012b52, 0x58c12c12, 0x128012b92, 0x31c12fd2, 0x4a9012af2,
    0x29f012df2, 0x4c412fd2, 0x2bf012df2, 0x7d412fd2, 0x8a412fd2, 0x404012d12, 0x15fc132d2,
    0x2fd013192, 0x1f7013272, 0x18f4132d2, 0x217413272, 0x218013272, 0x1a64132d2, 0x1ad4132d2,
    0x54013492, 0x654137b2, 0x630137b2, 0x1413812, 0x347013572, 0x16413812, 0x13013812, 0x964137b2,
    0x68013bb2, 0x76c13bb2, 0x4d8013812, 0x85413bb2, 0x85013bb2, 0x89413bb2, 0x4013c32, 0x20c13c32,
    0xac013f92, 0x38c13ff2, 0x128013f32, 0x3e413ff2, 0x4c413ff2, 0x54013ff2, 0x124c13ff2,
    0x1840142f2, 0x143c14332, 0x2ad014212, 0xb24143b2, 0xac0143b2, 0xcdc143b2, 0x4c014452,
    0x142c14752, 0x4580144d2, 0x189814712, 0x1bb4146f2, 0x164414752, 0x1b4014712, 0x1bac14712,
    0x1df0146f2, 0xf4014bd2, 0xf3414bd2, 0xf4c14bd2, 0x314814a12, 0xf9c14bd2, 0x175814b72,
    0x102c14bd2, 0x108414bd2, 0x24014cb2, 0xa0415052, 0x455014d52, 0x345414e32, 0x52c014bd2,
    0x46f014d52, 0x318414e72, 0x333014e72, 0x2415112, 0xac15112, 0xb3015492, 0xd5415492,
    0x240015372, 0xf2415492, 0xfc415492, 0x107c15492, 0x10c015492, 0x12e415492, 0x1ff0157f2,
    0x3c415972, 0x2570157d2, 0xdc159b2, 0x130159b2, 0x26c159b2, 0x2a4159b2, 0x850159b2,
    0x1a1415cd2, 0x240015c52, 0xe0015d72, 0x1b4c15cd2, 0x1c2015cd2, 0xfd415d72, 0xfdc15d72,
    0x1280161b2, 0x6e416252, 0x15c016192, 0x71c16252, 0x72416252, 0x7c016252, 0x82c16252,
    0x84416252, 0x1540161b2, 0x1a34161b2, 0x7c0166d2, 0x58c166f2, 0x5f0166f2, 0x8a4166d2,
    0x8ec166d2, 0x740166f2, 0xa416752, 0xce8166f2, 0xa416bd2, 0x347016932, 0x11c16bd2, 0x1c016bd2,
    0x26c16bd2, 0xc9416b52, 0xe6c16b52, 0x16c32, 0xa416c32, 0xd8016bd2, 0x5417092, 0x4b4016cf2,
    0x5bc17092, 0x19c016f92, 0x65c17092, 0xaf417092, 0xb3017092, 0x1c8817412, 0x1d0c17412,
    0x1db017412, 0x1e4417412, 0x220017412, 0x8c175d2, 0x298175d2, 0x784175d2, 0xfc0179b2,
    0x3c417a52, 0x20c0178d2, 0x58c17a52, 0x1a3017952, 0x1494179b2, 0x1740179b2, 0xc417f52,
    0x11c17f52, 0x1c017f52, 0x368017cb2, 0x69417f32, 0x134017e92, 0x73c17f52, 0x21b817e12,
    0x15f417f52, 0x134018372, 0x4cc18432, 0x3410181d2, 0x74418432, 0x85018432, 0x11418492,
    0x1e418492, 0x608018352, 0x60cc18372, 0x608418372, 0x60c018372]

def opsB500817 : List Nat :=
  [0x30418c12, 0xc4018b92, 0x1bbc18ad2, 0xcf818b92, 0x610418432, 0xd8018b92, 0x51418c12,
    0x25c018f52, 0x1bd418fd2, 0x1c3c18fd2, 0x1c8818fd2, 0x1ccc18fd2, 0x1db018fd2, 0x1d419152,
    0x1f8018fd2, 0x2fc19152, 0x850191b2, 0xf7c195b2, 0x25c019492, 0xf80195b2, 0x1034195b2,
    0x1d4419512, 0x1228195b2, 0x12e4195b2, 0x128019ab2, 0xb5c19b12, 0x6f419b52, 0x324019932,
    0xd8019b12, 0x91419b52, 0xc4019b52, 0xe1c19b52, 0xf001a032, 0xd341a052, 0x10741a032,
    0x66b019b12, 0x1801a112, 0x2d41a112, 0x15d41a032, 0x183c1a512, 0x2e801a3f2, 0x41a692, 0x1a692,
    0x24001a4d2, 0x401a6b2, 0x2fc1a692, 0x52c1a6b2, 0x9401ab92, 0x9ac1ab92, 0x13181ab12,
    0xa141ab92, 0xa801ab92, 0x151c1ab12, 0x11c41ab92, 0x1e401aff2, 0x1ec41aff2, 0x40c81ae32,
    0x1ee41aff2, 0x18d41b052, 0x19c01b052, 0x206c1b052, 0x35c01aff2, 0x7541b6b2, 0xf401b652,
    0xfa41b652, 0x1e181b592, 0xccc1b6b2, 0x16901b652, 0x1341b832, 0x1c01b832, 0xb641bc52,
    0x14401bbf2, 0xe001bc52, 0xfc1bd12, 0x4241bd12, 0x5f01bd92, 0x4241c272, 0x48c01bef2,
    0x14401c192, 0x1bc1c2b2, 0x2c1c2d2, 0x47c1c2b2, 0x3ec1c2d2, 0x9401c812, 0xc941c812, 0xce81c812,
    0xcb41c812, 0xd3c1c812, 0xd401c812, 0xe041c812, 0x1c8d2, 0x35c1c8d2, 0x60c1c8d2, 0xcf81c8d2,
    0xb241ce12, 0x16401cdb2, 0xe001ce12, 0x109c1ce12, 0x11ec1ce12, 0x5a01cf32, 0x5941cf92,
    0x1d401d352, 0xeec1d412, 0xfb41d412, 0x34c01d232, 0x1acc1d392, 0x1a301d412, 0x6a41da72,
    0x6801da72, 0x9a41da52, 0x2c501d892, 0x7f41da72, 0x8501da72, 0x9f41da72, 0x17fc1da72,
    0x7401e072, 0x5a41e0b2, 0x11801e012, 0x67c1e0b2, 0x7041e0b2, 0x7c01e0b2, 0x8541e0b2,
    0x23901df52, 0x1641e712, 0x2981e712, 0x76a41e132, 0x7c01e6d2, 0x3401e712, 0x3641e712,
    0x40c1e712, 0x45c1e712, 0x96c1e712, 0x1c881e6d2, 0x18dc1ec52, 0x44901ea12, 0x19341ec52,
    0x28001ebb2, 0x78b01e2f2, 0x6a9c1e892]

def stageB1 : List (Nat × List Nat) :=
  [(131072, opsB238673), (131072, opsB369745), (131072, opsB500817)]

def opsB631889 : List Nat :=
  [0x6e41f392, 0x6401f392, 0x2bf41f1b2, 0x5f281ef12, 0x7241f392, 0x7801f392, 0x9fc1f392,
    0xad41f392, 0xadc1f392, 0x1fa52, 0xac41f9d2, 0x12801f972, 0x13641f972, 0x2e41fa52, 0x7b801ef12,
    0x12641fff2, 0x7e901fa52, 0x7e381f912, 0x126c1fff2, 0x75681faf2, 0x13001fff2, 0x134c1fff2,
    0x16141fff2, 0x1f420772, 0x634020272, 0x22c20772, 0x7110201d2, 0x13c420692, 0x34c20772,
    0x3d420772, 0x47420772, 0x7f481fd32, 0x10420e32, 0x819820772, 0xfc20e32, 0x14020e32,
    0x1c420e32, 0x29820e32, 0x31c20e32, 0x45420e32, 0x8c021492, 0x837420e32, 0x18c214f2,
    0x180214f2, 0x94021492, 0x294214f2, 0x7f4214f2, 0xa4021592, 0x77421b92, 0xfc021b32, 0x8ac21b92,
    0x90021b92, 0x9421c12, 0xab021b92, 0x340222b2, 0x86dc21b92, 0x4dc222b2, 0x64c021dd2,
    0x544222b2, 0x858021652, 0xfc229d2, 0x887822252, 0x653c224b2, 0x130229d2, 0x875821d72,
    0x2ac229d2, 0x52c229d2, 0x640230b2, 0x9a423092, 0x8a70229d2, 0x89a422732, 0x7f4230b2,
    0x91c230b2, 0x97c230b2, 0x44c022db2, 0x7423832, 0x14023832, 0x8c0023092, 0x19c23832,
    0x20c23832, 0x29423832, 0x2d423832, 0x34023832, 0xac23ef2, 0xb4023ef2, 0x8dd823832, 0xc1423ef2,
    0x2423f92, 0x4023f92, 0xc423f92, 0x19c23f92, 0x37c23f92, 0x2bc24052, 0x2bd0244d2, 0x8f2c23f92,
    0x15dc245f2, 0xc4024672, 0xc5c24672, 0xcc424672, 0xcf824672, 0xdb424672, 0xf8024672,
    0xf9c24672, 0xacc24df2, 0x134024d72, 0x130024d92, 0xba424df2, 0xc1424df2, 0xfc024df2,
    0x102c24df2, 0x130024dd2, 0x931c24cd2, 0x929024c52, 0x933024d72, 0x936424d92]

def opsB762961 : List Nat :=
  [0xac425b12, 0x94025b12, 0x946425272, 0x124025ab2, 0x128425ab2, 0xb4025b12, 0xc2c25b12,
    0xce825b12, 0x26425bd2, 0x4c26352, 0x3380260b2, 0x4026352, 0x6426352, 0xfc26352, 0x24026352,
    0x2fc263f2, 0x850263f2, 0x5bc26ad2, 0x5e4026692, 0xa8426ad2, 0x20f0269b2, 0x184c26ad2,
    0x198026ad2, 0x2c26c32, 0x4026c32, 0x90427372, 0xa0027372, 0xd1027352, 0xe1427352, 0xf0027352,
    0xcf427372, 0x103427352, 0xe8c27372, 0x10a427372, 0x15c027af2, 0x5427c12, 0xa0027b92,
    0xdc27c12, 0x13427c12, 0x184027af2, 0x33427c12, 0xdc27c52, 0x7c0283d2, 0x151c28312, 0x58c283f2,
    0x5a0283f2, 0x76c283f2, 0x2f4028212, 0xa44283f2, 0xa80283f2, 0x82428c12, 0xd9828bd2,
    0xf4028bd2, 0xa09c283d2, 0xad428c12, 0x136428bb2, 0xc7428c12, 0xe4428c12, 0x120028c12,
    0x179c28c12, 0x298294d2, 0x484294d2, 0x93ac28d92, 0x945828d92, 0x900294d2, 0x9e4294d2,
    0x40c295d2, 0x298295d2, 0x4cc29d72, 0xa520294d2, 0x22f029bf2, 0x60429d72, 0x9bc29d72,
    0x74029e32, 0x1c2a652, 0xa70029d72, 0x1802a652, 0x1e42a652, 0x9842a5f2, 0x2c02a652, 0x5742a652,
    0x5f02a652, 0x6302aeb2, 0xa93c2a652, 0x35702ac52, 0x6bc2aeb2, 0x8542aeb2, 0x3042af12,
    0xb242aeb2, 0x5f02af12, 0x3242afb2, 0x5402afb2, 0x4742b7b2, 0x1c882b692, 0xd3c2b7b2,
    0x1f702b6d2, 0x13942b7b2, 0x25e42b6d2, 0xac2b8d2, 0x3c42b8d2, 0xaca82b312, 0xacb42b332,
    0xaccc2b3f2, 0xac982b272]

def opsB894033 : List Nat :=
  [0x7402c2f2, 0xae5c2ba52, 0xadcc2b7b2, 0xae882ba32, 0x8242c2f2, 0xc42c352, 0x1302c352,
    0x1aa42c232, 0x64c2c352, 0x12802cb92, 0xb0b42c352, 0x1a942cb32, 0x1b002cb32, 0x13d42cb92,
    0x1bc02cb32, 0x16342cb92, 0x101c2d4d2, 0xb2982cb92, 0x5ab02d112, 0x10e42d4d2, 0x12bc2d4d2,
    0x13542d4d2, 0x18402d492, 0x138c2d4d2, 0x232c2dd32, 0x21b82dd32, 0x23642dd32, 0x32002dc72,
    0x23b42dd32, 0x24802dd32, 0x35d42dc52, 0x25ac2dd32, 0x942e012, 0x6b42e7f2, 0x1df02e6f2,
    0x12002e792, 0xb6a42db52, 0x4242e852, 0xd802e7f2, 0x60c2e852, 0x6842e852, 0x13cc2f112,
    0xb9e82e852, 0x13d42f112, 0x21b02f052, 0x14b42f112, 0xb8742e1f2, 0x342fb32, 0xbc182f112,
    0x1f402fa12, 0x1a742fa52, 0x9542fb32, 0x136c2fab2, 0xb2c2fb32, 0x11c2fc32, 0x29402fa52,
    0x1d0430372, 0x14030552, 0xab0304f2, 0xbe8c2fb32, 0xa2c30592, 0xb4430592, 0xd1030592,
    0x6e430ef2, 0xc14030532, 0x28430fd2, 0x54030fb2, 0x40030fd2, 0x54430fd2, 0x60430fd2,
    0x18c31032, 0x96c31992, 0xc3c830fd2, 0xc37430e52, 0x85031992, 0x10431a32, 0x6431a92,
    0x98431a32, 0x56431a92, 0xc5b0316d2, 0xc5a431732, 0xc568315d2, 0xc67c319f2, 0xc5d8317f2]

def opsB1025105 : List Nat :=
  [0x3a432ad2, 0xc7e032092, 0xc74c31ed2, 0x66a8325d2, 0x44432ad2, 0x2ac32ad2, 0x48432ad2,
    0x51432ad2, 0xe6432a72, 0x34032b32, 0x138433472, 0xca8832ad2, 0xca04328d2, 0x2a8033352,
    0x14d433472, 0x1d0433412, 0x20c335b2, 0x240335b2, 0x23433fd2, 0xccd033352, 0x26c33fd2,
    0x29834012, 0x85033fd2, 0x9e433fd2, 0xa3c33fd2, 0x54034012, 0x58c34012, 0xc1c33fd2, 0x8c034012,
    0x47c34ab2, 0x5e4034632, 0x5b434ab2, 0x258034912, 0x5f034ab2, 0x67c34ab2, 0x76434ab2,
    0x7cc34ab2, 0x94034ab2, 0xd3c35512, 0xd270349d2, 0xdd435512, 0xd18034632, 0x3b4c352d2,
    0x11c435512, 0x18035b72, 0x30436072, 0x37c035dd2, 0x45c36072, 0x7c360d2, 0x85036072,
    0x4a4360d2, 0x68036112, 0x30436bb2, 0x124036ad2, 0x128036af2, 0xd73435dd2, 0x76436bb2, 0x36cd2,
    0x29ec371b2, 0x341837452, 0x17bc37612, 0x13037752, 0x9ac37752, 0xd437f12, 0x1e40380f2,
    0xac038212, 0xb4438212, 0x185438172, 0xc3438212, 0xc438332, 0x4b438352, 0xdf5037d52,
    0xdf0437c72, 0xdee037c72, 0xdea437a92]

def opsB1156177 : List Nat :=
  [0x2a439292, 0xe1c038712, 0xe07c38212, 0x35c038ff2, 0x3ec39292, 0x40c39292, 0x5b439292,
    0x65439292, 0x67c39292, 0x80c392f2, 0x114039292, 0xcf839dd2, 0xe48439252, 0x4fc39e52,
    0x64039e52, 0xe5439e52, 0x47439ef2, 0x5bc39ef2, 0x77439ef2, 0xf1c39ef2, 0x6bc3aa92,
    0xe7b039ef2, 0x13803aa52, 0x9643aaf2, 0x11543aa92, 0xa7c3aaf2, 0x2c03ab72, 0x4dc3b712,
    0xea803aa92, 0x6143b712, 0x8de03b032, 0x64c3b712, 0x8043b712, 0xe80c3a092, 0x3dc3c352,
    0xeda03b712, 0x287c3c172, 0x55003bf32, 0x40c3c352, 0x4dc3c352, 0x63c3c352, 0x7843c352,
    0xc843c352, 0x20c3c432, 0xdc03cf72, 0xf0d43c352, 0x99c03c852, 0xe643cf72, 0xea43cf72,
    0x64c3d032, 0x6943d032, 0xa0c3d032, 0x18c3d0d2, 0xd103dc92, 0xf3fc3d032, 0x6543dcf2,
    0x2d403daf2, 0xf20c3c852, 0xd803e872, 0xbac3e932, 0xf6303d912, 0xc143e932, 0xc943e932,
    0xcdc3e932, 0xda43e932, 0xf843e932, 0xf8703e1d2, 0xf8803e232, 0xf82c3e0f2, 0xf8103e052]

def opsB1287249 : List Nat :=
  [0x1a443f912, 0xfae03ec52, 0xfb443ed72, 0x4e503f672, 0x1a9c3f912, 0x1afc3f912, 0x1f0c3f912,
    0x228c3f912, 0xe00406d2, 0xfe243f912, 0x38c0404b2, 0xfd4c3f592, 0x11b4406d2, 0x12bc406d2,
    0x1c040852, 0x103c413f2, 0x1017040612, 0x1174413f2, 0x208041332, 0x8c41592, 0x2440413f2,
    0x2c042052, 0x51442292, 0x55c42292, 0x10410410b2, 0x64042292, 0xfc422f2, 0x594422f2,
    0x1a4042f12, 0x1083c42192, 0x1a8442f12, 0x551842c52, 0x19443092, 0x1bc43092, 0x20c43092,
    0x32c43092, 0x3ec43092, 0x4dc43092, 0x10c430f2, 0x13043e72, 0x10b9c42f12, 0x90043e12,
    0x10b3442d92, 0xa7443e12, 0x48443e72, 0x5f043e72, 0x24043ed2, 0xcd444bd2, 0x10f0843cf2,
    0xac444bf2, 0x550044832, 0xbac44bf2, 0xdb444bf2, 0x124044bd2, 0x1119444692, 0x1118c44652,
    0x11170447d2, 0x1120044832]

def opsB1418321 : List Nat :=
  [0x7d4461b2, 0x114a0452b2, 0x105846132, 0x80c461b2, 0x1129444a52, 0x164046df2, 0x270c46e52,
    0xdb046f92, 0xe9446f92, 0x1143c46252, 0x5447052, 0xfb446f92, 0x3d447052, 0x18c47ed2,
    0x11be847052, 0x11aa446b12, 0x11c0047052, 0x23447ed2, 0x1c447f32, 0xd1448d32, 0x11f6847dd2,
    0x11fa447ed2, 0x11f8047e12, 0xd5448d32, 0x173449b72, 0x1232848d32, 0x121d848792, 0x1bac49b72,
    0x1c5c49b72, 0x74449d32, 0x2a44ac52, 0x1268049a92, 0x1271049d32, 0x3dc4ac52, 0x7344ac32,
    0x4c44ac52, 0x12ab84ab12, 0x12af44ac32, 0x129f44a7d2, 0x12aa04ab12, 0x12ac44ab12]

def opsB1549393 : List Nat :=
  [0x4644c992, 0x12e104b852, 0xbf44c932, 0x33404c732, 0x4dc4c992, 0x4d44c992, 0x67c4c992,
    0x15c04c8d2, 0x8ec4c992, 0x2404d952, 0x132544c992, 0x131444c572, 0xce84d8d2, 0x4644d952,
    0x4c04d952, 0x5044d952, 0x6644e8b2, 0x13804e832, 0x134f44d412, 0x1c04e952, 0x8ac4e912,
    0x3e44e952, 0x5dc4e952, 0x8344e952, 0xd844e9b2, 0xdc04f912, 0x139e44e852, 0x138d44e372,
    0x10584f912, 0x5544fa92, 0x7c04fa92, 0x63050a12, 0x13dfc4f812, 0x13e684f9d2, 0x60c50ab2,
    0x64c50ab2, 0xa0050ab2, 0x1d0451a12, 0x1424850932, 0x142a450ab2, 0x1a4051a32, 0x1acc51a32,
    0x1af451a32, 0x1b2451a32, 0x18051b92, 0x14410510b2, 0x1440851072, 0x1440451012]

def opsB1680465 : List Nat :=
  [0xdc53172, 0x147a051f52, 0x1466451a32, 0x10453172, 0x14053172, 0x7e453152, 0x169054132,
    0x14b7c52e52, 0xf8054192, 0x14b1c52c72, 0x141c54192, 0x147454192, 0x165454192, 0x274454132,
    0x34055392, 0x14fe453ff2, 0xa85c54b32, 0x71c054df2, 0xe7455312, 0x54553d2, 0x244553d2,
    0x52455452, 0x18c0563f2, 0x1548c55272, 0x1534054d12, 0xad4564b2, 0xb30564b2, 0x114565f2,
    0x120c57232, 0xfc0575f2, 0x15918564b2, 0x13457772, 0x2d457772, 0x34457772, 0x75457772,
    0x15d40575f2, 0x15cfc57432, 0xd0e457ef2, 0x15d68575f2, 0x15a0c56832]

def opsB1811537 : List Nat :=
  [0x4c0598f2, 0x16084582d2, 0x161a4586f2, 0x24d059752, 0x614598f2, 0x6dc598f2, 0x784598f2,
    0x86c598f2, 0x874598f2, 0x7c59992, 0xdc05aad2, 0x1653459572, 0xf145aad2, 0x1b005aa32,
    0x14c05aa92, 0x8c5abb2, 0x3d45abb2, 0x43c5abb2, 0x12945abb2, 0x27605bc92, 0x16ab45aad2,
    0x7a105b872, 0x169245a672, 0x1ab45bd52, 0x2a705bc92, 0x4c05beb2, 0x2445d132, 0x16f305bd52,
    0x25c5d132, 0x16e005b872, 0x1645d192, 0x2c05e372, 0xbcc5e392, 0x172e45cbd2, 0x245e452,
    0x405e452, 0x22c5e452, 0x4d45e452, 0x405e492, 0x176f05dbf2, 0x176a05da92, 0x1779c5deb2,
    0x1768c5da32]

def stageB2 : List (Nat × List Nat) :=
  [(131072, opsB631889), (131072, opsB762961), (131072, opsB894033), (131072, opsB1025105),
    (131072, opsB1156177), (131072, opsB1287249), (131072, opsB1418321), (131072, opsB1549393),
    (131072, opsB1680465), (131072, opsB1811537)]

def opsB1942609 : List Nat :=
  [0x17545ffb2, 0x17aa05eb72, 0x153c5ffb2, 0x179d05e752, 0xd460112, 0x21461332, 0x5a061332,
    0x2280612d2, 0x13d461392, 0x640060f72, 0x14b461392, 0x64c61572, 0x24062832, 0x1842461092,
    0x176d061552, 0x2a462832, 0x2c062832, 0x2e462832, 0x5f462832, 0x28463c52, 0x1891862472,
    0x189f862812, 0x7cc63c12, 0x31c63c52, 0xdec63c12, 0x117463c52, 0x18065112, 0x18eec63c12,
    0x18d9063672, 0x48465152, 0x5dc65152, 0xb5465152, 0x105865112, 0x85465212, 0x1909464272,
    0x18fd463f52]

def opsB2073681 : List Nat :=
  [0x2466892, 0x194b0652f2, 0x192c064c12, 0x4c66892, 0xa466892, 0xfc66892, 0xb3467cd2,
    0x199a866732, 0x197ec66012, 0x1dfc67bd2, 0x1bc067c32, 0x116c67cd2, 0x13fc67cd2, 0x5a469292,
    0x19ed067c12, 0x35fc69012, 0x19dd867792, 0x3a4692f2, 0xf46a752, 0xdc06a7b2, 0x1a268689f2,
    0x9b46a7f2, 0xf46a932, 0x15c46b412, 0x1aa186a8d2, 0x1a9f46a872, 0x1a8d86a372]

def opsB2204753 : List Nat :=
  [0x8f46cfd2, 0x1ae386b932, 0x1ac346b0f2, 0xa2c6cfd2, 0x21306ceb2, 0x5946d0f2, 0x3b2c6e452,
    0x1b3d86cfd2, 0x1b2346c912, 0x10c6e772, 0x1b3986ceb2, 0x86c6fd72, 0x1b9006e452, 0x1b9a86e752,
    0x8a46fd72, 0x9246fd72, 0x9446fd72, 0x9dc6fd72, 0x57471452, 0x1be786fa72, 0x1bf306fd32,
    0x5cc71452, 0x60c71452, 0x91c71452, 0x1c29470a52, 0x1c2d470bb2, 0x1c230708d2, 0x1c0cc70332]

def opsB2335825 : List Nat :=
  [0x7c737f2, 0x1c70871cb2, 0x1c7b071ef2, 0xb4737f2, 0x1c2ec70bb2, 0xfdc74e92, 0x1cce0733f2,
    0x1cd5c73572, 0x104074e92, 0x12d474e72, 0x143474e92, 0x1f1474e12, 0xa7c74fb2, 0x133c766f2,
    0x1d36074dd2, 0x1d1a4746b2, 0xf8476732, 0x1540766f2, 0x384768b2, 0x8a478072, 0x1d94876552,
    0x1d88476212, 0xa7c78072, 0x1d970765d2, 0x1dbf476fd2, 0x1dbbc76f12, 0x1dad476b52]

def opsB2466897 : List Nat :=
  [0x1e09478252, 0x1dfb477ef2, 0x1e098782b2, 0x1dd5477572]

def stageB3 : List (Nat × List Nat) :=
  [(131072, opsB1942609), (131072, opsB2073681), (131072, opsB2204753), (131072, opsB2335825),
    (24544, opsB2466897)]

end OrderBitmap.Cert

namespace OrderBitmap.Cert

/-! ## The certificate

The three stages: the bitmap `certH` of the orders below `107601`, produced block by block
from the seeds; the intervals from `107601` to `2491440`, covered by two-group truncations read
from `certH`; and the chain, from `[26143, 2491440]` to the tail. The heavy checks are separate
declarations, so the kernel frees its cache between them, and `Elab.async` is off so that they
do not run at once. -/

/-- The bitmap of the orders below `107601` that the certificate records. -/
noncomputable def certH : Nat := ofWords hWords 0

theorem stageA0_ok : blocksOK seedBits certH 0 stageA0 = true := by
  decide +kernel

theorem stageA0_end : blocksEnd 0 stageA0 = 4096 := by rfl

theorem stageA1_ok : blocksOK seedBits certH 4096 stageA1 = true := by
  decide +kernel

theorem stageA1_end : blocksEnd 4096 stageA1 = 8192 := by rfl

theorem stageA2_ok : blocksOK seedBits certH 8192 stageA2 = true := by
  decide +kernel

theorem stageA2_end : blocksEnd 8192 stageA2 = 16384 := by rfl

theorem stageA3_ok : blocksOK seedBits certH 16384 stageA3 = true := by
  decide +kernel

theorem stageA3_end : blocksEnd 16384 stageA3 = 24576 := by rfl

theorem stageA4_ok : blocksOK seedBits certH 24576 stageA4 = true := by
  decide +kernel

theorem stageA4_end : blocksEnd 24576 stageA4 = 107601 := by rfl

theorem sound_certH_mod : Sound (certH % 2 ^ 107601) := by
  have h0 : Sound (certH % 2 ^ 0) := by
    rw [Nat.pow_zero, Nat.mod_one]
    intro n hn
    simp at hn
  have h1 := Sound.of_blocksOK sound_seedBits 0 stageA0 h0 stageA0_ok
  rw [stageA0_end] at h1
  have h2 := Sound.of_blocksOK sound_seedBits 4096 stageA1 h1 stageA1_ok
  rw [stageA1_end] at h2
  have h3 := Sound.of_blocksOK sound_seedBits 8192 stageA2 h2 stageA2_ok
  rw [stageA2_end] at h3
  have h4 := Sound.of_blocksOK sound_seedBits 16384 stageA3 h3 stageA3_ok
  rw [stageA3_end] at h4
  have h5 := Sound.of_blocksOK sound_seedBits 24576 stageA4 h4 stageA4_ok
  rw [stageA4_end] at h5
  exact h5

theorem certH_lt : certH < 2 ^ 107601 := by
  decide +kernel

/-- **Every order recorded in `certH` carries a pointed model.** -/
theorem sound_certH : Sound certH := by
  have h := sound_certH_mod
  rwa [Nat.mod_eq_of_lt certH_lt] at h

theorem certH_interval : intervalOK certH 26143 81458 = true := by
  decide +kernel

theorem stageB0_ok : coversOK certH 107601 stageB0 = true := by
  decide +kernel

theorem stageB0_end : blocksEnd 107601 stageB0 = 238673 := by rfl

theorem stageB1_ok : coversOK certH 238673 stageB1 = true := by
  decide +kernel

theorem stageB1_end : blocksEnd 238673 stageB1 = 631889 := by rfl

theorem stageB2_ok : coversOK certH 631889 stageB2 = true := by
  decide +kernel

theorem stageB2_end : blocksEnd 631889 stageB2 = 1942609 := by rfl

theorem stageB3_ok : coversOK certH 1942609 stageB3 = true := by
  decide +kernel

theorem stageB3_end : blocksEnd 1942609 stageB3 = 2491441 := by rfl

/-- **Every size in `[26143, 2491440]` carries a model.** -/
theorem upto_certificate : Upto 26143 2491440 := by
  intro n h1 h2
  by_cases hY : n ≤ 107600
  · exact sound_certH n (testBit_of_intervalOK certH_interval h1 (by omega))
  by_cases hB0 : n < 238673
  · exact hasPtModel_of_coversOK sound_certH _ _ stageB0_ok n (by omega)
      (by rw [stageB0_end]; omega)
  by_cases hB1 : n < 631889
  · exact hasPtModel_of_coversOK sound_certH _ _ stageB1_ok n (by omega)
      (by rw [stageB1_end]; omega)
  by_cases hB2 : n < 1942609
  · exact hasPtModel_of_coversOK sound_certH _ _ stageB2_ok n (by omega)
      (by rw [stageB2_end]; omega)
  exact hasPtModel_of_coversOK sound_certH _ _ stageB3_ok n (by omega)
    (by rw [stageB3_end]; omega)

theorem chain_certificate : 80 * (79 * (P79 + 2) + 26143) ≤ chain 26143 5263 2491440 := by
  decide +kernel

/-- **Every size from `26143` on carries a model.** -/
theorem hasModel_of_ge {n : Nat} (hn : 26143 ≤ n) : HasModel n :=
  ((upto_certificate.chain 5263).tail chain_certificate n hn).hasModel

end OrderBitmap.Cert

/-! ## The main theorem -/

/-- **Every `n ≥ 26143` is the order of a magma satisfying Equation 677**, with the operation
written out: there is a binary operation `op` on `Fin n` with
`x = op y (op x (op (op y x) y))` for all `x` and `y`. -/
theorem exists_op_of_ge {n : Nat} (hn : 26143 ≤ n) :
    ∃ op : Fin n → Fin n → Fin n, ∀ x y : Fin n, x = op y (op x (op (op y x) y)) :=
  exists_fin_of_hasModel (OrderBitmap.Cert.hasModel_of_ge hn)

/-- **Every `n ≥ 26143` is the order of a magma satisfying Equation 677**: some
multiplication on `Fin n`, a type with exactly `n` elements, satisfies `Equation677`. -/
theorem exists_mul_of_ge {n : Nat} (hn : 26143 ≤ n) : ∃ _ : Mul (Fin n), Equation677 (Fin n) :=
  let ⟨op, h⟩ := exists_op_of_ge hn
  ⟨⟨op⟩, h⟩

end Spectrum677


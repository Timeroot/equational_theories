import equational_theories.Definability.Structural
import equational_theories.Equations.All

/-!
# The affine plane over `ZMod 3` and the transvection obstruction

Equation `692` has a nine-element model that is affine over `V = (ZMod 3)²`,

    x ◇ y = P x + Q y + ρ,   P = ![![2,2],![0,2]],  Q = ![![2,1],![0,2]],  ρ = (0,1),

and `P + Q = 1`, so every translation of `V` is an automorphism of it. In fact the translations are
*all* of them: `Aut(M) = V` acting regularly. That makes `692` a candidate source for the
exact-automorphism obstruction of `Definability/Structural.lean` — a structural companion of `M`
has exactly the automorphisms of `M` — but the family of translation-invariant operations on nine
points has `9 ^ 9 = 387420489` members, three orders of magnitude past what
`Definability/ExactAut.lean` can enumerate. So it is classified instead.

An operation invariant under all translations is `x ◇ y = x + f (y - x)` for `f y = 0 ◇ y`, and
writing `h u = f u + u` the target laws become one condition on `h`:

* `1073` (`x = y ◇ ((x ◇ (x ◇ x)) ◇ y)`) says `h (u + h u) = h u`;
* `4386` (`x ◇ (x ◇ x) = (y ◇ x) ◇ y`) says `h (u - h u) = h u`, which is the same thing.

Read geometrically: `h` is constant along the line through `u` in direction `h u`. Two lines of
`AG(2, 3)` with different directions meet, and the value at the meeting point is both directions,
so all the directions that occur are the same one, say `⟨d⟩`, and `h` is constant on the cosets of
`⟨d⟩` with values inside `⟨d⟩`. The transvection

    A_d w = w + λ_d(w) · d,   λ_d(w) = d₁w₂ - d₂w₁

then commutes with `h` (it moves `w` along its own `⟨d⟩`-coset and fixes `⟨d⟩` pointwise), hence
with `f`, hence is an automorphism of `◇` — and it is not an automorphism of `M`, because
`Aut(M)` is only the translations. That contradiction refutes `L.StructuralFromFin Law692` for
`L ∈ {1073, 4386}`, and by implication for every law implying one of them (`4458 → 4386`,
`14 → 1073`).

The `105` solutions are `h w = δ(λ_d(w)) · d` for a direction `d` and an arbitrary
`δ : ZMod 3 → ZMod 3`, i.e. `x ◇ y = -x - y + δ(λ_d(y - x)) · d`; the count `4 · 3³ - 3 = 105`
matches an exhaustive search. Nothing below needs the list, only the transvection.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace E9

/-- The affine plane over `ZMod 3`, as the carrier of everything here. -/
abbrev V := ZMod 3 × ZMod 3

/-- Scalar multiplication, written out so that every fact about it is a `decide`. -/
def smul (c : ZMod 3) (v : V) : V := (c * v.1, c * v.2)

/-- The determinant pairing. For `d ≠ 0`, `lam d` is a nonzero linear functional whose kernel is
the line `⟨d⟩`, so it labels the three cosets of that line. -/
def lam (d w : V) : ZMod 3 := d.1 * w.2 - d.2 * w.1

/-- The transvection with axis `⟨d⟩`: it fixes `⟨d⟩` pointwise and moves every other point along
its own `⟨d⟩`-coset. It has order `3` and, for `d ≠ 0`, is not a translation. -/
def A (d w : V) : V := w + smul (lam d w) d

/-- The inverse transvection. -/
def Ainv (d w : V) : V := w - smul (lam d w) d

/-! ### Linear algebra over `ZMod 3`, all by `decide` -/

theorem smul_zero_left (v : V) : smul 0 v = 0 := by revert v; decide

theorem smul_one_left (v : V) : smul 1 v = v := by revert v; decide

theorem smul_two (v : V) : smul 2 v = v + v := by revert v; decide

theorem smul_smul (a b : ZMod 3) (v : V) : smul a (smul b v) = smul (a * b) v := by
  revert a b v; decide

theorem cases3 (c : ZMod 3) : c = 0 ∨ c = 1 ∨ c = 2 := by revert c; decide

theorem A_add (d a b : V) : A d (a + b) = A d a + A d b := by revert d a b; decide

theorem A_sub (d a b : V) : A d (a - b) = A d a - A d b := by revert d a b; decide

theorem A_left (d : V) : Function.LeftInverse (Ainv d) (A d) := by revert d; decide

theorem A_right (d : V) : Function.RightInverse (Ainv d) (A d) := by revert d; decide

theorem A_eq_self {d w : V} (h : lam d w = 0) : A d w = w := by revert h; revert d w; decide

/-- `A d w` differs from `w` by a multiple of `d`. -/
theorem A_eq_add (d w : V) : A d w = w + smul (lam d w) d := rfl

/-- Two lines of `AG(2, 3)` in different directions meet. -/
theorem lines_meet {d b : V} (h : lam d b ≠ 0) (u₀ u : V) :
    ∃ s t : ZMod 3, u₀ + smul s d = u + smul t b := by
  revert h; revert d b u₀ u; decide

/-- Two nonzero vectors killed by the same functional are parallel. -/
theorem parallel {d b : V} (hb : b ≠ 0) (h : lam d b = 0) : ∃ c : ZMod 3, d = smul c b := by
  revert hb h; revert d b; decide

theorem three_smul (u d : V) : (u + d) + smul 2 d = u := by revert u d; decide

/-! ### The transvections as permutations -/

/-- The transvection as an `Equiv.Perm`, which is what `Magma.IsEndo.of_definable` needs. -/
def Aperm (d : V) : Equiv.Perm V := ⟨A d, Ainv d, A_left d, A_right d⟩

@[simp] theorem coe_Aperm (d : V) : ⇑(Aperm d) = A d := rfl

/-- Translation as an `Equiv.Perm`. -/
def tr (v : V) : Equiv.Perm V :=
  ⟨fun x ↦ x + v, fun x ↦ x - v, fun x ↦ by simp, fun x ↦ by simp⟩

@[simp] theorem coe_tr (v : V) : ⇑(tr v) = fun x ↦ x + v := rfl

/-! ### The source model -/

/-- The affine model `x ◇ y = P x + Q y + ρ` of equation `692` on `V`. -/
@[implicit_reducible] def m692 : Magma V :=
  Magma.mk fun x y ↦ (2 * x.1 + 2 * x.2 + 2 * y.1 + y.2, 2 * x.2 + 2 * y.2 + 1)

theorem m692_sat : @satisfies _ V m692 Law692 :=
  (@Law692.models_iff V m692).mpr (by decide)

/-- `P + Q = 1`, so the translations are automorphisms. -/
theorem m692_endo_tr (v : V) : m692.IsEndo ⇑(tr v) := by
  simp only [coe_tr]; revert v; decide

/-- No transvection is an automorphism of the model: `Aut(m692)` is only the translations. -/
theorem m692_not_endo_A {d : V} (hd : d ≠ 0) : ¬ m692.IsEndo (A d) := by
  revert hd; revert d; decide

/-- The row through the origin of a second source model, this one for equation `1488`.  Every
*affine* translation-invariant model of `1488` admits a transvection — the nine of them have
automorphism groups of order `162` — so this row has to be a genuine quadratic, and it is written
here as its interpolating polynomial. -/
def f1488 (u : V) : V :=
  (1 + u.1 * u.2 * u.2 + u.1 * u.1 + u.1 * u.1 * u.2 + u.1 * u.1 * u.2 * u.2,
   1 + u.1 + u.1 * u.2 + 2 * u.1 * u.1 * u.2 + 2 * u.1 * u.1 * u.2 * u.2)

/-- The model `x ◇ y = x + f (y - x)` of equation `1488`. -/
@[implicit_reducible] def m1488 : Magma V := Magma.mk fun x y ↦ x + f1488 (y - x)

theorem m1488_sat : @satisfies _ V m1488 Law1488 :=
  (@Law1488.models_iff V m1488).mpr (by decide)

theorem m1488_endo_tr (v : V) : m1488.IsEndo ⇑(tr v) := by
  simp only [coe_tr]; revert v; decide

/-- `Aut(m1488)` is only the translations; in particular no transvection is in it. -/
theorem m1488_not_endo_A {d : V} (hd : d ≠ 0) : ¬ m1488.IsEndo (A d) := by
  revert hd; revert d; decide

/-! ### Arithmetic of the plane, all by `decide`

`3 = 0` on `V`, so doubling is negation and tripling is zero; those two facts are what turn the
law reductions into the single condition on `h`. -/

theorem lam_self (d : V) : lam d d = 0 := by revert d; decide

theorem eq_zero_of_eq_neg {a : V} (h : a = -a) : a = 0 := by revert h; revert a; decide

theorem eq_zero_of_add_self {a k : V} (h : a + k = a) : k = 0 := by revert h; revert a k; decide

theorem sub_sub_eq_add (a b : V) : a - b - b = a + b := by revert a b; decide

theorem add_add_eq_sub (a b : V) : a + b + b = a - b := by revert a b; decide

theorem sub_add_self (a k : V) : a - (a + k) = -k := by revert a k; decide

theorem neg_sub_three (a k : V) : -k - (a + k + k) = 0 - a := by revert a k; decide

theorem add_three (a k : V) : a + k + k + k = a := by revert a k; decide

theorem add_sub_self' (a b : V) : a + b - b = a := by revert a b; decide

theorem neg_sub_add (u k : V) : -u - k + k = -u := by revert u k; decide

theorem zero_sub_neg (u : V) : (0 : V) - -u = u := by revert u; decide

theorem negadd_sub_zero (a u : V) : -u + a - 0 = a - u := by revert a u; decide

theorem sub_add_left (u a : V) : u - (a + u) = -a := by revert u a; decide

theorem neg_add_cancel_left' (u a : V) : -u + (u + a) = a := by revert u a; decide

theorem shuffle {a b c k : V} (h : a + b = c + k) : b + -a = a + c + k := by
  revert h; revert a b c k; decide

theorem cancel_left' {a b c : V} (h : a + b = a + c) : b = c := by revert h; revert a b c; decide

theorem cancel_right' {a b c : V} (h : a + c = b + c) : a = b := by revert h; revert a b c; decide

theorem eq_of_double {a b : V} (h : a + a = b + b) : a = b := by revert h; revert a b; decide

theorem sub_sub_self' (a u : V) : a - (a - u) = u := by revert a u; decide

theorem sub_add_cancel' (a b : V) : a - b + b = a := by revert a b; decide

theorem sub_add_comm' (u c k : V) : u - c + k = u + (k - c) := by revert u c k; decide

theorem neg_add_zero' (c : V) : -c + c = 0 := by revert c; decide

theorem key_arg (u k : V) : u + (k + u) = -u + k := by revert u k; decide

theorem key_fin (u k : V) : -u + (-u + k) = k + u := by revert u k; decide

theorem arg_3272 (w k c : V) : w + (k + w) + (c + 0) = c - w + k := by revert w k c; decide

theorem fin_3272 (w k c : V) : c - w + c + (c - w + k) = k + w := by revert w k c; decide

theorem arg_1519 (c u k : V) : c - u + k - c = k - u := by revert c u k; decide

theorem arg_3472 (c u k : V) : c + k - (c + u) = k - u := by revert c u k; decide

theorem neg_of_sub {c u z : V} (h : c - u = c + z) : z = -u := by revert h; revert c u z; decide

theorem neg_of_add {c u z : V} (h : c = c + u + z) : z = -u := by revert h; revert c u z; decide

/-- Every vector lies on some transvection axis: this is what turns a constant or a translation
row into an automorphism. -/
theorem exists_dir (c : V) : ∃ d : V, d ≠ 0 ∧ lam d c = 0 := by revert c; decide

/-! ### Translation-invariant operations -/

/-- The row through the origin, which determines a translation-invariant operation. -/
def fOf (M' : Magma V) (u : V) : V := M'.op 0 u

/-- The row through the origin, shifted: this is the function the target laws constrain. -/
def hOf (M' : Magma V) (u : V) : V := M'.op 0 u + u

theorem hOf_eq (M' : Magma V) (w : V) : hOf M' w = fOf M' w + w := rfl

theorem fOf_def (M' : Magma V) (u : V) : M'.op 0 u = fOf M' u := rfl

/-- **The classification of translation-invariant operations.** -/
theorem op_eq {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v)) (x y : V) :
    M'.op x y = x + fOf M' (y - x) := by
  have h := htr x 0 (y - x)
  simp only [coe_tr, zero_add, sub_add_cancel] at h
  rw [fOf, ← h, add_comm]

/-- The diagonal is a translation: `x ◇ x = x + f 0`. -/
theorem op_self {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v)) (x : V) :
    M'.op x x = x + fOf M' 0 := by rw [op_eq htr, sub_self]

/-! ### The geometry: a direction, and the transvection along it -/

/-- **The heart of the argument.** If `h` is constant along the line through `u` in direction
`h u` — which is what both target laws say — then all the directions that occur are one and the
same `⟨d⟩`, and the transvection with that axis commutes with `h` in both senses. -/
theorem exists_transvection {h : V → V} (hstep : ∀ u, h (u + h u) = h u) :
    ∃ d : V, d ≠ 0 ∧ (∀ u, h (A d u) = h u) ∧ (∀ u, A d (h u) = h u) := by
  -- `h` is constant on the whole line `u + ⟨h u⟩`, not just at the next step
  have hline : ∀ (c : ZMod 3) (u : V), h (u + smul c (h u)) = h u := by
    intro c u
    rcases cases3 c with rfl | rfl | rfl
    · rw [smul_zero_left, add_zero]
    · rw [smul_one_left]; exact hstep u
    · rw [smul_two, ← add_assoc]
      have h2 := hstep (u + h u)
      rw [hstep u] at h2
      exact h2
  by_cases hz : ∀ u, h u = 0
  · refine ⟨(1, 0), by decide, fun u ↦ ?_, fun u ↦ ?_⟩
    · rw [hz, hz]
    · rw [hz]; decide
  · simp only [not_forall] at hz
    obtain ⟨u₀, hu₀⟩ := hz
    -- every value of `h` lies on the line `⟨h u₀⟩`
    have hB : ∀ u, lam (h u₀) (h u) = 0 := by
      intro u
      by_contra hne
      obtain ⟨s, t, hst⟩ := lines_meet hne u₀ u
      have e1 := hline s u₀
      rw [hst] at e1
      have e2 := hline t u
      rw [e2] at e1
      rw [← e1] at hne
      exact hne (lam_self _)
    -- and `h` is constant on the cosets of that line
    have hC : ∀ u, h (u + h u₀) = h u := by
      have main : ∀ w, h w ≠ 0 → h (w + h u₀) = h w := by
        intro w hw
        obtain ⟨c, hc⟩ := parallel hw (hB w)
        rw [hc]; exact hline c w
      intro u
      by_cases hu : h u = 0
      · by_contra hne
        rw [hu] at hne
        obtain ⟨c, hc⟩ := parallel hne (hB (u + h u₀))
        have hd2 : smul 2 (h u₀) = smul (2 * c) (h (u + h u₀)) := by
          conv_lhs => rw [hc]
          rw [smul_smul]
        have hh := hline (2 * c) (u + h u₀)
        rw [← hd2, three_smul] at hh
        rw [hu] at hh
        exact hne hh.symm
      · exact main u hu
    refine ⟨h u₀, hu₀, fun u ↦ ?_, fun u ↦ A_eq_self (hB u)⟩
    rw [A_eq_add]
    rcases cases3 (lam (h u₀) u) with e | e | e <;> rw [e]
    · rw [smul_zero_left, add_zero]
    · rw [smul_one_left]; exact hC u
    · rw [smul_two, ← add_assoc, hC, hC]

/-- A transvection that commutes with the row `f` is an automorphism of the operation.  This is
the only way any transvection is ever produced below. -/
theorem isEndo_A' {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v)) {d : V}
    (hf : ∀ w, A d (fOf M' w) = fOf M' (A d w)) : M'.IsEndo (A d) := by
  have hop := op_eq htr
  intro x y
  rw [hop x y, hop (A d x) (A d y), A_add, hf, A_sub]

/-- A transvection commuting with `h` in both senses is an automorphism of the operation. -/
theorem isEndo_A {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v)) {d : V}
    (hD : ∀ u, hOf M' (A d u) = hOf M' u) (hE : ∀ u, A d (hOf M' u) = hOf M' u) :
    M'.IsEndo (A d) := by
  refine isEndo_A' htr fun w ↦ ?_
  have e1 : fOf M' w = hOf M' w - w := by rw [hOf_eq, add_sub_self']
  have e2 : fOf M' (A d w) = hOf M' (A d w) - A d w := by rw [hOf_eq, add_sub_self']
  rw [e1, e2, A_sub, hE, hD]

/-! ### Four ways for a target law to hand over a transvection

The plain step condition `h (u + h u) = h u` is one of them; the other three come from laws that
pin the row down much harder, and they are proved directly from `isEndo_A'`. -/

/-- `hstep` gives a transvection. -/
theorem exists_endo_of_hstep {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hs : ∀ u : V, hOf M' (u + hOf M' u) = hOf M' u) :
    ∃ d : V, d ≠ 0 ∧ M'.IsEndo (A d) := by
  obtain ⟨d, hd, hD, hE⟩ := exists_transvection hs
  exact ⟨d, hd, isEndo_A htr hD hE⟩

/-- The *shifted* step condition also gives one: `h (u + h u + h 0) = h u` is exactly `hstep` for
`H u = h u + h 0`, and `A d` fixes `h 0` because it fixes `H 0 = h 0 + h 0`. -/
theorem exists_endo_of_hstepc {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hs : ∀ u : V, hOf M' (u + hOf M' u + hOf M' 0) = hOf M' u) :
    ∃ d : V, d ≠ 0 ∧ M'.IsEndo (A d) := by
  have hstep : ∀ u : V, hOf M' (u + (hOf M' u + hOf M' 0)) + hOf M' 0
      = hOf M' u + hOf M' 0 := by
    intro u; rw [← add_assoc, hs u]
  obtain ⟨d, hd, hD, hE⟩ := exists_transvection (h := fun w ↦ hOf M' w + hOf M' 0) hstep
  have hD' : ∀ u : V, hOf M' (A d u) + hOf M' 0 = hOf M' u + hOf M' 0 := hD
  have hE' : ∀ u : V, A d (hOf M' u + hOf M' 0) = hOf M' u + hOf M' 0 := hE
  have hcc : A d (hOf M' 0) = hOf M' 0 := by
    have h0 := hE' 0
    rw [A_add] at h0
    exact eq_of_double h0
  refine ⟨d, hd, isEndo_A htr (fun u ↦ cancel_right' (hD' u)) fun u ↦ ?_⟩
  have h1 := hE' u
  rw [A_add, hcc] at h1
  exact cancel_right' h1

/-- A constant row gives one: pick any axis through the constant. -/
theorem exists_endo_of_const {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v)) {k : V}
    (hc : ∀ u : V, fOf M' u = k) : ∃ d : V, d ≠ 0 ∧ M'.IsEndo (A d) := by
  obtain ⟨d, hd, hl⟩ := exists_dir k
  refine ⟨d, hd, isEndo_A' htr fun w ↦ ?_⟩
  rw [hc w, hc (A d w), A_eq_self hl]

/-- A row that is a translation gives one, by the same axis. -/
theorem exists_endo_of_transl {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v)) {b : V}
    (hb : ∀ u : V, fOf M' u = u + b) : ∃ d : V, d ≠ 0 ∧ M'.IsEndo (A d) := by
  obtain ⟨d, hd, hl⟩ := exists_dir b
  refine ⟨d, hd, isEndo_A' htr fun w ↦ ?_⟩
  rw [hb w, hb (A d w), A_add, A_eq_self hl]

/-- A row invariant under translation by each of its own values gives one.  Two independent values
would make `f` periodic in both directions, hence constant, hence with a single value; so all the
values lie on one line `⟨d⟩`, and that `d` is the axis. -/
theorem exists_endo_of_periodic {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hp : ∀ u t : V, fOf M' u = fOf M' (u + fOf M' t)) :
    ∃ d : V, d ≠ 0 ∧ M'.IsEndo (A d) := by
  have hper : ∀ (a : ZMod 3) (u t : V), fOf M' (u + smul a (fOf M' t)) = fOf M' u := by
    intro a u t
    rcases cases3 a with rfl | rfl | rfl
    · rw [smul_zero_left, add_zero]
    · rw [smul_one_left]; exact (hp u t).symm
    · rw [smul_two, ← add_assoc, ← hp (u + fOf M' t) t, ← hp u t]
  have hB : ∀ s t : V, lam (fOf M' s) (fOf M' t) = 0 := by
    intro s t
    by_contra hne
    have hconst : ∀ u : V, fOf M' u = fOf M' 0 := by
      intro u
      obtain ⟨a, b, hab⟩ := lines_meet hne 0 u
      have e1 := hper a 0 s
      rw [hab, hper b u t] at e1
      exact e1
    rw [hconst s, hconst t] at hne
    exact hne (lam_self _)
  by_cases hz : ∀ u : V, fOf M' u = 0
  · exact exists_endo_of_const htr hz
  · simp only [not_forall] at hz
    obtain ⟨t₀, ht₀⟩ := hz
    refine ⟨fOf M' t₀, ht₀, isEndo_A' htr fun w ↦ ?_⟩
    rw [A_eq_self (hB t₀ w), A_eq_add]
    exact (hper (lam (fOf M' t₀) w) w t₀).symm

/-! ### Reducing the target laws

Every target below lands in one of the four shapes above.  Two intermediate forms do most of the
work: the *key identity* `f (f u - u) = -u`, which is `hstep` in disguise, and a law whose right
side does not mention its bound variable at all, which forces the whole row to be constant. -/

/-- The diagonal term is affine in `x`, with slope one: `x ◇ (x ◇ x) = x + f (f 0)`. -/
theorem diag_eq {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v)) (x : V) :
    M'.op x (M'.op x x) = x + fOf M' (fOf M' 0) := by
  have hop := op_eq htr
  rw [hop x x, sub_self, hop, add_sub_cancel_left]

/-- **The key identity implies `hstep`.**  `u + h u = f u + u + u = f u - u`, so `f` at that point
is `-u` and adding the argument back gives `h u`. -/
theorem hstep_of_key {M' : Magma V} (key : ∀ u : V, fOf M' (fOf M' u - u) = -u) (u : V) :
    hOf M' (u + hOf M' u) = hOf M' u := by
  have hfin : fOf M' (u + hOf M' u) = -u := by
    rw [add_comm u (hOf M' u), hOf_eq, add_add_eq_sub]
    exact key u
  show fOf M' (u + hOf M' u) + (u + hOf M' u) = hOf M' u
  rw [hfin]
  exact neg_add_cancel_left' u (hOf M' u)

/-- **A law with a free right-hand side forces a constant row.**  If some fixed `a` has
`x ◇ a = x + k` for every `x`, then reading it at `x = a - u` gives `f u = k`. -/
theorem const_of_free {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v)) {a k : V}
    (hL : ∀ x : V, M'.op x a = x + k) (u : V) : fOf M' u = k := by
  have h := hL (a - u)
  rw [op_eq htr, sub_sub_self'] at h
  exact cancel_left' h

/-- **Law 1073 forces `hstep`.**  Instantiating `x = y ◇ ((x ◇ (x ◇ x)) ◇ y)` at `y = 0` and
`x = -u - k` gives `f (f u - u) = -u - k`; at `u = 0` that reads `k = -k`, so `k = 0` because two
is invertible mod three. -/
theorem hstep_1073 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law1073) (u : V) :
    hOf M' (u + hOf M' u) = hOf M' u := by
  have hE : @Equation1073 V M' := (@Law1073.models_iff V M').mp hL
  have hop := op_eq htr
  have key : ∀ u : V, fOf M' (fOf M' u - u) = -u - fOf M' (fOf M' 0) := by
    intro u
    have hx := hE (-u - fOf M' (fOf M' 0)) 0
    rw [diag_eq htr, neg_sub_add, hop (-u) 0, zero_sub_neg, hop 0, negadd_sub_zero,
      zero_add] at hx
    exact hx.symm
  have hk : fOf M' (fOf M' 0) = 0 := by
    have h0 := key 0
    rw [sub_zero, neg_zero, zero_sub] at h0
    exact eq_zero_of_eq_neg h0
  exact hstep_of_key (fun u ↦ by rw [key u, hk, sub_zero]) u

/-- The constant is forced to vanish by a three-step chain: `h (-h 0) = h 0 + k`, then
`h (-k) = h 0 + 2k`, then `h (-h 0) = h 0 + 3k = h 0`.  Comparing the first and the last gives
`k = 0`.  This step is not vacuous -- dropping it admits twenty-four extra operations for each
nonzero `k`, none of which is self-consistent. -/
theorem const_eq_zero {H : V → V} {k : V} (hk : H (H 0) = H 0 + k)
    (hcond : ∀ u, H (u - H u) = H u + k) : k = 0 := by
  have i := hcond 0
  have ii := hcond (H 0)
  rw [hk, sub_add_self] at ii
  have iii := hcond (-k)
  rw [ii, neg_sub_three, add_three] at iii
  rw [iii] at i
  exact eq_zero_of_add_self i.symm

/-- **Law 4386 forces `hstep`.**  At `y = 0` the law reads `f u + f (-f u) = u + k`, i.e.
`h (u - h u) = h u + k`; the chain above kills `k`, and applying the resulting identity twice
turns the minus into a plus. -/
theorem hstep_4386 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law4386) (u : V) :
    hOf M' (u + hOf M' u) = hOf M' u := by
  have hE : @Equation4386 V M' := (@Law4386.models_iff V M').mp hL
  have hop := op_eq htr
  have key : ∀ u : V, fOf M' u + fOf M' (-fOf M' u) = u + fOf M' (fOf M' 0) := by
    intro u
    have hx := hE u 0
    rw [diag_eq htr, fOf_def, hop (fOf M' u) 0, zero_sub] at hx
    exact hx.symm
  have hcond : ∀ u : V, hOf M' (u - hOf M' u) = hOf M' u + fOf M' (fOf M' 0) := by
    intro u
    have e : u - hOf M' u = -fOf M' u := by rw [hOf_eq]; exact sub_add_left u (fOf M' u)
    rw [e]
    show fOf M' (-fOf M' u) + -fOf M' u = fOf M' u + u + fOf M' (fOf M' 0)
    exact shuffle (key u)
  have hH0 : hOf M' 0 = fOf M' 0 := by rw [hOf_eq, add_zero]
  have hk : hOf M' (hOf M' 0) = hOf M' 0 + fOf M' (fOf M' 0) := by
    rw [hH0, hOf_eq]; exact add_comm _ _
  have hk0 := const_eq_zero hk hcond
  have hcond' : ∀ u : V, hOf M' (u - hOf M' u) = hOf M' u := by
    intro u; rw [hcond u, hk0, add_zero]
  have h2 := hcond' (u - hOf M' u)
  rw [hcond' u, sub_sub_eq_add] at h2
  exact h2

/-- **Law 14 forces `hstep`**, through `1073`: `x = y ◇ (x ◇ y)` at `y = x` says the diagonal term
is the identity, and the law again at `x ◇ (x ◇ x)` is then `1073`. -/
theorem hstep_14 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law14) (u : V) :
    hOf M' (u + hOf M' u) = hOf M' u := by
  have hE : @Equation14 V M' := (@Law14.models_iff V M').mp hL
  refine hstep_1073 htr ((@Law1073.models_iff V M').mpr ?_) u
  intro x y
  rw [← hE x x]
  exact hE x y

/-- **Law 4458 forces `hstep`**, through `4386`: substituting `y = x` in
`x ◇ (y ◇ x) = (z ◇ y) ◇ z` is exactly `4386`. -/
theorem hstep_4458 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law4458) (u : V) :
    hOf M' (u + hOf M' u) = hOf M' u := by
  have hE : @Equation4458 V M' := (@Law4458.models_iff V M').mp hL
  exact hstep_4386 htr ((@Law4386.models_iff V M').mpr fun x y ↦ hE x x y) u

/-- **Law 1519 forces the key identity.**  `x = (y ◇ y) ◇ (x ◇ (y ◇ y))` at `y = 0` and
`x = f 0 - u` reads `f 0 - u = f 0 + f (f u - u)`. -/
theorem hstep_1519 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law1519) (u : V) :
    hOf M' (u + hOf M' u) = hOf M' u := by
  have hE : @Equation1519 V M' := (@Law1519.models_iff V M').mp hL
  have hop := op_eq htr
  refine hstep_of_key (fun u ↦ ?_) u
  have h := hE (fOf M' 0 - u) 0
  simp only [fOf_def] at h
  rw [hop (fOf M' 0 - u) (fOf M' 0), sub_sub_self', hop (fOf M' 0), arg_1519] at h
  exact neg_of_sub h

/-- **Law 3472 forces the key identity**, by the same computation read at `x = 0`,
`y = f 0 + u`. -/
theorem hstep_3472 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law3472) (u : V) :
    hOf M' (u + hOf M' u) = hOf M' u := by
  have hE : @Equation3472 V M' := (@Law3472.models_iff V M').mp hL
  have hop := op_eq htr
  refine hstep_of_key (fun u ↦ ?_) u
  have h := hE 0 (fOf M' 0 + u)
  simp only [fOf_def] at h
  rw [hop (fOf M' 0) (fOf M' 0 + u), add_sub_cancel_left, hop (fOf M' 0 + u), arg_3472] at h
  exact neg_of_add h

/-- **Law 3272 forces the shifted step.**  It is `3472` with the two outer arguments swapped, and
that swap is exactly what shifts the step by `h 0`: at `y = 0`, `x = f 0 - w` the law says
`f (f 0 - w + f w) = f 0 - w + f 0`, which is `h (w + h w + h 0) = h w`. -/
theorem hstepc_3272 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law3272) (w : V) :
    hOf M' (w + hOf M' w + hOf M' 0) = hOf M' w := by
  have hE : @Equation3272 V M' := (@Law3272.models_iff V M').mp hL
  have hop := op_eq htr
  have h := hE (fOf M' 0 - w) 0
  simp only [fOf_def] at h
  rw [op_self htr, hop (fOf M' 0 - w) (fOf M' 0), sub_sub_self'] at h
  have hw : hOf M' w = fOf M' w + w := rfl
  have h0 : hOf M' 0 = fOf M' 0 + 0 := rfl
  rw [hw, h0, arg_3272 w (fOf M' w) (fOf M' 0), hOf_eq, ← h, fin_3272]

/-- **Law 3323 forces periodicity.**  `x ◇ y = x ◇ (y ◇ (z ◇ z))` at `x = 0`, `y = u`,
`z = t + u - f 0` says `f u = f (u + f t)`. -/
theorem periodic_3323 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law3323) (u t : V) :
    fOf M' u = fOf M' (u + fOf M' t) := by
  have hE : @Equation3323 V M' := (@Law3323.models_iff V M').mp hL
  have hop := op_eq htr
  have h := hE 0 u (t + u - fOf M' 0)
  rw [op_self htr, sub_add_cancel', hop u (t + u), add_sub_self'] at h
  simpa only [fOf_def] using h

/-- **Law 4272 forces the row to be a translation.**  Its left side is `x + f (f 0)`, free of the
second variable, so at `y = 0` and `x = u - f 0` it reads `f u = u + (f (f 0) - f 0)`. -/
theorem transl_4272 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law4272) (u : V) :
    fOf M' u = u + (fOf M' (fOf M' 0) - fOf M' 0) := by
  have hE : @Equation4272 V M' := (@Law4272.models_iff V M').mp hL
  have h := hE (u - fOf M' 0) 0
  rw [diag_eq htr, op_self htr, sub_add_cancel'] at h
  simp only [fOf_def] at h
  rw [← h, sub_add_comm']

/-! Five laws say outright that `x ◇ a` does not depend on `a`, and each of them forces the row to
be constant through `const_of_free`; they differ only in which closed term plays the part of `a`
and whether the left side is `x ◇ x` or `x ◇ (x ◇ x)`. -/

theorem const_310 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law310) (u : V) : fOf M' u = fOf M' 0 :=
  have hE : @Equation310 V M' := (@Law310.models_iff V M').mp hL
  const_of_free htr (fun x ↦ (hE x 0).symm.trans (op_self htr x)) u

theorem const_3262 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law3262) (u : V) : fOf M' u = fOf M' 0 :=
  have hE : @Equation3262 V M' := (@Law3262.models_iff V M').mp hL
  const_of_free htr (fun x ↦ (hE x 0).symm.trans (op_self htr x)) u

theorem const_3465 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law3465) (u : V) : fOf M' u = fOf M' 0 :=
  have hE : @Equation3465 V M' := (@Law3465.models_iff V M').mp hL
  const_of_free htr (fun x ↦ (hE x 0).symm.trans (op_self htr x)) u

theorem const_3466 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law3466) (u : V) : fOf M' u = fOf M' 0 :=
  have hE : @Equation3466 V M' := (@Law3466.models_iff V M').mp hL
  const_of_free htr (fun x ↦ (hE x 0 0).symm.trans (op_self htr x)) u

theorem const_4270 {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v))
    (hL : @satisfies _ V M' Law4270) (u : V) : fOf M' u = fOf M' (fOf M' 0) :=
  have hE : @Equation4270 V M' := (@Law4270.models_iff V M').mp hL
  const_of_free htr (fun x ↦ (hE x 0).symm.trans (diag_eq htr x)) u

/-! ### The certificate -/

/-- **The transvection certificate.**  A source model whose only automorphisms are the
translations, and a target law that hands every translation-invariant operation a transvection:
the transported model would have to have both properties at once. -/
theorem not_structuralFromFin_of_endo {L L' : Law.NatMagmaLaw} (M : Magma V)
    (htrM : ∀ v : V, M.IsEndo ⇑(tr v)) (hAM : ∀ d : V, d ≠ 0 → ¬ M.IsEndo (A d))
    (hsrc : @satisfies _ V M L')
    (hkey : ∀ M' : Magma V, (∀ v : V, M'.IsEndo ⇑(tr v)) → @satisfies _ V M' L →
      ∃ d : V, d ≠ 0 ∧ M'.IsEndo (A d)) :
    ¬ L.StructuralFromFin L' := by
  intro hstruct
  obtain ⟨M', hM', hfwd, hback⟩ := hstruct M hsrc
  have htr : ∀ v : V, M'.IsEndo ⇑(tr v) := fun v ↦ (htrM v).of_definable hfwd
  obtain ⟨d, hd, hA⟩ := hkey M' htr hM'
  have hA' : M'.IsEndo ⇑(Aperm d) := hA
  exact hAM d hd (hA'.of_definable hback)

/-- The `hstep` special case, against the affine order-nine model of `692`. -/
theorem not_structuralFromFin_of_hstep {L L' : Law.NatMagmaLaw}
    (hsrc : @satisfies _ V m692 L')
    (hkey : ∀ M' : Magma V, (∀ v : V, M'.IsEndo ⇑(tr v)) → @satisfies _ V M' L →
      ∀ u : V, hOf M' (u + hOf M' u) = hOf M' u) :
    ¬ L.StructuralFromFin L' :=
  not_structuralFromFin_of_endo m692 m692_endo_tr (fun _ hd ↦ m692_not_endo_A hd) hsrc
    fun M' htr hM' ↦ exists_endo_of_hstep htr (hkey M' htr hM')

/-- The same against the quadratic model of `1488`. -/
theorem not_structuralFromFin_1488 {L : Law.NatMagmaLaw}
    (hkey : ∀ M' : Magma V, (∀ v : V, M'.IsEndo ⇑(tr v)) → @satisfies _ V M' L →
      ∃ d : V, d ≠ 0 ∧ M'.IsEndo (A d)) :
    ¬ L.StructuralFromFin Law1488 :=
  not_structuralFromFin_of_endo m1488 m1488_endo_tr (fun _ hd ↦ m1488_not_endo_A hd) m1488_sat hkey

end E9

/-! ### The cells

Each source below is a law that the affine model satisfies, so the model is a legal starting point;
each target is one of the four laws shown above to force `hstep`.  `StructuralFromFin` is the
strongest of the four structural flavours, so one statement per cell settles all of them.
-/

/-- The affine order-nine model satisfies equation 680. -/
theorem E9.m692_sat_680 : @satisfies _ E9.V E9.m692 Law680 :=
  (@Law680.models_iff E9.V E9.m692).mpr (by decide)

/-- The affine order-nine model satisfies equation 692. -/
theorem E9.m692_sat_692 : @satisfies _ E9.V E9.m692 Law692 :=
  (@Law692.models_iff E9.V E9.m692).mpr (by decide)

/-- The affine order-nine model satisfies equation 1276. -/
theorem E9.m692_sat_1276 : @satisfies _ E9.V E9.m692 Law1276 :=
  (@Law1276.models_iff E9.V E9.m692).mpr (by decide)

/-- The affine order-nine model satisfies equation 1695. -/
theorem E9.m692_sat_1695 : @satisfies _ E9.V E9.m692 Law1695 :=
  (@Law1695.models_iff E9.V E9.m692).mpr (by decide)

/-- The affine order-nine model satisfies equation 1719. -/
theorem E9.m692_sat_1719 : @satisfies _ E9.V E9.m692 Law1719 :=
  (@Law1719.models_iff E9.V E9.m692).mpr (by decide)

theorem Equation14_not_structuralFromFin_Equation680 :
    ¬ Law14.StructuralFromFin Law680 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_680 fun _ htr hL ↦ E9.hstep_14 htr hL

theorem Equation14_not_structuralFromFin_Equation692 :
    ¬ Law14.StructuralFromFin Law692 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_692 fun _ htr hL ↦ E9.hstep_14 htr hL

theorem Equation14_not_structuralFromFin_Equation1276 :
    ¬ Law14.StructuralFromFin Law1276 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1276 fun _ htr hL ↦ E9.hstep_14 htr hL

theorem Equation14_not_structuralFromFin_Equation1695 :
    ¬ Law14.StructuralFromFin Law1695 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1695 fun _ htr hL ↦ E9.hstep_14 htr hL

theorem Equation14_not_structuralFromFin_Equation1719 :
    ¬ Law14.StructuralFromFin Law1719 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1719 fun _ htr hL ↦ E9.hstep_14 htr hL

theorem Equation1073_not_structuralFromFin_Equation680 :
    ¬ Law1073.StructuralFromFin Law680 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_680 fun _ htr hL ↦ E9.hstep_1073 htr hL

theorem Equation1073_not_structuralFromFin_Equation692 :
    ¬ Law1073.StructuralFromFin Law692 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_692 fun _ htr hL ↦ E9.hstep_1073 htr hL

theorem Equation1073_not_structuralFromFin_Equation1276 :
    ¬ Law1073.StructuralFromFin Law1276 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1276 fun _ htr hL ↦ E9.hstep_1073 htr hL

theorem Equation1073_not_structuralFromFin_Equation1695 :
    ¬ Law1073.StructuralFromFin Law1695 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1695 fun _ htr hL ↦ E9.hstep_1073 htr hL

theorem Equation1073_not_structuralFromFin_Equation1719 :
    ¬ Law1073.StructuralFromFin Law1719 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1719 fun _ htr hL ↦ E9.hstep_1073 htr hL

theorem Equation4386_not_structuralFromFin_Equation680 :
    ¬ Law4386.StructuralFromFin Law680 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_680 fun _ htr hL ↦ E9.hstep_4386 htr hL

theorem Equation4386_not_structuralFromFin_Equation692 :
    ¬ Law4386.StructuralFromFin Law692 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_692 fun _ htr hL ↦ E9.hstep_4386 htr hL

theorem Equation4386_not_structuralFromFin_Equation1276 :
    ¬ Law4386.StructuralFromFin Law1276 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1276 fun _ htr hL ↦ E9.hstep_4386 htr hL

theorem Equation4386_not_structuralFromFin_Equation1695 :
    ¬ Law4386.StructuralFromFin Law1695 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1695 fun _ htr hL ↦ E9.hstep_4386 htr hL

theorem Equation4386_not_structuralFromFin_Equation1719 :
    ¬ Law4386.StructuralFromFin Law1719 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1719 fun _ htr hL ↦ E9.hstep_4386 htr hL

theorem Equation4458_not_structuralFromFin_Equation680 :
    ¬ Law4458.StructuralFromFin Law680 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_680 fun _ htr hL ↦ E9.hstep_4458 htr hL

theorem Equation4458_not_structuralFromFin_Equation692 :
    ¬ Law4458.StructuralFromFin Law692 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_692 fun _ htr hL ↦ E9.hstep_4458 htr hL

theorem Equation4458_not_structuralFromFin_Equation1276 :
    ¬ Law4458.StructuralFromFin Law1276 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1276 fun _ htr hL ↦ E9.hstep_4458 htr hL

theorem Equation4458_not_structuralFromFin_Equation1695 :
    ¬ Law4458.StructuralFromFin Law1695 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1695 fun _ htr hL ↦ E9.hstep_4458 htr hL

theorem Equation4458_not_structuralFromFin_Equation1719 :
    ¬ Law4458.StructuralFromFin Law1719 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1719 fun _ htr hL ↦ E9.hstep_4458 htr hL

theorem Equation1519_not_structuralFromFin_Equation1719 :
    ¬ Law1519.StructuralFromFin Law1719 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1719 fun _ htr hL ↦ E9.hstep_1519 htr hL

theorem Equation3472_not_structuralFromFin_Equation1719 :
    ¬ Law3472.StructuralFromFin Law1719 :=
  E9.not_structuralFromFin_of_hstep E9.m692_sat_1719 fun _ htr hL ↦ E9.hstep_3472 htr hL

theorem Equation3272_not_structuralFromFin_Equation1719 :
    ¬ Law3272.StructuralFromFin Law1719 :=
  E9.not_structuralFromFin_of_endo E9.m692 E9.m692_endo_tr (fun _ hd ↦ E9.m692_not_endo_A hd)
    E9.m692_sat_1719 fun _ htr hL ↦ E9.exists_endo_of_hstepc htr (E9.hstepc_3272 htr hL)

theorem Equation310_not_structuralFromFin_Equation1488 :
    ¬ Law310.StructuralFromFin Law1488 :=
  E9.not_structuralFromFin_1488 fun _ htr hL ↦ E9.exists_endo_of_const htr (E9.const_310 htr hL)

theorem Equation3262_not_structuralFromFin_Equation1488 :
    ¬ Law3262.StructuralFromFin Law1488 :=
  E9.not_structuralFromFin_1488 fun _ htr hL ↦ E9.exists_endo_of_const htr (E9.const_3262 htr hL)

theorem Equation3465_not_structuralFromFin_Equation1488 :
    ¬ Law3465.StructuralFromFin Law1488 :=
  E9.not_structuralFromFin_1488 fun _ htr hL ↦ E9.exists_endo_of_const htr (E9.const_3465 htr hL)

theorem Equation3466_not_structuralFromFin_Equation1488 :
    ¬ Law3466.StructuralFromFin Law1488 :=
  E9.not_structuralFromFin_1488 fun _ htr hL ↦ E9.exists_endo_of_const htr (E9.const_3466 htr hL)

theorem Equation4270_not_structuralFromFin_Equation1488 :
    ¬ Law4270.StructuralFromFin Law1488 :=
  E9.not_structuralFromFin_1488 fun _ htr hL ↦ E9.exists_endo_of_const htr (E9.const_4270 htr hL)

theorem Equation4272_not_structuralFromFin_Equation1488 :
    ¬ Law4272.StructuralFromFin Law1488 :=
  E9.not_structuralFromFin_1488 fun _ htr hL ↦ E9.exists_endo_of_transl htr (E9.transl_4272 htr hL)

theorem Equation3323_not_structuralFromFin_Equation1488 :
    ¬ Law3323.StructuralFromFin Law1488 :=
  E9.not_structuralFromFin_1488 fun _ htr hL ↦
    E9.exists_endo_of_periodic htr (E9.periodic_3323 htr hL)

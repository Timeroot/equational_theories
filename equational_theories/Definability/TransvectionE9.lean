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

/-- A transvection commuting with `h` in both senses is an automorphism of the operation. -/
theorem isEndo_A {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v)) {d : V}
    (hD : ∀ u, hOf M' (A d u) = hOf M' u) (hE : ∀ u, A d (hOf M' u) = hOf M' u) :
    M'.IsEndo (A d) := by
  have hop := op_eq htr
  have hf : ∀ w, A d (fOf M' w) = fOf M' (A d w) := by
    intro w
    have e1 : fOf M' w = hOf M' w - w := by rw [hOf_eq, add_sub_self']
    have e2 : fOf M' (A d w) = hOf M' (A d w) - A d w := by rw [hOf_eq, add_sub_self']
    rw [e1, e2, A_sub, hE, hD]
  intro x y
  rw [hop x y, hop (A d x) (A d y), A_add, hf, A_sub]

/-! ### The two target laws both reduce to `hstep`

Neither law mentions the constant `k = f (f 0)` in its reduced form, but for very different
reasons: `1073` kills it in one step, while `4386` needs a three-term chain. -/

/-- The diagonal term is affine in `x`, with slope one: `x ◇ (x ◇ x) = x + f (f 0)`. -/
theorem diag_eq {M' : Magma V} (htr : ∀ v : V, M'.IsEndo ⇑(tr v)) (x : V) :
    M'.op x (M'.op x x) = x + fOf M' (fOf M' 0) := by
  have hop := op_eq htr
  rw [hop x x, sub_self, hop, add_sub_cancel_left]

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
  have key' : ∀ u : V, fOf M' (fOf M' u - u) = -u := by
    intro u; rw [key u, hk, sub_zero]
  have hfin : fOf M' (u + hOf M' u) = -u := by
    rw [add_comm u (hOf M' u), hOf_eq, add_add_eq_sub]
    exact key' u
  show fOf M' (u + hOf M' u) + (u + hOf M' u) = hOf M' u
  rw [hfin]
  exact neg_add_cancel_left' u (hOf M' u)

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

/-! ### The certificate -/

/-- **The transvection certificate.** If the target law forces the shifted row `h` of a
translation-invariant operation to be constant along its own lines, then the target is not
structural from any law that the affine order-nine model of `692` satisfies. -/
theorem not_structuralFromFin_of_hstep {L L' : Law.NatMagmaLaw}
    (hsrc : @satisfies _ V m692 L')
    (hkey : ∀ M' : Magma V, (∀ v : V, M'.IsEndo ⇑(tr v)) → @satisfies _ V M' L →
      ∀ u : V, hOf M' (u + hOf M' u) = hOf M' u) :
    ¬ L.StructuralFromFin L' := by
  intro hstruct
  obtain ⟨M', hM', hfwd, hback⟩ := hstruct m692 hsrc
  have htr : ∀ v : V, M'.IsEndo ⇑(tr v) := fun v ↦ (m692_endo_tr v).of_definable hfwd
  obtain ⟨d, hd, hD, hE⟩ := exists_transvection (hkey M' htr hM')
  have hA : M'.IsEndo ⇑(Aperm d) := isEndo_A htr hD hE
  exact m692_not_endo_A hd (hA.of_definable hback)

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

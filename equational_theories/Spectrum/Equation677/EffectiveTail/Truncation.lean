import equational_theories.Spectrum.Equation677.EffectiveTail.Seeds
import equational_theories.Spectrum.PBD.Cyclic

/-! Arbitrary group fillings of a truncated transversal design. Only the block
models are idempotent. This replaces the coordinate-by-coordinate gluing in PR #6
with the existing design and E677 gluing API. -/
namespace Spectrum.E677.EffectiveTail
open Classical Law Law.MagmaLaw

private theorem model_of_hasModel {n : ℕ} (h : Law677.HasModel n) : Model (Fin n) := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M.op, fun x y => ((@Law677.models_iff _ M).mp hM x y).symm, by simp⟩

/-- Keep `k` complete groups and `h` independently truncated groups. -/
theorem hasTD_truncate {k h q : ℕ} (hD : PBD.HasTD (k+h) q)
    (r : Fin h → ℕ) (hr : ∀ j, r j ≤ q)
    (full : Model (Fin q)) (part : ∀ j, Model (Fin (r j)))
    (small : ∀ n, k ≤ n → n ≤ k+h → Model (Fin n) true) :
    Law677.HasModel (k*q + ∑ j, r j) := by
  obtain ⟨D⟩ := hD
  let e : (Fin k ⊕ Fin h) ≃ Fin (k+h) := finSumFinEquiv
  let T : E63.Transversal (Fin k ⊕ Fin h) (Fin q) (Fin q × Fin q) := {
    coord t i := D.line t (e i)
    pair i j hij x y := by
      have hne : e i ≠ e j := fun he => hij (e.injective he)
      obtain ⟨t, ht⟩ := (D.pair (e i) (e j) hne).surjective (x,y)
      refine ⟨t, ⟨congrArg Prod.fst ht, congrArg Prod.snd ht⟩, ?_⟩
      intro u hu
      exact (D.pair (e i) (e j) hne).injective ((Prod.ext hu.1 hu.2).trans ht.symm) }
  let keep : Fin k ⊕ Fin h → Fin q → Prop := fun i x => match i with
    | .inl _ => True
    | .inr j => x.val < r j
  let A := Σ i, {x // keep i x}
  let er (j : Fin h) : {x // keep (.inr j) x} ≃ Fin (r j) := {
    toFun x := ⟨x.val.val, x.property⟩
    invFun x := ⟨⟨x.val, lt_of_lt_of_le x.isLt (hr j)⟩, x.isLt⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hg : ∀ i, Model {x // (T.restrict keep).group x = i} := by
    intro i
    apply Model.relabel (e := (T.groupEquiv keep i).symm)
    cases i with
    | inl i => exact full.relabel (Equiv.Set.univ (Fin q)).symm
    | inr j => exact (part j).relabel (er j).symm
  have hb : ∀ t, Model ((T.restrict keep).block t) true := by
    intro t
    apply Model.relabel (e := (T.blockEquiv keep t).symm)
    have hlo : k ≤ Fintype.card {i // keep i (T.coord t i)} := by
      let f : Fin k → {i // keep i (T.coord t i)} := fun i => ⟨.inl i, trivial⟩
      have hf : Function.Injective f := fun i j he => Sum.inl.inj (congrArg Subtype.val he)
      simpa using Fintype.card_le_of_injective f hf
    have hhi : Fintype.card {i // keep i (T.coord t i)} ≤ k+h := by
      simpa using Fintype.card_le_of_injective
        (Subtype.val : {i // keep i (T.coord t i)} → Fin k ⊕ Fin h) Subtype.val_injective
    exact (small _ hlo hhi).of_card rfl
  have hm : Model A := design_model (T.restrict keep) hg hb
  apply (hm.relabel (Fintype.equivFinOfCardEq ?_)).hasModel
  change Fintype.card (Σ i : Fin k ⊕ Fin h, {x // keep i x}) = _
  rw [Fintype.card_sigma, Fintype.sum_sum_type]
  have hc (j : Fin h) : Fintype.card {x // keep (.inr j) x} = r j := by
    simpa using Fintype.card_congr (er j)
  have hf (i : Fin k) : Fintype.card {x // keep (.inl i) x} = q := by simp [keep]
  simp only [Fintype.card_eq_nat_card] at hc hf ⊢
  simp only [hc, hf, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The product of primes at most 79, as used by the finite certificate. -/
def P79 : Nat :=
  2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 37 * 41 * 43 * 47 * 53 * 59 * 61 * 67 * 71 * 73 * 79

private theorem primorial_eq : PBD.primorial 80 = P79 := by decide +kernel

/-- The certificate's two-hole rule: blocks have sizes 79, 80, or 81. -/
theorem hasModel_trunc {q s r : Nat} (hg : Nat.gcd q P79 = 1) (hs : s ≤ q) (hr : r ≤ q)
    (hq : Law677.HasModel q) (hmS : Law677.HasModel s) (hmR : Law677.HasModel r) :
    Law677.HasModel (79*q+s+r) := by
  have hpos : 0 < q := by
    by_contra! he
    have : q = 0 := by omega
    subst q
    norm_num [P79] at hg
  have hD : PBD.HasTD 81 q := PBD.HasTD.cyclic hpos (by rwa [primorial_eq])
  have he := hasTD_truncate (k := 79) (h := 2) hD ![s,r]
    (by intro j; fin_cases j <;> assumption) (model_of_hasModel hq)
    (by intro j; fin_cases j; exact model_of_hasModel hmS; exact model_of_hasModel hmR)
    (fun n hlo hhi => by
      have : n = 79 ∨ n = 80 ∨ n = 81 := by omega
      rcases this with rfl | rfl | rfl
      · exact idem79
      · exact E677.idem80
      · exact E677.idem81)
  simpa [Fin.sum_univ_two, Nat.add_assoc] using he
end Spectrum.E677.EffectiveTail

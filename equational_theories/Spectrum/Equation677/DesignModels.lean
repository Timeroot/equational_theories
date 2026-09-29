import equational_theories.Spectrum.Equation677.Gluing
import equational_theories.Spectrum.PBD.Transversal

/-! E677 models from a transversal design with one truncated group.
Only the two transversal block models must be idempotent. -/
namespace Spectrum.E677
open Classical Law Law.MagmaLaw

def select {Q : Type*} {k : ℕ} (s : Set Q) : Option (Fin k) → Q → Prop
  | none, x => x ∈ s
  | some _, _ => True

theorem transversal_oneHole {Q T : Type*} [Fintype Q] {k : ℕ}
    (D : E63.Transversal (Option (Fin k)) Q T)
    (s : Set Q) (g : Model Q) (r : Model s)
    (hk : Model (Fin k) true) (hk1 : Model (Fin (k+1)) true) :
    Model (Fin (k * Fintype.card Q + Fintype.card s)) := by
  let keep := select (k := k) s
  let A := Σ i, {x // keep i x}
  have hg : ∀ i, Model {x // (D.restrict keep).group x = i} := by
    intro i
    apply Model.relabel (e := (D.groupEquiv keep i).symm)
    cases i with
    | none => exact r
    | some i => exact g.relabel (Equiv.Set.univ Q).symm
  have hb : ∀ t, Model ((D.restrict keep).block t) true := by
    intro t
    apply Model.relabel (e := (D.blockEquiv keep t).symm)
    by_cases he : D.coord t none ∈ s
    · apply hk1.of_card
      have hh : (fun i => keep i (D.coord t i)) = fun _ => True := by
        funext i
        cases i <;> simp [keep, select, he]
      simp [hh, Fintype.card_option]
    · apply hk.of_card
      let e : {i // keep i (D.coord t i)} ≃ Fin k := {
        toFun := fun i => match i with
          | ⟨some j, _⟩ => j
          | ⟨none, h⟩ => False.elim (he h)
        invFun := fun j => ⟨some j, trivial⟩
        left_inv := by rintro ⟨(_ | j), h⟩; exact (he h).elim; rfl
        right_inv := fun _ => rfl }
      simpa using Fintype.card_congr e
  have hm : Model A := design_model (D.restrict keep) hg hb
  apply hm.relabel
  apply Fintype.equivFinOfCardEq
  change Fintype.card (Σ i : Option (Fin k), {x // keep i x}) = _
  rw [Fintype.card_sigma]
  simp [keep, select, Fintype.sum_option, Nat.add_comm]
  exact Fintype.card_congr (Equiv.refl s)

theorem hasTD_models {k q r : ℕ} (hD : PBD.HasTD (k+1) q)
    (hr : r ≤ q) (g : Model (Fin q)) (h : Model (Fin r))
    (hk : Model (Fin k) true) (hk1 : Model (Fin (k+1)) true) :
    Law677.HasModel (k*q+r) := by
  obtain ⟨D⟩ := hD
  let e : Option (Fin k) ≃ Fin (k+1) := Fintype.equivFinOfCardEq (by simp)
  let T : E63.Transversal (Option (Fin k)) (Fin q) (Fin q × Fin q) := {
    coord t i := D.line t (e i)
    pair i j hij x y := by
      have hne : e i ≠ e j := fun he => hij (e.injective he)
      obtain ⟨t,ht⟩ := (D.pair (e i) (e j) hne).surjective (x,y)
      refine ⟨t, ⟨congrArg Prod.fst ht, congrArg Prod.snd ht⟩, ?_⟩
      intro u hu
      exact (D.pair (e i) (e j) hne).injective ((Prod.ext hu.1 hu.2).trans ht.symm) }
  let s : Set (Fin q) := {x | x.val < r}
  let e' : s ≃ Fin r := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    invFun := fun x => ⟨⟨x.val,lt_of_lt_of_le x.isLt hr⟩,x.isLt⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hh := (transversal_oneHole T s g (h.relabel e'.symm) hk hk1).hasModel
  convert hh using 1
  simp only [Fintype.card_fin]
  congr 1
  rw [Fintype.card_eq_nat_card, Nat.card_congr e', Nat.card_fin]

end Spectrum.E677

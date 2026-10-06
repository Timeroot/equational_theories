import equational_theories.Spectrum.Equation63.ExtendedDesign

/-! Adjoin one common point to every group of a group-divisible design.
The enlarged groups and original transversal blocks form a pairwise balanced
design. Idempotent fillings agree at their common singleton intersections. -/
namespace Spectrum.E63
open Classical
variable {A I B : Type*}

def Design.pointBlock (D : Design A I B) : I ⊕ B → Set (Option A)
  | .inl i => {x | ∀ a, x = some a → D.group a = i}
  | .inr b => {x | ∃ a, x = some a ∧ a ∈ D.block b}

@[simp] theorem Design.none_pointBlock_left (D : Design A I B) (i : I) :
    none ∈ D.pointBlock (.inl i) := by simp [pointBlock]
@[simp] theorem Design.some_pointBlock_left (D : Design A I B) (i : I) (a : A) :
    some a ∈ D.pointBlock (.inl i) ↔ D.group a = i := by simp [pointBlock]
@[simp] theorem Design.none_pointBlock_right (D : Design A I B) (b : B) :
    none ∉ D.pointBlock (.inr b) := by simp [pointBlock]
@[simp] theorem Design.some_pointBlock_right (D : Design A I B) (b : B) (a : A) :
    some a ∈ D.pointBlock (.inr b) ↔ a ∈ D.block b := by simp [pointBlock]

noncomputable def Design.adjoinPoint (D : Design A I B) :
    Design (Option A) (Option A) (I ⊕ B) where
  group := id
  block := D.pointBlock
  transverse _ := fun _ _ _ _ h => h
  pair x y h := by
    change x ≠ y at h
    cases x with
    | none =>
      cases y with
      | none => exact (h rfl).elim
      | some y =>
        refine ⟨.inl (D.group y), by simp, ?_⟩
        intro z hz
        cases z with
        | inl i => exact congrArg Sum.inl ((D.some_pointBlock_left i y).mp hz.2).symm
        | inr b => exact (D.none_pointBlock_right b hz.1).elim
    | some x =>
      cases y with
      | none =>
        refine ⟨.inl (D.group x), by simp, ?_⟩
        intro z hz
        cases z with
        | inl i => exact congrArg Sum.inl ((D.some_pointBlock_left i x).mp hz.1).symm
        | inr b => exact (D.none_pointBlock_right b hz.2).elim
      | some y =>
        by_cases hg : D.group x = D.group y
        · refine ⟨.inl (D.group x), by simp [hg], ?_⟩
          intro z hz
          cases z with
          | inl i => exact congrArg Sum.inl ((D.some_pointBlock_left i x).mp hz.1).symm
          | inr b =>
            have hx := (D.some_pointBlock_right b x).mp hz.1
            have hy := (D.some_pointBlock_right b y).mp hz.2
            exact (h (congrArg some (D.transverse b hx hy hg))).elim
        · obtain ⟨b, hb, hu⟩ := D.pair x y hg
          refine ⟨.inr b, by simpa using hb, ?_⟩
          intro z hz
          cases z with
          | inl i =>
            exact (hg (((D.some_pointBlock_left i x).mp hz.1).trans
              ((D.some_pointBlock_left i y).mp hz.2).symm)).elim
          | inr c => exact congrArg Sum.inr (hu c (by simpa using hz))

noncomputable def Design.pointGroupEquiv (D : Design A I B) (i : I) :
    (D.pointBlock (.inl i)) ≃ Option {x // D.group x = i} where
  toFun p := match p with
    | ⟨none, _⟩ => none
    | ⟨some a, h⟩ => some ⟨a, (D.some_pointBlock_left i a).mp h⟩
  invFun p := match p with
    | none => ⟨none, D.none_pointBlock_left i⟩
    | some a => ⟨some a.val, (D.some_pointBlock_left i a).mpr a.property⟩
  left_inv := by rintro ⟨(_ | a),h⟩ <;> rfl
  right_inv := by rintro (_ | ⟨a,h⟩) <;> rfl

noncomputable def Design.pointBlockEquiv (D : Design A I B) (b : B) :
    (D.pointBlock (.inr b)) ≃ D.block b where
  toFun p := match p with
    | ⟨none, h⟩ => False.elim (D.none_pointBlock_right b h)
    | ⟨some a, h⟩ => ⟨a, (D.some_pointBlock_right b a).mp h⟩
  invFun p := ⟨some p.val, p.val, rfl, p.property⟩
  left_inv := by
    rintro ⟨(_ | a),h⟩
    · exact (D.none_pointBlock_right b h).elim
    · rfl
  right_inv := fun _ => rfl

/-- Fill every group with one extra point, identifying all extra points. -/
theorem Design.pointed_idempotent_model [Finite A] (D : Design A I B)
    (hg : ∀ i, Model (Option {x // D.group x = i}) true)
    (hb : ∀ b, Model (D.block b) true) : Model (Option A) true := by
  apply D.adjoinPoint.idempotent_model
  · intro x
    change Model {z : Option A // z = x} true
    exact ⟨fun _ _ => ⟨x,rfl⟩, fun a _ => Subtype.ext a.property.symm,
      fun _ a => Subtype.ext a.property.symm⟩
  · intro j
    cases j with
    | inl i => exact (hg i).relabel (D.pointGroupEquiv i).symm
    | inr b => exact (hb b).relabel (D.pointBlockEquiv b).symm

/-- A truncated transversal design with a common extra point. -/
theorem Transversal.wide_pointed_models {k q r : ℕ} {T : Type*} [Fintype T]
    (D : Transversal (Option (Fin k)) (Fin q) T) (hr : r ≤ q)
    (g : Model (Fin (q+1)) true) (h : Model (Fin (r+1)) true)
    (hk : Model (Fin k) true) (hk1 : Model (Fin (k+1)) true) :
    Model (Fin (k*q+r+1)) true := by
  let s : Set (Fin q) := {x | x.val < r}
  let e : s ≃ Fin r := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    invFun := fun x => ⟨⟨x.val,lt_of_lt_of_le x.isLt hr⟩,x.isLt⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let keep := wideSelect (k := k) s
  let A := Σ i, {x // keep i x}
  have hg : ∀ i, Model (Option {x // (D.restrict keep).group x = i}) true := by
    intro i
    cases i with
    | none =>
      apply h.of_card
      rw [Fintype.card_option, Fintype.card_congr (D.groupEquiv keep none)]
      simp only [keep,wideSelect]
      rw [Fintype.card_eq_nat_card]
      change Nat.card s + 1 = r + 1
      rw [Nat.card_congr e, Nat.card_fin]
    | some i =>
      apply g.of_card
      rw [Fintype.card_option, Fintype.card_congr (D.groupEquiv keep (some i))]
      simp [keep, wideSelect]
  have hb : ∀ t, Model ((D.restrict keep).block t) true := by
    intro t
    apply Model.relabel (e := (D.blockEquiv keep t).symm)
    by_cases he : D.coord t none ∈ s
    · apply hk1.of_card
      have hh : (fun i => keep i (D.coord t i)) = fun _ => True := by
        funext i
        cases i <;> simp [keep, wideSelect, he]
      simp [hh, Fintype.card_option]
    · apply hk.of_card
      let ee : {i // keep i (D.coord t i)} ≃ Fin k := {
        toFun := fun i => match i with
          | ⟨some j, _⟩ => j
          | ⟨none, h⟩ => False.elim (he h)
        invFun := fun j => ⟨some j, trivial⟩
        left_inv := by rintro ⟨(_ | j), h⟩; exact (he h).elim; rfl
        right_inv := fun _ => rfl }
      simpa using Fintype.card_congr ee
  have hm : Model (Option A) true := (D.restrict keep).pointed_idempotent_model hg hb
  apply hm.relabel
  apply Fintype.equivFinOfCardEq
  rw [Fintype.card_option]
  change Fintype.card (Σ i : Option (Fin k), {x // keep i x}) + 1 = _
  rw [Fintype.card_sigma]
  have hc : Nat.card s = r := by rw [Nat.card_congr e, Nat.card_fin]
  simp only [keep, wideSelect, Fintype.sum_option, Fintype.card_subtype_true,
    Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Fintype.card_eq_nat_card]
  change Nat.card s + k*q+1 = k*q+r+1
  rw [hc]
  omega

theorem HasTD.pointed_models {q r : ℕ} (D : HasTD q) (hr : r ≤ q)
    (g : Model (Fin (q+1)) true) (h : Model (Fin (r+1)) true) :
    Model (Fin (7*q+r+1)) true := by
  obtain ⟨D⟩ := D
  exact D.wide_pointed_models hr g h idem7 idem8

end Spectrum.E63

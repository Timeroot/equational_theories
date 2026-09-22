import equational_theories.Spectrum.Equation66
import Mathlib.Data.Fintype.Card

/-! # Semisymmetric loops and their Mendelsohn systems -/

open Classical
namespace Spectrum

structure SemisymmetricLoop (Q : Type*) where
  op : Q → Q → Q
  unit : Q
  square : ∀ x, op x x = unit
  left_unit : ∀ x, op unit x = x
  right_unit : ∀ x, op x unit = x
  semi : ∀ x y, op y (op x y) = x

namespace SemisymmetricLoop
variable {Q : Type*} (L : SemisymmetricLoop Q)

@[implicit_reducible] def magma : Magma Q := ⟨L.op⟩

theorem equation887 : @Equation887 Q L.magma := by
  intro x y z
  change x = L.op y (L.op (L.op x y) (L.op z z))
  rw [L.square, L.right_unit, L.semi]

theorem col_inj (y : Q) : Function.Injective (fun x => L.op x y) := by
  intro x z h
  simpa only [L.semi] using congrArg (L.op y) h

theorem semi' (x y : Q) : L.op (L.op x y) x = y := by
  simpa only [L.semi] using L.semi y (L.op x y)

theorem row_inj (x : Q) : Function.Injective (L.op x) := by
  intro y z h
  simpa only [L.semi'] using congrArg (fun w => L.op w x) h

abbrev Points := {x : Q // x ≠ L.unit}

noncomputable def removeOp (x y : L.Points) : L.Points :=
  if h : x = y then x else
    ⟨L.op x.val y.val, fun he => h (Subtype.ext ((L.row_inj x.val)
      (he.trans (L.square x.val).symm)).symm)⟩

noncomputable def remove : Mendelsohn L.Points where
  op := L.removeOp
  idem x := by simp [removeOp]
  semi x y := by
    by_cases h : x = y
    · subst y; simp [removeOp]
    have hxy : L.op x.val y.val ≠ y.val := by
      intro e
      exact x.property ((L.col_inj y.val) (e.trans (L.left_unit y.val).symm))
    apply Subtype.ext
    simp only [removeOp, dif_neg h]
    split
    · rename_i he
      exact False.elim (hxy (congrArg Subtype.val he).symm)
    · exact L.semi x.val y.val

/-- The finite E887 identity supplies cancellation, a common square, and a unit. -/
def ofEquation887 [Finite Q] [Magma Q] (h : Equation887 Q) (a : Q) :
    SemisymmetricLoop Q := by
  have law (x y z : Q) : y ◇ ((x ◇ y) ◇ (z ◇ z)) = x := (h x y z).symm
  have hinj (y : Q) : Function.Injective (fun x : Q => y ◇ x) := by
    apply (Finite.injective_iff_surjective).mpr
    intro x
    exact ⟨(x ◇ y) ◇ (a ◇ a), law x y a⟩
  have cinj (y : Q) : Function.Injective (fun x : Q => x ◇ y) := by
    intro x z e
    simpa only [law] using congrArg (fun w => y ◇ (w ◇ (a ◇ a))) e
  have sq (z : Q) : z ◇ z = a ◇ a := by
    apply hinj (a ◇ a)
    apply hinj a
    change a ◇ ((a ◇ a) ◇ (z ◇ z)) = a ◇ ((a ◇ a) ◇ (a ◇ a))
    rw [law, law]
  have ru (x : Q) : x ◇ (a ◇ a) = x := by
    have hh := law x x a
    rw [sq x, sq (a ◇ a)] at hh
    exact hh
  have semi (x y : Q) : y ◇ (x ◇ y) = x := by
    simpa only [ru] using law x y a
  have lu (x : Q) : (a ◇ a) ◇ x = x := by
    apply hinj x
    change x ◇ ((a ◇ a) ◇ x) = x ◇ x
    rw [semi, sq x]
  exact ⟨fun x y => x ◇ y, a ◇ a, sq, lu, ru, semi⟩

end SemisymmetricLoop

namespace Mendelsohn
variable {Q : Type*} (M : Mendelsohn Q)

theorem row_inj (x : Q) : Function.Injective (M.op x) := by
  intro y z h
  simpa only [M.semi'] using congrArg (fun w => M.op w x) h

theorem op_ne_left {x y : Q} (h : x ≠ y) : M.op x y ≠ x := by
  intro he
  exact h ((M.row_inj x) (he.trans (M.idem x).symm)).symm

noncomputable def adjoinOp : Option Q → Option Q → Option Q
  | none, y => y
  | some x, none => some x
  | some x, some y => if x = y then none else some (M.op x y)

noncomputable def adjoin : SemisymmetricLoop (Option Q) where
  op := M.adjoinOp
  unit := none
  square x := by cases x <;> simp [adjoinOp]
  left_unit x := rfl
  right_unit x := by cases x <;> rfl
  semi x y := by
    cases x with
    | none => cases y <;> simp [adjoinOp]
    | some x =>
      cases y with
      | none => rfl
      | some y =>
        by_cases h : x = y
        · subst y; simp [adjoinOp]
        · have hn : M.op x y ≠ y := by
            intro e
            have hh := M.semi x y
            rw [e, M.idem] at hh
            exact h hh.symm
          simp [adjoinOp, h, hn.symm, M.semi]

end Mendelsohn

open Law Law.MagmaLaw

theorem models_887 {n : ℕ} (h : n ∈ residues 3 {1,2} {7}) : Law887.HasModel n := by
  by_cases h1 : n = 1
  · subst n; exact hasModel_one Law887
  have hm : n-1 ∈ residues 3 {0,1} {6} := by
    simp only [residues, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton] at h ⊢
    omega
  obtain ⟨M,hM⟩ := models_66 hm
  let D := Mendelsohn.ofEquation66 ((@Law66.models_iff _ M).mp hM)
  exact hasModel_of_card D.adjoin.magma
    ((@Law887.models_iff _ D.adjoin.magma).mpr D.adjoin.equation887)
    (by simp only [Fintype.card_option, Fintype.card_fin]; have := h.1; omega)

theorem orders_887 {n : ℕ} (h : n ∈ Law887.spectrum) : n ∈ residues 3 {1,2} {7} := by
  obtain ⟨hn,M,hM⟩ := h
  let L := @SemisymmetricLoop.ofEquation887 (Fin n) _ M
    ((@Law887.models_iff _ M).mp hM) ⟨0,hn⟩
  letI : Fintype L.Points := Fintype.ofFinite _
  have hc : Fintype.card L.Points = n-1 := by
    change Fintype.card {x : Fin n // x ≠ L.unit} = n-1
    simp
  have hm := L.remove.card_mod_three
  rw [hc] at hm
  have h7 : n ≠ 7 := by
    intro he
    have hc6 : Fintype.card L.Points = 6 := by omega
    have he66 : Law66.HasModel 6 := hasModel_of_card L.remove.magma
      ((@Law66.models_iff _ L.remove.magma).mpr L.remove.equation66) hc6
    have ho := orders_66 (show 6 ∈ Law66.spectrum from ⟨by omega, he66⟩)
    simp [residues] at ho
  simp only [residues, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨hn, by omega, h7⟩

theorem exact_887 : Law887.spectrum = residues 3 {1,2} {7} := by
  ext n
  exact ⟨orders_887, fun h => ⟨h.1, models_887 h⟩⟩

spectrum_assert exact_887 complete
end Spectrum

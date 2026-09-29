import equational_theories.Spectrum.Equation63.Transversal

/-! E677 gluing with arbitrary group fillings. Finite idempotent E677 models
automatically have the distinct-intermediate-arguments property required on
transversal blocks. No multiplication table is enumerated in this proof. -/
namespace Spectrum.E677
open Classical Law Law.MagmaLaw

abbrev Lawful {A : Type*} (op : A → A → A) : Prop :=
  ∀ x y, op y (op x (op (op y x) y)) = x

abbrev Idem {A : Type*} (op : A → A → A) : Prop := ∀ x, op x x = x

theorem injective_left {A : Type*} [Finite A] {op : A → A → A}
    (h : Lawful op) (y : A) : Function.Injective (op y) := by
  apply Finite.injective_iff_surjective.mpr
  intro x
  exact ⟨op x (op (op y x) y), h x y⟩

theorem discrete {A : Type*} [Finite A] {op : A → A → A}
    (h : Lawful op) (hi : Idem op) {x y : A} (hne : x ≠ y) :
    op y x ≠ y ∧ x ≠ op (op y x) y ∧ y ≠ op x (op (op y x) y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    exact hne (injective_left h y (he.trans (hi y).symm))
  · intro he
    have hyx : op y x = x := by simpa only [← he, hi] using h x y
    have hxy : op x y = x := by simpa only [hyx] using he.symm
    have hh := h y x
    rw [hxy, hi, hyx, hi] at hh
    exact hne hh
  · intro he
    have hh := h x y
    rw [← he, hi] at hh
    exact hne hh.symm

theorem design_lawful {A I B : Type*} [Finite A] (D : E63.Design A I B) (g b)
    (hg : ∀ i, Lawful (g i)) (hb : ∀ j, Lawful (b j))
    (hi : ∀ j, Idem (b j)) : Lawful (D.op g b) := by
  intro x y
  by_cases he : D.group x = D.group y
  · let X : {z // D.group z = D.group x} := ⟨x, rfl⟩
    let Y : {z // D.group z = D.group x} := ⟨y, he.symm⟩
    change D.op g b Y (D.op g b X (D.op g b (D.op g b Y X) Y)) = X.val
    rw [D.op_group, D.op_group, D.op_group, D.op_group, hg]
  · let j := D.chosen x y he
    let X : D.block j := ⟨x, (D.chosen_mem x y he).1⟩
    let Y : D.block j := ⟨y, (D.chosen_mem x y he).2⟩
    have hxy : X ≠ Y := fun h => he (congrArg D.group (congrArg Subtype.val h))
    have hd := discrete (hb j) (hi j) hxy
    change D.op g b Y (D.op g b X (D.op g b (D.op g b Y X) Y)) = X.val
    rw [D.op_block _ _ _ _ _ hxy.symm, D.op_block _ _ _ _ _ hd.1,
      D.op_block _ _ _ _ _ hd.2.1, D.op_block _ _ _ _ _ hd.2.2, hb]

/-- Existence with optional idempotence on a specified carrier. -/
def Model (A : Type*) (idem : Bool := false) : Prop :=
  ∃ op : A → A → A, Lawful op ∧ (idem = true → Idem op)

theorem Model.relabel {A C : Type*} {idem : Bool} (h : Model A idem) (e : A ≃ C) :
    Model C idem := by
  obtain ⟨op, hl, hi⟩ := h
  refine ⟨fun x y => e (op (e.symm x) (e.symm y)), ?_, ?_⟩
  · intro x y
    simp only [Equiv.symm_apply_apply, hl, Equiv.apply_symm_apply]
  · intro he x
    simp only [hi he, Equiv.apply_symm_apply]

theorem Model.of_card {A : Type*} [Fintype A] {n : ℕ} {idem : Bool}
    (h : Model (Fin n) idem) (hc : Fintype.card A = n) : Model A idem :=
  h.relabel (Fintype.equivFinOfCardEq hc).symm

theorem Model.hasModel {n : ℕ} {idem : Bool} (h : Model (Fin n) idem) :
    Law677.HasModel n := by
  obtain ⟨op, hl, _⟩ := h
  exact ⟨⟨op⟩, (@Law677.models_iff _ ⟨op⟩).mpr (fun x y => (hl x y).symm)⟩

theorem Model.forget {A : Type*} (h : Model A true) : Model A := by
  obtain ⟨op,hl,_⟩ := h
  exact ⟨op,hl,by simp⟩

theorem Model.product {A C : Type*} {idem : Bool} (h : Model A idem) (g : Model C idem) :
    Model (A × C) idem := by
  obtain ⟨op,hl,hi⟩ := h
  obtain ⟨op',hl',hi'⟩ := g
  exact ⟨fun x y => (op x.1 y.1, op' x.2 y.2),
    fun x y => Prod.ext (hl x.1 y.1) (hl' x.2 y.2),
    fun he x => Prod.ext (hi he x.1) (hi' he x.2)⟩

theorem design_model {A I B : Type*} [Finite A] (D : E63.Design A I B)
    (hg : ∀ i, Model {x // D.group x = i})
    (hb : ∀ j, Model (D.block j) true) : Model A := by
  choose g hgl hgi using hg
  choose b hbl hbi using hb
  exact ⟨D.op g b, design_lawful D g b hgl hbl (fun j => hbi j rfl), by simp⟩

end Spectrum.E677

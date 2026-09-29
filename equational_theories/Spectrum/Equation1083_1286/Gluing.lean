import equational_theories.Spectrum.Equation63.Transversal

/-! Symbolic group-divisible gluing for E1083 and E1286.
`which = false` selects E1083, `which = true` selects E1286.
Finite idempotent blocks automatically have distinct multiplication arguments
on distinct original inputs. The group fillings need not be idempotent. -/
namespace Spectrum.E1083E1286
open Classical Law Law.MagmaLaw

def Lawful {A : Type*} (which : Bool) (op : A → A → A) : Prop :=
  if which then ∀ x y, op y (op (op (op x y) x) y) = x
  else ∀ x y, op y (op (op x (op y x)) y) = x

abbrev Idem {A : Type*} (op : A → A → A) : Prop := ∀ x, op x x = x

theorem injective_left {A : Type*} [Finite A] {which : Bool} {op : A → A → A}
    (h : Lawful which op) (y : A) : Function.Injective (op y) := by
  apply Finite.injective_iff_surjective.mpr
  intro x
  cases which
  · exact ⟨op (op x (op y x)) y, h x y⟩
  · exact ⟨op (op (op x y) x) y, h x y⟩

theorem discrete1083 {A : Type*} [Finite A] {op : A → A → A}
    (h : Lawful false op) (hi : Idem op) {x y : A} (hne : x ≠ y) :
    x ≠ op y x ∧ op x (op y x) ≠ y ∧ y ≠ op (op x (op y x)) y := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hh := h x y
    rw [← he, hi] at hh
    have hxy : op x y = x := injective_left h y (hh.trans he)
    have hh' := h y x
    rw [hxy, ← he, hi, hi] at hh'
    exact hne hh'
  · intro he
    have hh := h x y
    rw [he, hi, hi] at hh
    exact hne hh.symm
  · intro he
    have hh := h x y
    rw [← he, hi] at hh
    exact hne hh.symm

theorem discrete1286 {A : Type*} [Finite A] {op : A → A → A}
    (h : Lawful true op) (hi : Idem op) {x y : A} (hne : x ≠ y) :
    op x y ≠ x ∧ op (op x y) x ≠ y ∧ y ≠ op (op (op x y) x) y := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    exact hne (injective_left h x ((hi x).trans he.symm))
  · intro he
    have hh := h x y
    rw [he, hi, hi] at hh
    exact hne hh.symm
  · intro he
    have hh := h x y
    rw [← he, hi] at hh
    exact hne hh.symm

theorem design_lawful {A I B : Type*} [Finite A] {which : Bool}
    (D : E63.Design A I B) (g b)
    (hg : ∀ i, Lawful which (g i)) (hb : ∀ j, Lawful which (b j))
    (hi : ∀ j, Idem (b j)) : Lawful which (D.op g b) := by
  cases which with
  | false =>
    intro x y
    by_cases he : D.group x = D.group y
    · let X : {z // D.group z = D.group x} := ⟨x, rfl⟩
      let Y : {z // D.group z = D.group x} := ⟨y, he.symm⟩
      change D.op g b Y (D.op g b (D.op g b X (D.op g b Y X)) Y) = X.val
      rw [D.op_group, D.op_group, D.op_group, D.op_group, hg]
    · let j := D.chosen x y he
      let X : D.block j := ⟨x, (D.chosen_mem x y he).1⟩
      let Y : D.block j := ⟨y, (D.chosen_mem x y he).2⟩
      have hxy : X ≠ Y := fun h => he (congrArg D.group (congrArg Subtype.val h))
      have hd := discrete1083 (hb j) (hi j) hxy
      change D.op g b Y (D.op g b (D.op g b X (D.op g b Y X)) Y) = X.val
      rw [D.op_block _ _ _ _ _ hxy.symm, D.op_block _ _ _ _ _ hd.1,
        D.op_block _ _ _ _ _ hd.2.1, D.op_block _ _ _ _ _ hd.2.2, hb]
  | true =>
    intro x y
    by_cases he : D.group x = D.group y
    · let X : {z // D.group z = D.group x} := ⟨x, rfl⟩
      let Y : {z // D.group z = D.group x} := ⟨y, he.symm⟩
      change D.op g b Y (D.op g b (D.op g b (D.op g b X Y) X) Y) = X.val
      rw [D.op_group, D.op_group, D.op_group, D.op_group, hg]
    · let j := D.chosen x y he
      let X : D.block j := ⟨x, (D.chosen_mem x y he).1⟩
      let Y : D.block j := ⟨y, (D.chosen_mem x y he).2⟩
      have hxy : X ≠ Y := fun h => he (congrArg D.group (congrArg Subtype.val h))
      have hd := discrete1286 (hb j) (hi j) hxy
      change D.op g b Y (D.op g b (D.op g b (D.op g b X Y) X) Y) = X.val
      rw [D.op_block _ _ _ _ _ hxy, D.op_block _ _ _ _ _ hd.1,
        D.op_block _ _ _ _ _ hd.2.1, D.op_block _ _ _ _ _ hd.2.2, hb]

def Model (which : Bool) (A : Type*) (idem : Bool := false) : Prop :=
  ∃ op : A → A → A, Lawful which op ∧ (idem = true → Idem op)

variable {which : Bool}

theorem Model.relabel {A C : Type*} {idem : Bool} (h : Model which A idem) (e : A ≃ C) :
    Model which C idem := by
  obtain ⟨op, hl, hi⟩ := h
  refine ⟨fun x y => e (op (e.symm x) (e.symm y)), ?_, ?_⟩
  · cases which <;> intro x y <;>
      simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
        congrArg e (hl (e.symm x) (e.symm y))
  · intro he x
    simp only [hi he, Equiv.apply_symm_apply]

theorem Model.of_card {A : Type*} [Fintype A] {n : ℕ} {idem : Bool}
    (h : Model which (Fin n) idem) (hc : Fintype.card A = n) : Model which A idem :=
  h.relabel (Fintype.equivFinOfCardEq hc).symm

def law (which : Bool) := if which then Law1286 else Law1083

theorem Model.hasModel {n : ℕ} {idem : Bool} (h : Model which (Fin n) idem) :
    (law which).HasModel n := by
  obtain ⟨op, hl, _⟩ := h
  cases which
  · exact ⟨⟨op⟩, (@Law1083.models_iff _ ⟨op⟩).mpr (fun x y => (hl x y).symm)⟩
  · exact ⟨⟨op⟩, (@Law1286.models_iff _ ⟨op⟩).mpr (fun x y => (hl x y).symm)⟩

theorem Model.forget {A : Type*} (h : Model which A true) : Model which A := by
  obtain ⟨op,hl,_⟩ := h
  exact ⟨op,hl,by simp⟩

theorem Model.product {A C : Type*} {idem : Bool}
    (h : Model which A idem) (g : Model which C idem) : Model which (A × C) idem := by
  obtain ⟨op,hl,hi⟩ := h
  obtain ⟨op',hl',hi'⟩ := g
  refine ⟨fun x y => (op x.1 y.1, op' x.2 y.2), ?_,
    fun he x => Prod.ext (hi he x.1) (hi' he x.2)⟩
  cases which <;> exact fun x y => Prod.ext (hl x.1 y.1) (hl' x.2 y.2)

theorem design_model {A I B : Type*} [Finite A] (D : E63.Design A I B)
    (hg : ∀ i, Model which {x // D.group x = i})
    (hb : ∀ j, Model which (D.block j) true) : Model which A := by
  choose g hgl hgi using hg
  choose b hbl hbi using hb
  exact ⟨D.op g b, design_lawful D g b hgl hbl (fun j => hbi j rfl), by simp⟩

end Spectrum.E1083E1286

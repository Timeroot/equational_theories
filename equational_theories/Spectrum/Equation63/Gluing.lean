import equational_theories.Spectrum.Basic
import equational_theories.Equations.All
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Gluing E63 models along a group-divisible design. Only the transversal
blocks must be idempotent; group fillings may have arbitrary diagonals. -/
namespace Spectrum.E63
open Law Law.MagmaLaw Classical

abbrev Lawful {A : Type*} (op : A → A → A) : Prop :=
  ∀ x y, op y (op x (op x y)) = x

abbrev Idem {A : Type*} (op : A → A → A) : Prop := ∀ x, op x x = x

theorem injective_left {A : Type*} [Finite A] {op : A → A → A}
    (h : Lawful op) (x : A) : Function.Injective (op x) := by
  apply (Finite.injective_iff_surjective).mpr
  intro y
  exact ⟨op y (op y x), h y x⟩

theorem discrete {A : Type*} [Finite A] {op : A → A → A}
    (h : Lawful op) (hi : Idem op) {x y : A} (hne : x ≠ y) :
    x ≠ op x y ∧ y ≠ op x (op x y) := by
  constructor
  · intro he
    exact hne ((injective_left h x) ((hi x).trans he))
  · intro he
    have hh := h x y
    rw [← he, hi] at hh
    exact hne hh.symm

/-- A partition and transversal blocks, with a unique block through every
pair from distinct groups. Blocks are represented as predicates. -/
structure Design (A I B : Type*) where
  group : A → I
  block : B → Set A
  transverse : ∀ b, Set.InjOn group (block b)
  pair : ∀ x y, group x ≠ group y → ∃! b, x ∈ block b ∧ y ∈ block b

variable {A I B : Type*}

noncomputable def Design.chosen (D : Design A I B) (x y : A)
    (h : D.group x ≠ D.group y) : B := (D.pair x y h).exists.choose

theorem Design.chosen_mem (D : Design A I B) (x y : A)
    (h : D.group x ≠ D.group y) :
    x ∈ D.block (D.chosen x y h) ∧ y ∈ D.block (D.chosen x y h) :=
  (D.pair x y h).exists.choose_spec

theorem Design.chosen_eq (D : Design A I B) (x y : A)
    (h : D.group x ≠ D.group y) (b : B)
    (hx : x ∈ D.block b) (hy : y ∈ D.block b) : D.chosen x y h = b := by
  obtain ⟨c, hc, hu⟩ := D.pair x y h
  exact (hu _ (D.chosen_mem x y h)).trans (hu _ ⟨hx, hy⟩).symm

noncomputable def Design.op (D : Design A I B)
    (g : ∀ i, {x // D.group x = i} → {x // D.group x = i} → {x // D.group x = i})
    (b : ∀ j, D.block j → D.block j → D.block j) (x y : A) : A :=
  if h : D.group x = D.group y then
    (g (D.group x) ⟨x, rfl⟩ ⟨y, h.symm⟩).val
  else (b (D.chosen x y h) ⟨x, (D.chosen_mem x y h).1⟩
      ⟨y, (D.chosen_mem x y h).2⟩).val

theorem Design.op_group (D : Design A I B) (g b) (i : I)
    (x y : {x // D.group x = i}) :
    D.op g b x y = (g i x y).val := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  subst i
  simp [Design.op, hy]

theorem Design.op_block (D : Design A I B) (g b) (j : B)
    (x y : D.block j) (hne : x ≠ y) :
    D.op g b x y = (b j x y).val := by
  have hg : D.group x.val ≠ D.group y.val := fun he =>
    hne (Subtype.ext (D.transverse j x.property y.property he))
  simp only [Design.op, dif_neg hg]
  have hh := D.chosen_eq x y hg j x.property y.property
  have aux (c : B) (hx : x.val ∈ D.block c) (hy : y.val ∈ D.block c)
      (hc : c = j) : (b c ⟨x.val, hx⟩ ⟨y.val, hy⟩).val = (b j x y).val := by
    subst c
    rfl
  exact aux _ _ _ hh

theorem Design.lawful [Finite A] (D : Design A I B) (g b)
    (hg : ∀ i, Lawful (g i)) (hb : ∀ j, Lawful (b j))
    (hi : ∀ j, Idem (b j)) : Lawful (D.op g b) := by
  intro x y
  by_cases he : D.group x = D.group y
  · let X : {z // D.group z = D.group x} := ⟨x, rfl⟩
    let Y : {z // D.group z = D.group x} := ⟨y, he.symm⟩
    change D.op g b Y (D.op g b X (D.op g b X Y)) = X.val
    rw [D.op_group, D.op_group, D.op_group, hg]
  · let j := D.chosen x y he
    let X : D.block j := ⟨x, (D.chosen_mem x y he).1⟩
    let Y : D.block j := ⟨y, (D.chosen_mem x y he).2⟩
    have hxy : X ≠ Y := fun h => he (congrArg D.group (congrArg Subtype.val h))
    have hd := discrete (hb j) (hi j) hxy
    change D.op g b Y (D.op g b X (D.op g b X Y)) = X.val
    rw [D.op_block _ _ _ _ _ hxy, D.op_block _ _ _ _ _ hd.1,
      D.op_block _ _ _ _ _ hd.2, hb]

/-- Existence with optional idempotence, on a specified finite carrier. -/
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
    Law63.HasModel n := by
  obtain ⟨op, hl, _⟩ := h
  exact ⟨⟨op⟩, (@Law63.models_iff _ ⟨op⟩).mpr (fun x y => (hl x y).symm)⟩

theorem model_of_hasModel {n : ℕ} (h : Law63.HasModel n) : Model (Fin n) := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M.op, fun x y => ((@Law63.models_iff _ M).mp hM x y).symm, by simp⟩

theorem Design.model [Finite A] (D : Design A I B)
    (hg : ∀ i, Model {x // D.group x = i})
    (hb : ∀ j, Model (D.block j) true) : Model A := by
  choose g hgl hgi using hg
  choose b hbl hbi using hb
  exact ⟨D.op g b, D.lawful g b hgl hbl (fun j => hbi j rfl), by simp⟩

end Spectrum.E63

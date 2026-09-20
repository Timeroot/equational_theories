import equational_theories.Definability.CloneTraps
import equational_theories.Definability.Generated.Subset3352

/-!
# A subalgebra obstruction to recovering E3352 from E4408

On this eight-element E3352 model, every term operation satisfying E4408 either
adds an idempotent or preserves one of two sets that the source operation does
not preserve. Either property prevents recovery of the source by a binary term.
The finite dichotomy uses the LRAT certificate checked by `bv_decide`; the model
and compatible relations are checked using kernel `decide`.
-/

open Law Law.MagmaLaw

namespace Definability.Subset3352

local instance : Fintype (BitVec 3) := Fintype.ofEquiv (Fin 8) (BitVec.equivFin (m := 3)).symm.toEquiv

@[implicit_reducible] def source : Magma (BitVec 3) where
  op x y := (![![7, 3, 6, 3, 7, 0, 0, 4],
    ![4, 0, 6, 3, 0, 1, 1, 3],
    ![4, 4, 4, 3, 6, 6, 4, 4],
    ![3, 3, 3, 3, 3, 3, 3, 3],
    ![0, 1, 6, 3, 2, 6, 2, 7],
    ![7, 0, 6, 3, 6, 6, 6, 1],
    ![7, 0, 4, 3, 2, 6, 5, 1],
    ![3, 4, 6, 3, 1, 7, 7, 1]] : Fin 8 → Fin 8 → BitVec 3) x.toFin y.toFin

theorem source_law : @Equation3352 (BitVec 3) source := by decide

theorem source_preserves : ∀ i, Preserves (relation i) source.op := by
  unfold Preserves
  decide

theorem source_invariant : source.IsCloneInvariant
    (fun f => f 3 3 = 3 ∧ ∀ i, Preserves (relation i) f) where
  fst := ⟨rfl, fun _ _ _ _ _ hab _ => hab⟩
  snd := ⟨rfl, fun _ _ _ _ _ _ hcd => hcd⟩
  comp f g hf hg := by
    constructor
    · change source.op (f 3 3) (g 3 3) = 3
      rw [hf.1, hg.1]
      decide
    · intro i a b c d hab hcd
      exact source_preserves i (f a c) (f b d) (g a c) (g b d)
        (hf.2 i a b c d hab hcd) (hg.2 i a b c d hab hcd)

theorem closed_invariant (S : BitVec 3 → Prop) (N : Magma (BitVec 3))
    (hN : Closed S N.op) : N.IsCloneInvariant (Closed S) where
  fst _ _ hx _ := hx
  snd _ _ _ hy := hy
  comp _ _ hf hg x y hx hy := hN _ _ (hf x y hx hy) (hg x y hx hy)

theorem fixed_invariant (x : BitVec 3) (N : Magma (BitVec 3))
    (hN : N.op x x = x) : N.IsCloneInvariant (fun f => f x x = x) where
  fst := rfl
  snd := rfl
  comp f g hf hg := by change N.op (f x x) (g x x) = x; rw [hf, hg, hN]

theorem source_not_closed_left : ¬ Closed (fun x => x ≠ 3) source.op := by
  intro h
  exact h 0 1 (by decide) (by decide) (by decide)

theorem source_not_closed_right : ¬ Closed (fun x => x = 0 ∨ x = 3) source.op := by
  intro h
  have := h 0 0 (Or.inl rfl) (Or.inl rfl)
  contradiction

end Definability.Subset3352

namespace Law.MagmaLaw

open Definability.Subset3352

/-- Four equivalent raw pairs are excluded by this eight-element obstruction. -/
theorem Equation4408_not_termStructuralFromFin_Equation3352_subsets :
    ¬ Law4408.TermStructuralFromFin Law3352 := by
  letI : Fintype (BitVec 3) := Fintype.ofEquiv (Fin 8) (BitVec.equivFin (m := 3)).symm.toEquiv
  intro h
  obtain ⟨N, hN, hf, hb⟩ := h source
    ((@Law3352.models_iff (BitVec 3) source).mpr source_law)
  obtain ⟨hi3, hr⟩ := source_invariant.of_termDefinable hf
  have hn (x : BitVec 3) (hx : source.op x x ≠ x) : N.op x x ≠ x := by
    intro hnx
    exact hx ((fixed_invariant x N hnx).of_termDefinable hb)
  have hl := (@Law4408.models_iff (BitVec 3) N).mp hN
  obtain hc | hc := cover N.op hl hr (hn 0 (by decide)) hi3
    (hn 5 (by decide)) (hn 6 (by decide))
  · exact source_not_closed_left ((closed_invariant _ N hc).of_termDefinable hb)
  · exact source_not_closed_right ((closed_invariant _ N hc).of_termDefinable hb)

/--
info: 'Law.MagmaLaw.Equation4408_not_termStructuralFromFin_Equation3352_subsets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 refute._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms Equation4408_not_termStructuralFromFin_Equation3352_subsets

end Law.MagmaLaw

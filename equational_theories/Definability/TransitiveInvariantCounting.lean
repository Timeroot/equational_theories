import equational_theories.Definability.InvariantFamilyCounting

/-! Law testing with one variable fixed, for any transitive family of automorphisms.
This includes regular actions of noncyclic additive groups. -/

open Law Law.MagmaLaw FreeMagma

namespace Magma.InvariantFamily

variable {A : Type} {k : ℕ}

def PointTest (a : A) (M : Magma A) (L : MagmaLaw (Fin (k + 1))) : Prop :=
  ∀ φ : Fin k → A, @evalInMagma _ _ M (Fin.cons a φ) L.lhs =
    @evalInMagma _ _ M (Fin.cons a φ) L.rhs

instance [Fintype A] [DecidableEq A] (a : A) (M : Magma A)
    (L : MagmaLaw (Fin (k + 1))) : Decidable (PointTest a M L) := by
  unfold PointTest
  infer_instance

theorem eval_endo (M : Magma A) (g : A → A) (hg : M.IsEndo g)
    (φ : Fin k → A) (t : FreeMagma (Fin k)) :
    @evalInMagma _ _ M (fun i => g (φ i)) t = g (@evalInMagma _ _ M φ t) := by
  induction t with
  | Leaf i => rfl
  | Fork l r hl hr =>
    change M.op _ _ = g (M.op _ _)
    rw [hl, hr]
    exact (hg _ _).symm

theorem pointTest_iff_satisfies (a : A) (M : Magma A)
    (moves : A → Equiv.Perm A) (hm : ∀ x, M.IsEndo (moves x))
    (ha : ∀ x, moves x a = x) (L : MagmaLaw (Fin (k + 1))) :
    PointTest a M L ↔ @satisfies _ A M L := by
  constructor
  · intro ht φ
    let g := moves (φ 0)
    let ψ : Fin k → A := fun i => g.symm (φ i.succ)
    have he : φ = fun i : Fin (k + 1) => g ((Fin.cons a ψ : Fin (k + 1) → A) i) := by
      funext i
      cases i using Fin.cases with
      | zero => exact (ha (φ 0)).symm
      | succ i => exact (g.apply_symm_apply (φ i.succ)).symm
    change @evalInMagma _ _ M φ L.lhs = @evalInMagma _ _ M φ L.rhs
    conv_lhs => rw [he]
    conv_rhs => rw [he]
    rw [eval_endo M g (hm (φ 0)), eval_endo M g (hm (φ 0)), ht ψ]
  · intro ht φ
    exact ht (Fin.cons a φ)

end Magma.InvariantFamily

/-- info: 'Magma.InvariantFamily.pointTest_iff_satisfies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.InvariantFamily.pointTest_iff_satisfies

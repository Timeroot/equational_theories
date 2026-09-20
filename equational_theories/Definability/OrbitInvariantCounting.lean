import equational_theories.Definability.TransitiveInvariantCounting

/-! Exact law testing at one representative of each automorphism orbit. -/

open Law Law.MagmaLaw FreeMagma

namespace Magma.InvariantFamily

variable {A I : Type} {k : ℕ}

def OrbitTest (points : I → A) (M : Magma A) (L : MagmaLaw (Fin (k + 1))) : Prop :=
  ∀ i, PointTest (points i) M L

instance [Fintype A] [DecidableEq A] [Fintype I] (points : I → A)
    (M : Magma A) (L : MagmaLaw (Fin (k + 1))) : Decidable (OrbitTest points M L) := by
  unfold OrbitTest
  infer_instance

theorem orbitTest_iff_satisfies (points : I → A) (M : Magma A)
    (index : A → I) (moves : A → Equiv.Perm A)
    (hm : ∀ x, M.IsEndo (moves x)) (ha : ∀ x, moves x (points (index x)) = x)
    (L : MagmaLaw (Fin (k + 1))) : OrbitTest points M L ↔ @satisfies _ A M L := by
  constructor
  · intro ht φ
    let g := moves (φ 0)
    let ψ : Fin k → A := fun i => g.symm (φ i.succ)
    have he : φ = fun i : Fin (k + 1) =>
        g ((Fin.cons (points (index (φ 0))) ψ : Fin (k + 1) → A) i) := by
      funext i
      cases i using Fin.cases with
      | zero => exact (ha (φ 0)).symm
      | succ i => exact (g.apply_symm_apply (φ i.succ)).symm
    change @evalInMagma _ _ M φ L.lhs = @evalInMagma _ _ M φ L.rhs
    conv_lhs => rw [he]
    conv_rhs => rw [he]
    rw [eval_endo M g (hm (φ 0)), eval_endo M g (hm (φ 0)), ht (index (φ 0)) ψ]
  · intro ht i φ
    exact ht (Fin.cons (points i) φ)

end Magma.InvariantFamily

/-- info: 'Magma.InvariantFamily.orbitTest_iff_satisfies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.InvariantFamily.orbitTest_iff_satisfies

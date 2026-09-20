import equational_theories.Definability.CloneTraps
import equational_theories.Definability.Generated.Idempotent1485

/-!
# An idempotent orbit separates E1483 from E1485

The eight-element source has an idempotent at `0` and an automorphism with cycles
`(0 1 2)(3 5 7)`. Both properties persist under binary terms. The generated finite
refutation proves that no operation with these properties satisfies E1485.
All finite calculations and all branches of the refutation use ordinary kernel proofs.
-/

open Law Law.MagmaLaw

namespace Definability.IdempotentOrbit

@[implicit_reducible] def source : Magma (Fin 8) where
  op := ![![0, 3, 1, 0, 3, 1, 4, 4],
          ![2, 1, 5, 4, 5, 1, 4, 2],
          ![7, 0, 2, 0, 7, 4, 4, 2],
          ![4, 1, 1, 4, 1, 1, 4, 4],
          ![7, 3, 5, 0, 6, 1, 4, 2],
          ![2, 4, 2, 4, 2, 4, 4, 2],
          ![4, 4, 4, 4, 4, 4, 4, 4],
          ![0, 0, 4, 0, 0, 4, 4, 4]]

theorem source_law : @Equation1483 (Fin 8) source := by decide

theorem source_cycle : Magma.Equivariant Idempotent1485.cycle source.op := by decide

theorem source_invariant : source.IsCloneInvariant
    (fun f => f 0 0 = 0 ∧ Magma.Equivariant Idempotent1485.cycle f) where
  fst := ⟨rfl, fun _ _ => rfl⟩
  snd := ⟨rfl, fun _ _ => rfl⟩
  comp f g hf hg := by
    constructor
    · change source.op (f 0 0) (g 0 0) = 0
      rw [hf.1, hg.1]
      rfl
    · exact (Magma.Equivariant.isCloneInvariant source_cycle).comp f g hf.2 hg.2

end Definability.IdempotentOrbit

namespace Law.MagmaLaw

theorem Equation1485_not_termDefinableFromFin_Equation1483_idempotentOrbit :
    ¬ Law1485.TermDefinableFromFin Law1483 := by
  apply not_termDefinableFromFin_of_invariant Definability.IdempotentOrbit.source
    ((@Law1483.models_iff (Fin 8) Definability.IdempotentOrbit.source).mpr
      Definability.IdempotentOrbit.source_law)
    Definability.IdempotentOrbit.source_invariant
  intro f hf h
  exact Definability.Idempotent1485.refute f
    (fun x y z => ((@Law1485.models_iff (Fin 8) ⟨f⟩).mp h x y z).symm) hf.2 hf.1

/--
info: 'Law.MagmaLaw.Equation1485_not_termDefinableFromFin_Equation1483_idempotentOrbit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Equation1485_not_termDefinableFromFin_Equation1483_idempotentOrbit

end Law.MagmaLaw

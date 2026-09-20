import equational_theories.Definability.CloneTraps
import equational_theories.Definability.Generated.Relation1482

/-!
# Compatible binary relations separate E1480 from E1482

Each of eight relations is a subalgebra of the square of the source magma.
Binary terms preserve these relations. A complete finite case proof shows that
no operation preserving all eight relations satisfies E1482.
-/

open Law Law.MagmaLaw

namespace Definability.Relation1482

@[implicit_reducible] def source : Magma (Fin 8) where
  op := ![![2, 6, 6, 6, 2, 3, 6, 1],
          ![7, 3, 7, 7, 2, 3, 0, 7],
          ![4, 4, 0, 4, 4, 3, 0, 1],
          ![5, 5, 5, 1, 2, 5, 0, 1],
          ![4, 4, 0, 4, 4, 3, 0, 1],
          ![5, 5, 5, 1, 2, 5, 0, 1],
          ![2, 6, 6, 6, 2, 3, 6, 1],
          ![7, 3, 7, 7, 2, 3, 0, 7]]

theorem source_law : @Equation1480 (Fin 8) source := by decide

theorem source_preserves : ∀ i, Preserves (relation i) source.op := by
  unfold Preserves
  decide

theorem source_invariant : source.IsCloneInvariant
    (fun f => ∀ i, Preserves (relation i) f) where
  fst _ _ _ _ _ hab _ := hab
  snd _ _ _ _ _ _ hcd := hcd
  comp f g hf hg i a b c d hab hcd :=
    source_preserves i (f a c) (f b d) (g a c) (g b d)
      (hf i a b c d hab hcd) (hg i a b c d hab hcd)

end Definability.Relation1482

namespace Law.MagmaLaw

theorem Equation1482_not_termDefinableFromFin_Equation1480_relations :
    ¬ Law1482.TermDefinableFromFin Law1480 := by
  apply not_termDefinableFromFin_of_invariant Definability.Relation1482.source
    ((@Law1480.models_iff (Fin 8) Definability.Relation1482.source).mpr
      Definability.Relation1482.source_law)
    Definability.Relation1482.source_invariant
  intro f hf h
  exact Definability.Relation1482.refute f
    (fun x y => ((@Law1482.models_iff (Fin 8) ⟨f⟩).mp h x y).symm) hf

/--
info: 'Law.MagmaLaw.Equation1482_not_termDefinableFromFin_Equation1480_relations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Equation1482_not_termDefinableFromFin_Equation1480_relations

end Law.MagmaLaw

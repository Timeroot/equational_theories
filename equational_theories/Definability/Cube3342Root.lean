import equational_theories.Definability.Invariant
import equational_theories.Definability.FiniteFlavour
import equational_theories.Definability.Generated.Cube3342RootData

/-! A 27-element E3342 magma with no term-equivalent E3545 operation.
The three-element factor restricts any recoverable operation to a term whose root
separates the variables. On the nine-element factor, every such E3545 operation
omits a value which the original operation can produce from two other values. -/

open FirstOrder Law Law.MagmaLaw
namespace CubeRoot

abbrev Carrier := Fin 3 × Fin 9
@[implicit_reducible] def paired (i : Fin 8) (f : Fin 9 → Fin 9 → Fin 9) : Magma Carrier where
  op x y := (gateOps i x.1 y.1, f x.2 y.2)
@[implicit_reducible] def source : Magma Carrier := paired 3 fiber.op

theorem source_law : @Equation3342 Carrier source := by
  intro x y
  apply Prod.ext
  · simpa only [source, paired, Magma.op, gate_main] using gate_law x.1 y.1
  · exact fiber_law x.2 y.2

def Shape (i : Fin 8) (f : Fin 9 → Fin 9 → Fin 9) : Prop :=
  (pureX i → ∃ u, f = fun x _ => unary u x) ∧
  (pureY i → ∃ u, f = fun _ y => unary u y) ∧
  (i = 3 → ∃ flip u v, f = (separated flip u v).op)

def SourceInvariant (f : Carrier → Carrier → Carrier) : Prop :=
  ∃ i g, f = (paired i g).op ∧ Shape i g

theorem source_invariant : source.IsCloneInvariant SourceInvariant where
  fst := by
    refine ⟨0, (fun x _ => x), ?_, ?_, ?_, ?_⟩
    · funext x y; exact Prod.ext (gate_fst x.1 y.1).symm rfl
    · intro _; exact ⟨0, funext fun x => funext fun _ => (unary_id x).symm⟩
    · intro h; exact False.elim ((by decide : ¬ pureY 0) h)
    · intro h; exact False.elim ((by decide : (0 : Fin 8) ≠ 3) h)
  snd := by
    refine ⟨1, (fun _ y => y), ?_, ?_, ?_, ?_⟩
    · funext x y; exact Prod.ext (gate_snd x.1 y.1).symm rfl
    · intro h; exact False.elim ((by decide : ¬ pureX 1) h)
    · intro _; exact ⟨0, funext fun _ => funext fun y => (unary_id y).symm⟩
    · intro h; exact False.elim ((by decide : (1 : Fin 8) ≠ 3) h)
  comp := by
    rintro _ _ ⟨i, f, rfl, hix, hiy, _⟩ ⟨j, g, rfl, hjx, hjy, _⟩
    refine ⟨gateComp i j, (fun x y => fiber.op (f x y) (g x y)), ?_, ?_, ?_, ?_⟩
    · funext x y
      exact Prod.ext ((gate_main _ _).trans (gate_comp i j x.1 y.1).symm) rfl
    · intro h
      obtain ⟨hi, hj⟩ := comp_pureX i j h
      obtain ⟨u, rfl⟩ := hix hi
      obtain ⟨v, rfl⟩ := hjx hj
      exact ⟨unaryComp u v, funext fun x => funext fun _ => (unary_comp u v x).symm⟩
    · intro h
      obtain ⟨hi, hj⟩ := comp_pureY i j h
      obtain ⟨u, rfl⟩ := hiy hi
      obtain ⟨v, rfl⟩ := hjy hj
      exact ⟨unaryComp u v, funext fun _ => funext fun y => (unary_comp u v y).symm⟩
    · intro h
      rcases comp_main i j h with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · obtain ⟨u, rfl⟩ := hix hi
        obtain ⟨v, rfl⟩ := hjy hj
        exact ⟨false, u, v, rfl⟩
      · obtain ⟨u, rfl⟩ := hiy hi
        obtain ⟨v, rfl⟩ := hjx hj
        exact ⟨true, u, v, rfl⟩

def GateRelation (f : Carrier → Carrier → Carrier) : Prop :=
  relation (f (0, 0) (2, 0)).1 (f (2, 0) (0, 0)).1

theorem other_invariant (i : Fin 8) (hi : i ≠ 3) (f : Fin 9 → Fin 9 → Fin 9) :
    (paired i f).IsCloneInvariant GateRelation where
  fst := by unfold GateRelation; decide
  snd := by unfold GateRelation; decide
  comp := fun _ _ h₁ h₂ => other_preserves i hi _ _ _ _ h₁ h₂

theorem not_recover_other (i : Fin 8) (hi : i ≠ 3) (f : Fin 9 → Fin 9 → Fin 9) :
    ¬ @Set.TermDefinable Carrier ∅ MagmaLanguage (paired i f).FOStructure
      (Fin 2) source.FinArityOp := by
  intro h
  have bad := (other_invariant i hi f).of_termDefinable h
  exact (by unfold GateRelation; decide : ¬ GateRelation source.op) bad

theorem paired_law (i : Fin 8) (f : Fin 9 → Fin 9 → Fin 9)
    (h : @Equation3545 Carrier (paired i f)) : @Equation3545 (Fin 9) (Magma.mk f) := by
  intro x y
  exact congrArg Prod.snd (h (0, x) (0, y))

def Avoid (c : Fin 9) (f : Carrier → Carrier → Carrier) : Prop :=
  (f (0, preLeft c) (0, preRight c)).2 ≠ c

theorem separated_invariant (flip : Bool) (u v : Fin 27)
    (h : @Equation3545 (Fin 9) (separated flip u v)) :
    (paired 3 (separated flip u v).op).IsCloneInvariant (Avoid (missing flip u v)) where
  fst := (preimage _).2.1
  snd := (preimage _).2.2
  comp := fun _ _ _ _ => separated_missing flip u v h _ _

theorem not_termStructural : ¬ Law3545.TermStructuralOnMagma source := by
  rintro ⟨N, hN, hforward, hback⟩
  obtain ⟨i, f, hf, hshape⟩ := source_invariant.of_termDefinable hforward
  have he : N = paired i f := by
    cases N
    exact congrArg Magma.mk hf
  subst N
  have hi : i = 3 := by
    by_contra h
    exact not_recover_other i h f hback
  subst i
  obtain ⟨flip, u, v, rfl⟩ := hshape.2.2 rfl
  have hB := paired_law 3 (separated flip u v).op
    ((@Law3545.models_iff Carrier (paired 3 (separated flip u v).op)).mp hN)
  have bad := (separated_invariant flip u v hB).of_termDefinable hback
  exact bad (preimage (missing flip u v)).1

end CubeRoot

theorem Equation3545_not_termStructuralFromFin_Equation3342_cubeRoot :
    ¬ Law3545.TermStructuralFromFin Law3342 := by
  intro h
  exact CubeRoot.not_termStructural (h CubeRoot.source
    ((@Law3342.models_iff CubeRoot.Carrier CubeRoot.source).mpr CubeRoot.source_law))

theorem Equation3545_not_termStructuralFrom_Equation3342_cubeRoot :
    ¬ Law3545.TermStructuralFrom Law3342 := by
  intro h
  exact Equation3545_not_termStructuralFromFin_Equation3342_cubeRoot
    (termStructuralFin_of_termStructural h)

/-- info: 'Equation3545_not_termStructuralFromFin_Equation3342_cubeRoot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3545_not_termStructuralFromFin_Equation3342_cubeRoot
/-- info: 'Equation3545_not_termStructuralFrom_Equation3342_cubeRoot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3545_not_termStructuralFrom_Equation3342_cubeRoot

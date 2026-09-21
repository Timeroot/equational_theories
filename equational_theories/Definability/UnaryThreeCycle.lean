import equational_theories.Definability.Invariant
import equational_theories.Asterix

/-!
# Three-cycle unary terms and an infinite E65 separation

Every one-variable term of an E1491 magma is the identity, the square map,
or its square. The square map has order dividing three, so all these terms
are bijections. A countable E65 magma with a noninjective square map therefore
cannot be recovered by terms from any E1491 companion.
-/

open Law Law.MagmaLaw

namespace UnaryThreeCycle

variable {G : Type} (M : Magma G) (h : @Equation1491 G M)
local infixl:70 " * " => M.op

include h in
theorem square_left (x : G) : (x * x) * x = x * x := by
  grind

include h in
theorem square_assoc (x : G) : (x * x) * (x * x) = x * (x * x) := by
  have hleft := square_left M h
  grind

include h in
theorem square_cube (x : G) :
    ((x * x) * (x * x)) * ((x * x) * (x * x)) = x := by
  have hleft := square_left M h
  have hassoc := square_assoc M h
  grind

def orbit (i : Fin 3) (x : G) : G := ![x, x * x, (x * x) * (x * x)] i

include h in
theorem orbit_mul (i j : Fin 3) (x : G) :
    orbit M i x * orbit M j x = orbit M (j + 1) x := by
  have hleft := square_left M h
  have hassoc := square_assoc M h
  have hcube := square_cube M h
  fin_cases i <;> fin_cases j <;> dsimp [orbit] <;> grind

include h in
theorem square_bijective : Function.Bijective (fun x => x * x) := by
  have hinv : Function.LeftInverse (fun x => (x * x) * (x * x)) (fun x => x * x) :=
    square_cube M h
  exact ⟨hinv.injective, fun x => ⟨(x * x) * (x * x), square_cube M h x⟩⟩

include h in
theorem orbit_bijective (i : Fin 3) : Function.Bijective (orbit M i) := by
  fin_cases i
  · exact Function.bijective_id
  · exact square_bijective M h
  · exact (square_bijective M h).comp (square_bijective M h)

def Good (f : G → G → G) : Prop := ∃ i : Fin 3, ∀ x, f x x = orbit M i x

include h in
theorem good_invariant : M.IsCloneInvariant (Good M) where
  fst := ⟨0, fun _ => rfl⟩
  snd := ⟨0, fun _ => rfl⟩
  comp := by
    rintro f g ⟨i, hi⟩ ⟨j, hj⟩
    refine ⟨j + 1, fun x => ?_⟩
    change f x x * g x x = _
    rw [hi, hj]
    exact orbit_mul M h i j x

theorem not_termStructuralOnMagma (N : Magma G)
    (hbad : ¬ Function.Injective (fun x => N.op x x)) :
    ¬ Law1491.TermStructuralOnMagma N := by
  rintro ⟨M, hM, _, hback⟩
  have h := (@Law1491.models_iff G M).mp hM
  obtain ⟨i, hi⟩ := (good_invariant M h).of_termDefinable hback
  have he : (fun x => N.op x x) = orbit M i := funext hi
  apply hbad
  rw [he]
  exact (orbit_bijective M h i).1

/-- This seed forces both 0 and 1 to have square 0. Asterix's extension
construction completes it to an E65 operation on the natural numbers. -/
def seed : Asterix.PartialSolution ℕ where
  E0 := {(0, 0), (1, 1)}
  E1 := {(0, 0), (1, 1), (1, 0), (1, 2), (2, 2)}
  f a b := if a = 1 then if b = 0 then 2 else if b = 2 then 1 else 0
    else if a = 2 then 1 else 0
  E0_subset_E1 := by decide
  t_mem_of_mem_E0' := by decide
  mem_2_of_mem_E0 := by decide
  eq_of_mem_E0 := by decide
  undef_of_not_mem_E0' := by decide
  strange := by decide

@[implicit_reducible] noncomputable def source : Magma ℕ := ⟨Asterix.closure seed⟩

theorem source_law : @Equation65 ℕ source := by
  intro x y
  exact (Asterix.closure_prop seed y x).symm

theorem source_square_zero : source.op 0 0 = 0 := by
  change Asterix.closure seed 0 0 = 0
  rw [Asterix.closure_eq_of_mem_e1 seed 0 0 0 (by decide)]
  rfl

theorem source_square_one : source.op 1 1 = 0 := by
  change Asterix.closure seed 1 1 = 0
  rw [Asterix.closure_eq_of_mem_e1 seed 0 1 1 (by decide)]
  rfl

theorem source_square_not_injective : ¬ Function.Injective (fun x => source.op x x) := by
  intro hinj
  have := hinj (source_square_zero.trans source_square_one.symm)
  omega

end UnaryThreeCycle

theorem Equation1491_not_termStructuralFrom_Equation65_unaryThreeCycle :
    ¬ Law1491.TermStructuralFrom Law65 := by
  intro h
  exact UnaryThreeCycle.not_termStructuralOnMagma UnaryThreeCycle.source
    UnaryThreeCycle.source_square_not_injective
    (h UnaryThreeCycle.source ((@Law65.models_iff ℕ UnaryThreeCycle.source).mpr
      UnaryThreeCycle.source_law))

/-- info: 'Equation1491_not_termStructuralFrom_Equation65_unaryThreeCycle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1491_not_termStructuralFrom_Equation65_unaryThreeCycle

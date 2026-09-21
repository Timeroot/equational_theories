import equational_theories.Definability.Invariant
import equational_theories.Generated.Greedy.Eq1648

/-!
# Two-cycle unary terms and an infinite E1648 separation

Every one-variable term of an E124 magma is the identity or its involutive
square map. A countable E1648 magma with a noninjective square map therefore
cannot be recovered by terms from any E124 companion.
-/

open Law Law.MagmaLaw

namespace UnaryTwoCycle

variable {G : Type} (M : Magma G) (h : @Equation124 G M)
local infixl:70 " * " => M.op

include h in
theorem square_left (x : G) : (x * x) * x = x * x := by
  grind

include h in
theorem square_right (x : G) : x * (x * x) = x := by
  have hleft := square_left M h
  grind

include h in
theorem square_invol (x : G) : (x * x) * (x * x) = x := by
  have hleft := square_left M h
  have hright := square_right M h
  grind

def orbit (i : Fin 2) (x : G) : G := ![x, x * x] i

include h in
theorem orbit_mul (i j : Fin 2) (x : G) :
    orbit M i x * orbit M j x = orbit M (j + 1) x := by
  have hleft := square_left M h
  have hright := square_right M h
  have hinvol := square_invol M h
  fin_cases i <;> fin_cases j <;> dsimp [orbit] <;> grind

include h in
theorem orbit_bijective (i : Fin 2) : Function.Bijective (orbit M i) := by
  fin_cases i
  · exact Function.bijective_id
  · exact Function.Involutive.bijective (square_invol M h)

def Good (f : G → G → G) : Prop := ∃ i : Fin 2, ∀ x, f x x = orbit M i x

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
    ¬ Law124.TermStructuralOnMagma N := by
  rintro ⟨M, hM, _, hback⟩
  have h := (@Law124.models_iff G M).mp hM
  obtain ⟨i, hi⟩ := (good_invariant M h).of_termDefinable hback
  have he : (fun x => N.op x x) = orbit M i := funext hi
  apply hbad
  rw [he]
  exact (orbit_bijective M h i).1

/-- The two prescribed squares agree. The existing E1648 extension theorem
completes this partial operation without changing either value. -/
noncomputable def seed : Eq1648.PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(0, 0, 0), (1, 1, 0)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[implicit_reducible] noncomputable def source : Magma ℕ := seed.toMagma

theorem source_law : @Equation1648 ℕ source := seed.toMagma_equation1648

theorem source_square_zero : source.op 0 0 = 0 :=
  seed.of_R 0 0 0 (by unfold seed; decide)

theorem source_square_one : source.op 1 1 = 0 :=
  seed.of_R 1 1 0 (by unfold seed; decide)

theorem source_square_not_injective : ¬ Function.Injective (fun x => source.op x x) := by
  intro hinj
  have := hinj (source_square_zero.trans source_square_one.symm)
  omega

end UnaryTwoCycle

theorem Equation124_not_termStructuralFrom_Equation1648_unaryTwoCycle :
    ¬ Law124.TermStructuralFrom Law1648 := by
  intro h
  exact UnaryTwoCycle.not_termStructuralOnMagma UnaryTwoCycle.source
    UnaryTwoCycle.source_square_not_injective
    (h UnaryTwoCycle.source ((@Law1648.models_iff ℕ UnaryTwoCycle.source).mpr
      UnaryTwoCycle.source_law))

/-- info: 'Equation124_not_termStructuralFrom_Equation1648_unaryTwoCycle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation124_not_termStructuralFrom_Equation1648_unaryTwoCycle

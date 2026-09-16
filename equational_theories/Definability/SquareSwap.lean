import equational_theories.Definability.Reversible

/-!
# Six structural constructions from the square-swap involution

These constructions previously used finite automorphism arguments. The explicit
inverse in Reversible.lean removes the finiteness hypothesis. The target laws
are proved separately from recovery, by the following elementary observations:

* E3503 makes every square a right-zero element. Swapping square values turns
  squares and nested products into right columns returning the row's square;
  this gives E3470, hence E3460.
* E3869 makes every square a left-zero element. Products with a square on the
  right also have constant rows; the opposite square-swap then gives E3462.
* E4633 makes the row of (x*x)*x constant, giving E3253 after the opposite swap.
* E3519 and E3522 give E3253 directly by splitting the square-swap's cases.

All statements quantify over arbitrary carriers. The old finite theorem names
are retained as corollaries, and all six new conclusions have axiom guards.
-/

open Law Law.MagmaLaw

namespace SquareSwap.E3503
variable {G : Type} (M : Magma G) (h : @Equation3503 G M)

include h in
theorem right_square (a b : G) : M.op b (M.op a a) = M.op a a := by
  let c := M.op (M.op a a) a
  have hc (z : G) : M.op z c = M.op a a := (h a z a a).symm
  calc
    M.op b (M.op a a) = M.op b (M.op (M.op a a) c) := congrArg (M.op b) (hc _).symm
    _ = M.op c c := (h c b a a).symm
    _ = M.op a a := hc c

include h in
theorem swap_right_square (a b : G) :
    (QFOp.squareSwap.magma M).op a (M.op b b) = M.op a a := by
  classical
  rw [QFOp.squareSwap_apply, right_square M h b, right_square M h b]
  simp

include h in
theorem swap_right_product (a b c d : G) :
    (QFOp.squareSwap.magma M).op a (M.op (M.op b c) d) = M.op a a := by
  classical
  rw [QFOp.squareSwap_apply, ← h d (M.op (M.op b c) d) b c, ← h d a b c]
  simp

theorem cases (a b : G) :
    (QFOp.squareSwap.magma M).op a b = M.op a a ∨
    (QFOp.squareSwap.magma M).op a b = M.op b b ∨
    (QFOp.squareSwap.magma M).op a b = M.op a b := by
  classical
  rw [QFOp.squareSwap_apply]
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem image (a b : G) : ∃ c d, (QFOp.squareSwap.magma M).op a b = M.op c d := by
  rcases cases M a b with h | h | h
  · exact ⟨a, a, h⟩
  · exact ⟨b, b, h⟩
  · exact ⟨a, b, h⟩

include h in
theorem satisfies : @Equation3470 G (QFOp.squareSwap.magma M) := by
  intro x y z w
  rw [QFOp.squareSwap_square]
  obtain ⟨a, b, hab⟩ := image M y z
  rw [hab]
  rcases cases M (M.op a b) w with hcase | hcase | hcase
  · rw [hcase, swap_right_square M h]
  · rw [hcase, swap_right_square M h]
  · rw [hcase, swap_right_product M h]

end SquareSwap.E3503

namespace SquareSwap.E3869
variable {G : Type} (M : Magma G) (h : @Equation3869 G M)
include h

theorem left_square (a b : G) : M.op (M.op a a) b = M.op a a := by
  let c := M.op a (M.op a a)
  have hc (z : G) : M.op c z = M.op a a := (h a a z).symm
  calc
    M.op (M.op a a) b = M.op (M.op c (M.op a c)) b := congrArg (M.op · b) (hc _).symm
    _ = M.op c c := (h c a b).symm
    _ = M.op a a := hc c

theorem after_square (a b c : G) : M.op (M.op a (M.op b b)) c = M.op a a := by
  have hb := h a (M.op b (M.op b b)) c
  rw [← h b b a] at hb
  exact hb.symm

theorem satisfies : @Equation3462 G (QFOp.squareSwapOpposite.magma M) := by
  intro x y
  classical
  have hs := left_square M h
  have hu := after_square M h
  simp only [QFOp.squareSwapOpposite_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

end SquareSwap.E3869

namespace SquareSwap.E4633
variable {G : Type} (M : Magma G) (h : @Equation4633 G M)
include h

/-- The row of `(a*a)*a` is constant. -/
theorem cube_row (a b : G) :
    M.op (M.op (M.op a a) a) b = M.op (M.op (M.op a a) a) a := by
  have hb := h (M.op a b) (M.op a b) b
  have ha := h (M.op a b) (M.op a b) a
  rw [← h a a b] at hb
  rw [h a b a] at ha
  exact hb.symm.trans ha

theorem cube_square (a b : G) :
    M.op (M.op (M.op a a) a) b =
      M.op (M.op (M.op a a) a) (M.op (M.op a a) a) :=
  (cube_row M h a b).trans (cube_row M h a _).symm

theorem satisfies : @Equation3253 G (QFOp.squareSwapOpposite.magma M) := by
  intro x
  classical
  have hc := cube_square M h
  simp only [QFOp.squareSwapOpposite_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

end SquareSwap.E4633

theorem Equation3253_StructuralFrom_Equation3519 : Law3253.StructuralFrom Law3519 := by
  apply structuralFrom_squareSwapOpposite
  intro G M hM
  have hm := (@Law3519.models_iff G M).mp hM
  apply (@Law3253.models_iff G (QFOp.squareSwapOpposite.magma M)).mpr
  intro x
  classical
  simp only [QFOp.squareSwapOpposite_apply, Equiv.swap_apply_def]
  split_ifs <;> grind


theorem Equation3253_StructuralFrom_Equation3522 : Law3253.StructuralFrom Law3522 := by
  apply structuralFrom_squareSwapOpposite
  intro G M hM
  have hm := (@Law3522.models_iff G M).mp hM
  apply (@Law3253.models_iff G (QFOp.squareSwapOpposite.magma M)).mpr
  intro x
  classical
  simp only [QFOp.squareSwapOpposite_apply, Equiv.swap_apply_def]
  split_ifs <;> grind


theorem Equation3470_StructuralFrom_Equation3503 : Law3470.StructuralFrom Law3503 :=
  structuralFrom_squareSwap fun {G} M hM ↦
    (@Law3470.models_iff G (QFOp.squareSwap.magma M)).mpr
      (SquareSwap.E3503.satisfies M (Law3503.models_iff.mp hM))

theorem Equation3460_StructuralFrom_Equation3503 : Law3460.StructuralFrom Law3503 :=
  structuralFrom_squareSwap fun {G} M hM ↦
    (@Law3460.models_iff G (QFOp.squareSwap.magma M)).mpr fun x y z ↦
      SquareSwap.E3503.satisfies M (Law3503.models_iff.mp hM) x x y z

theorem Equation3462_StructuralFrom_Equation3869 : Law3462.StructuralFrom Law3869 :=
  structuralFrom_squareSwapOpposite fun {G} M hM ↦
    (@Law3462.models_iff G (QFOp.squareSwapOpposite.magma M)).mpr
      (SquareSwap.E3869.satisfies M (Law3869.models_iff.mp hM))

theorem Equation3253_StructuralFrom_Equation4633 : Law3253.StructuralFrom Law4633 :=
  structuralFrom_squareSwapOpposite fun {G} M hM ↦
    (@Law3253.models_iff G (QFOp.squareSwapOpposite.magma M)).mpr
      (SquareSwap.E4633.satisfies M (Law4633.models_iff.mp hM))

/-- Compatibility with the former finite-only statement. -/
theorem Equation3253_StructuralFromFin_Equation3519 : Law3253.StructuralFromFin Law3519 :=
  structuralFin_of_structural Equation3253_StructuralFrom_Equation3519

/-- info: 'Equation3253_StructuralFrom_Equation3519' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation3253_StructuralFrom_Equation3519

/-- Compatibility with the former finite-only statement. -/
theorem Equation3253_StructuralFromFin_Equation3522 : Law3253.StructuralFromFin Law3522 :=
  structuralFin_of_structural Equation3253_StructuralFrom_Equation3522

/-- info: 'Equation3253_StructuralFrom_Equation3522' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation3253_StructuralFrom_Equation3522

/-- Compatibility with the former finite-only statement. -/
theorem Equation3460_StructuralFromFin_Equation3503 : Law3460.StructuralFromFin Law3503 :=
  structuralFin_of_structural Equation3460_StructuralFrom_Equation3503

/-- info: 'Equation3460_StructuralFrom_Equation3503' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation3460_StructuralFrom_Equation3503

/-- Compatibility with the former finite-only statement. -/
theorem Equation3470_StructuralFromFin_Equation3503 : Law3470.StructuralFromFin Law3503 :=
  structuralFin_of_structural Equation3470_StructuralFrom_Equation3503

/-- info: 'Equation3470_StructuralFrom_Equation3503' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation3470_StructuralFrom_Equation3503

/-- Compatibility with the former finite-only statement. -/
theorem Equation3462_StructuralFromFin_Equation3869 : Law3462.StructuralFromFin Law3869 :=
  structuralFin_of_structural Equation3462_StructuralFrom_Equation3869

/-- info: 'Equation3462_StructuralFrom_Equation3869' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation3462_StructuralFrom_Equation3869

/-- Compatibility with the former finite-only statement. -/
theorem Equation3253_StructuralFromFin_Equation4633 : Law3253.StructuralFromFin Law4633 :=
  structuralFin_of_structural Equation3253_StructuralFrom_Equation4633

/-- info: 'Equation3253_StructuralFrom_Equation4633' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation3253_StructuralFrom_Equation4633

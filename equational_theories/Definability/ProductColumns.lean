import equational_theories.Definability.ComposedDiagonalSwaps

/-! In E3363 every product has a constant column. Three reversible swaps
turn this into an operation whose rows are idempotent, establishing an E323
companion on arbitrary carriers. -/
open Law Law.MagmaLaw DiagonalOutputSwap
set_option maxHeartbeats 500000
namespace ProductColumns
noncomputable abbrev companion {G : Type} (M : Magma G) : Magma G :=
  (forward 0 1 false).magma ((forward 2 0 false).magma ((forward 3 2 false).magma M))

/-- All entries in the column of a product agree with its diagonal entry. -/
theorem column {G : Type} (M : Magma G) (h : @Equation3363 G M) (a b z : G) :
    M.op z (M.op a b) = M.op (M.op a b) (M.op a b) := by
  exact (h z (M.op a b) b).trans
    (congrArg (M.op (M.op a b)) (h a b z).symm)

/-- A product is fixed by every companion row other than its own. -/
theorem fixed_product {G : Type} (M : Magma G) (h : @Equation3363 G M)
    (a b x : G) (hne : x ≠ M.op a b) :
    (companion M).op x (M.op a b) = M.op a b := by
  classical
  have he : (companion M).op x (M.op a b) =
      Equiv.swap x (M.op a b) (Equiv.swap (M.op x x) x
        (Equiv.swap (M.op (M.op a b) (M.op a b)) (M.op x x) (M.op x (M.op a b)))) := by
    simp [forward_apply, value, hne]
  rw [he, column M h a b x]
  simp

/-- Each possible output is either the input or one of three known products;
the exceptional diagonal cases are recorded explicitly. -/
theorem output_cases {G : Type} (M : Magma G) (h : @Equation3363 G M) (x y : G) :
    (companion M).op x y = y ∨ (companion M).op x y = M.op x x ∨
      ((companion M).op x y = M.op y y ∧ x ≠ M.op y y) ∨
      ((companion M).op x y = M.op x y ∧ x ≠ M.op x y) := by
  classical
  have hct := column M h x y x
  have hrt := column M h x y y
  have hcq := column M h x x x
  have hrq := column M h x x y
  have hcr := column M h y y x
  have hqr := column M h y y y
  clear h
  simp [forward_apply, value, Equiv.swap_apply_def]
  grind

theorem target323 {G : Type} (M : Magma G) (h : @Equation3363 G M) :
    @Equation323 G (companion M) := by
  classical
  intro x y
  rcases output_cases M h x y with he | he | ⟨he, hn⟩ | ⟨he, hn⟩
  · rw [he]
    exact he.symm
  · rw [he]
    by_cases hx : x = M.op x x
    · rw [← hx]; simpa using hx
    · exact (fixed_product M h x x x hx).symm
  · rw [he]
    exact (fixed_product M h y y x hn).symm
  · rw [he]
    exact (fixed_product M h x y x hn).symm
theorem Equation323_structuralFrom_Equation3363_productColumns :
    Law323.StructuralFrom Law3363 :=
  structuralFrom_threeDiagonalSwaps 3 2 2 0 0 1 false fun {G} M hM =>
    (@Law323.models_iff G (companion M)).mpr
      (target323 M ((@Law3363.models_iff G M).mp hM))

end ProductColumns

/-- info: 'ProductColumns.Equation323_structuralFrom_Equation3363_productColumns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProductColumns.Equation323_structuralFrom_Equation3363_productColumns

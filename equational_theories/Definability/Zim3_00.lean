import equational_theories.Equations.All
import equational_theories.EquationLawConversion
import equational_theories.Preorder
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_zx
import equational_theories.Generated.VampireProven.Proofs9

open Law Law.MagmaLaw

/-- Law 3740 implies law 4380, along 3740 → 4512 → 4435 → 4380. -/
theorem Law3740_implies_Law4380 : Law3740.implies Law4380 := fun {_G} _ h ↦
  Law4380.models_iff.mpr (SimpleRewrites.Equation4435_implies_Equation4380 _ (SimpleRewrites.Equation4512_implies_Equation4435 _ (Equation3740_implies_Equation4512 _ (Law3740.models_iff.mp h))))

/-- Law 3929 implies law 4380, along 3929 → 4474 → 4472 → 4380. -/
theorem Law3929_implies_Law4380 : Law3929.implies Law4380 := fun {_G} _ h ↦
  Law4380.models_iff.mpr (SimpleRewrites.Equation4472_implies_Equation4380 _ (SimpleRewrites.Equation4474_implies_Equation4472 _ (Equation3929_implies_Equation4474 _ (Law3929.models_iff.mp h))))

/-- Law 4439 implies law 4380, along 4439 → 4433 → 4380. -/
theorem Law4439_implies_Law4380 : Law4439.implies Law4380 := fun {_G} _ h ↦
  Law4380.models_iff.mpr (SimpleRewrites.Equation4433_implies_Equation4380 _ (SimpleRewrites.Equation4439_implies_Equation4433 _ (Law4439.models_iff.mp h)))

/-- Law 4542 implies law 4380, along 4542 → 4432 → 4380. -/
theorem Law4542_implies_Law4380 : Law4542.implies Law4380 := fun {_G} _ h ↦
  Law4380.models_iff.mpr (SimpleRewrites.Equation4432_implies_Equation4380 _ (SimpleRewrites.Equation4542_implies_Equation4432 _ (Law4542.models_iff.mp h)))

import equational_theories.Equations.All
import equational_theories.EquationLawConversion
import equational_theories.Preorder
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx_zy
import equational_theories.Generated.TrivialBruteforce.theorems.NthRewrites
import equational_theories.Generated.VampireProven.Proofs11
import equational_theories.Generated.VampireProven.Proofs12
import equational_theories.Generated.VampireProven.Proofs6
import equational_theories.Generated.VampireProven.Proofs7
import equational_theories.Generated.VampireProven.Proofs8
import equational_theories.Generated.VampireProven.Proofs9

open Law Law.MagmaLaw

/-- Law 635 implies law 359, along 635 → 852 → 52 → 359. -/
theorem Law635_implies_Law359 : Law635.implies Law359 := fun {_G} _ h ↦
  Law359.models_iff.mpr (Equation52_implies_Equation359 _ (Equation852_implies_Equation52 _ (Equation635_implies_Equation852 _ (Law635.models_iff.mp h))))

/-- Law 645 implies law 359, along 645 → 55 → 359. -/
theorem Law645_implies_Law359 : Law645.implies Law359 := fun {_G} _ h ↦
  Law359.models_iff.mpr (Equation55_implies_Equation359 _ (Equation645_implies_Equation55 _ (Law645.models_iff.mp h)))

/-- Law 852 implies law 359, along 852 → 52 → 359. -/
theorem Law852_implies_Law359 : Law852.implies Law359 := fun {_G} _ h ↦
  Law359.models_iff.mpr (Equation52_implies_Equation359 _ (Equation852_implies_Equation52 _ (Law852.models_iff.mp h)))

/-- Law 2655 implies law 307, along 2655 → 257 → 307. -/
theorem Law2655_implies_Law307 : Law2655.implies Law307 := fun {_G} _ h ↦
  Law307.models_iff.mpr (Equation257_implies_Equation307 _ (Equation2655_implies_Equation257 _ (Law2655.models_iff.mp h)))

/-- Law 2868 implies law 307, along 2868 → 257 → 307. -/
theorem Law2868_implies_Law307 : Law2868.implies Law307 := fun {_G} _ h ↦
  Law307.models_iff.mpr (Equation257_implies_Equation307 _ (Equation2868_implies_Equation257 _ (Law2868.models_iff.mp h)))

/-- Law 2890 implies law 307, along 2890 → 263 → 307. -/
theorem Law2890_implies_Law307 : Law2890.implies Law307 := fun {_G} _ h ↦
  Law307.models_iff.mpr (Equation263_implies_Equation307 _ (Equation2890_implies_Equation263 _ (Law2890.models_iff.mp h)))

/-- Law 3863 implies law 359, along 3863 → 360 → 359. -/
theorem Law3863_implies_Law359 : Law3863.implies Law359 := fun {_G} _ h ↦
  Law359.models_iff.mpr (SimpleRewrites.Equation360_implies_Equation359 _ (NthRewrites.Equation3863_implies_Equation360 _ (Law3863.models_iff.mp h)))

/-- Law 3869 implies law 359, along 3869 → 3872 → 3863 → 360 → 359. -/
theorem Law3869_implies_Law359 : Law3869.implies Law359 := fun {_G} _ h ↦
  Law359.models_iff.mpr (SimpleRewrites.Equation360_implies_Equation359 _ (NthRewrites.Equation3863_implies_Equation360 _ (SimpleRewrites.Equation3872_implies_Equation3863 _ (Equation3869_implies_Equation3872 _ (Law3869.models_iff.mp h)))))

/-- Law 3872 implies law 359, along 3872 → 3863 → 360 → 359. -/
theorem Law3872_implies_Law359 : Law3872.implies Law359 := fun {_G} _ h ↦
  Law359.models_iff.mpr (SimpleRewrites.Equation360_implies_Equation359 _ (NthRewrites.Equation3863_implies_Equation360 _ (SimpleRewrites.Equation3872_implies_Equation3863 _ (Law3872.models_iff.mp h))))

/-- Law 3875 implies law 359, along 3875 → 3872 → 3863 → 360 → 359. -/
theorem Law3875_implies_Law359 : Law3875.implies Law359 := fun {_G} _ h ↦
  Law359.models_iff.mpr (SimpleRewrites.Equation360_implies_Equation359 _ (NthRewrites.Equation3863_implies_Equation360 _ (SimpleRewrites.Equation3872_implies_Equation3863 _ (Equation3875_implies_Equation3872 _ (Law3875.models_iff.mp h)))))

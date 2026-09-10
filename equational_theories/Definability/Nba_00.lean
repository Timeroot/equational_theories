import equational_theories.Equations.All
import equational_theories.EquationLawConversion
import equational_theories.Preorder
import equational_theories.Generated.MagmaEgg.small._002
import equational_theories.Generated.MagmaEgg.small._003
import equational_theories.Generated.MagmaEgg.small._004
import equational_theories.Generated.MagmaEgg.small._011
import equational_theories.Generated.MagmaEgg.small._013
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_wz
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_zx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_zy
import equational_theories.Generated.TrivialBruteforce.theorems.Apply
import equational_theories.Generated.VampireProven.Proofs10
import equational_theories.Generated.VampireProven.Proofs11
import equational_theories.Generated.VampireProven.Proofs13
import equational_theories.Generated.VampireProven.Proofs4
import equational_theories.Generated.VampireProven.Proofs6

open Law Law.MagmaLaw

/-- Law 224 implies law 2702, along 224 → 2782 → 2702. -/
theorem Law224_implies_Law2702 : Law224.implies Law2702 := fun {_G} _ h ↦
  Law2702.models_iff.mpr (SimpleRewrites.Equation2782_implies_Equation2702 _ (Apply.Equation224_implies_Equation2782 _ (Law224.models_iff.mp h)))

/-- Law 765 implies law 778, along 765 → 1577 → 778. -/
theorem Law765_implies_Law778 : Law765.implies Law778 := fun {_G} _ h ↦
  Law778.models_iff.mpr (Equation1577_implies_Equation778 _ (Equation765_implies_Equation1577 _ (Law765.models_iff.mp h)))

/-- Law 3791 implies law 4197, along 3791 → 4176 → 3404 → 4197. -/
theorem Law3791_implies_Law4197 : Law3791.implies Law4197 := fun {_G} _ h ↦
  Law4197.models_iff.mpr (Equation3404_implies_Equation4197 _ (Equation4176_implies_Equation3404 _ (Equation3791_implies_Equation4176 _ (Law3791.models_iff.mp h))))

/-- Law 4428 implies law 4388, along 4428 → 4424 → 4388. -/
theorem Law4428_implies_Law4388 : Law4428.implies Law4388 := fun {_G} _ h ↦
  Law4388.models_iff.mpr (SimpleRewrites.Equation4424_implies_Equation4388 _ (SimpleRewrites.Equation4428_implies_Equation4424 _ (Law4428.models_iff.mp h)))

/-- Law 4464 implies law 4388, along 4464 → 4448 → 4391 → 4388. -/
theorem Law4464_implies_Law4388 : Law4464.implies Law4388 := fun {_G} _ h ↦
  Law4388.models_iff.mpr (SimpleRewrites.Equation4391_implies_Equation4388 _ (Equation4448_implies_Equation4391 _ (SimpleRewrites.Equation4464_implies_Equation4448 _ (Law4464.models_iff.mp h))))

/-- Law 4574 implies law 4388, along 4574 → 4498 → 4388. -/
theorem Law4574_implies_Law4388 : Law4574.implies Law4388 := fun {_G} _ h ↦
  Law4388.models_iff.mpr (SimpleRewrites.Equation4498_implies_Equation4388 _ (SimpleRewrites.Equation4574_implies_Equation4498 _ (Law4574.models_iff.mp h)))

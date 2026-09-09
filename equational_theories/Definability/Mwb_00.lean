import equational_theories.Equations.All
import equational_theories.EquationLawConversion
import equational_theories.Preorder
import equational_theories.Generated.MagmaEgg.small._002
import equational_theories.Generated.MagmaEgg.small._004
import equational_theories.Generated.MagmaEgg.small._005
import equational_theories.Generated.MagmaEgg.small._006
import equational_theories.Generated.MagmaEgg.small._013
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_wy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_wz_yx_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_wz_zx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_yx_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_zx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx_zy
import equational_theories.Generated.TrivialBruteforce.theorems.Apply
import equational_theories.Generated.TrivialBruteforce.theorems.NthRewrites
import equational_theories.Generated.VampireProven.Proofs1
import equational_theories.Generated.VampireProven.Proofs11
import equational_theories.Generated.VampireProven.Proofs9

open Law Law.MagmaLaw

/-- Law 109 implies law 844, along 109 → 851 → 844. -/
theorem Law109_implies_Law844 : Law109.implies Law844 := fun {_G} _ h ↦
  Law844.models_iff.mpr (SimpleRewrites.Equation851_implies_Equation844 _ (Apply.Equation109_implies_Equation851 _ (Law109.models_iff.mp h)))

/-- Law 1060 implies law 844, along 1060 → 1257 → 851 → 844. -/
theorem Law1060_implies_Law844 : Law1060.implies Law844 := fun {_G} _ h ↦
  Law844.models_iff.mpr (SimpleRewrites.Equation851_implies_Equation844 _ (Equation1257_implies_Equation851 _ (Equation1060_implies_Equation1257 _ (Law1060.models_iff.mp h))))

/-- Law 3404 implies law 3591, along 3404 → 4197 → 3791 → 4176 → 3591. -/
theorem Law3404_implies_Law3591 : Law3404.implies Law3591 := fun {_G} _ h ↦
  Law3591.models_iff.mpr (Equation4176_implies_Equation3591 _ (Equation3791_implies_Equation4176 _ (NthRewrites.Equation4197_implies_Equation3791 _ (Equation3404_implies_Equation4197 _ (Law3404.models_iff.mp h)))))

/-- Law 3738 implies law 4401, along 3738 → 4519 → 4401. -/
theorem Law3738_implies_Law4401 : Law3738.implies Law4401 := fun {_G} _ h ↦
  Law4401.models_iff.mpr (SimpleRewrites.Equation4519_implies_Equation4401 _ (Equation3738_implies_Equation4519 _ (Law3738.models_iff.mp h)))

/-- Law 3755 implies law 4490, along 3755 → 3798 → 4559 → 4490. -/
theorem Law3755_implies_Law4490 : Law3755.implies Law4490 := fun {_G} _ h ↦
  Law4490.models_iff.mpr (SimpleRewrites.Equation4559_implies_Equation4490 _ (Equation3798_implies_Equation4559 _ (Equation3755_implies_Equation3798 _ (Law3755.models_iff.mp h))))

/-- Law 3791 implies law 3591, along 3791 → 4176 → 3591. -/
theorem Law3791_implies_Law3591 : Law3791.implies Law3591 := fun {_G} _ h ↦
  Law3591.models_iff.mpr (Equation4176_implies_Equation3591 _ (Equation3791_implies_Equation4176 _ (Law3791.models_iff.mp h)))

/-- Law 3798 implies law 4490, along 3798 → 4559 → 4490. -/
theorem Law3798_implies_Law4490 : Law3798.implies Law4490 := fun {_G} _ h ↦
  Law4490.models_iff.mpr (SimpleRewrites.Equation4559_implies_Equation4490 _ (Equation3798_implies_Equation4559 _ (Law3798.models_iff.mp h)))

/-- Law 3804 implies law 3591, along 3804 → 4197 → 3791 → 4176 → 3591. -/
theorem Law3804_implies_Law3591 : Law3804.implies Law3591 := fun {_G} _ h ↦
  Law3591.models_iff.mpr (Equation4176_implies_Equation3591 _ (Equation3791_implies_Equation4176 _ (NthRewrites.Equation4197_implies_Equation3791 _ (Equation3804_implies_Equation4197 _ (Law3804.models_iff.mp h)))))

/-- Law 4197 implies law 3591, along 4197 → 3791 → 4176 → 3591. -/
theorem Law4197_implies_Law3591 : Law4197.implies Law3591 := fun {_G} _ h ↦
  Law3591.models_iff.mpr (Equation4176_implies_Equation3591 _ (Equation3791_implies_Equation4176 _ (NthRewrites.Equation4197_implies_Equation3791 _ (Law4197.models_iff.mp h))))

/-- Law 4523 implies law 4385, along 4523 → 4540 → 4557 → 4489 → 4385. -/
theorem Law4523_implies_Law4385 : Law4523.implies Law4385 := fun {_G} _ h ↦
  Law4385.models_iff.mpr (SimpleRewrites.Equation4489_implies_Equation4385 _ (SimpleRewrites.Equation4557_implies_Equation4489 _ (Equation4540_implies_Equation4557 _ (Equation4523_implies_Equation4540 _ (Law4523.models_iff.mp h)))))

/-- Law 4535 implies law 4411, along 4535 → 4577 → 4427 → 4411. -/
theorem Law4535_implies_Law4411 : Law4535.implies Law4411 := fun {_G} _ h ↦
  Law4411.models_iff.mpr (SimpleRewrites.Equation4427_implies_Equation4411 _ (SimpleRewrites.Equation4577_implies_Equation4427 _ (Equation4535_implies_Equation4577 _ (Law4535.models_iff.mp h))))

/-- Law 4535 implies law 4448, along 4535 → 4577 → 4464 → 4448. -/
theorem Law4535_implies_Law4448 : Law4535.implies Law4448 := fun {_G} _ h ↦
  Law4448.models_iff.mpr (SimpleRewrites.Equation4464_implies_Equation4448 _ (SimpleRewrites.Equation4577_implies_Equation4464 _ (Equation4535_implies_Equation4577 _ (Law4535.models_iff.mp h))))

/-- Law 4540 implies law 4385, along 4540 → 4557 → 4489 → 4385. -/
theorem Law4540_implies_Law4385 : Law4540.implies Law4385 := fun {_G} _ h ↦
  Law4385.models_iff.mpr (SimpleRewrites.Equation4489_implies_Equation4385 _ (SimpleRewrites.Equation4557_implies_Equation4489 _ (Equation4540_implies_Equation4557 _ (Law4540.models_iff.mp h))))

/-- Law 4552 implies law 4535, along 4552 → 4567 → 4562 → 4535. -/
theorem Law4552_implies_Law4535 : Law4552.implies Law4535 := fun {_G} _ h ↦
  Law4535.models_iff.mpr (Equation4562_implies_Equation4535 _ (Equation4567_implies_Equation4562 _ (Equation4552_implies_Equation4567 _ (Law4552.models_iff.mp h))))

/-- Law 4557 implies law 4385, along 4557 → 4489 → 4385. -/
theorem Law4557_implies_Law4385 : Law4557.implies Law4385 := fun {_G} _ h ↦
  Law4385.models_iff.mpr (SimpleRewrites.Equation4489_implies_Equation4385 _ (SimpleRewrites.Equation4557_implies_Equation4489 _ (Law4557.models_iff.mp h)))

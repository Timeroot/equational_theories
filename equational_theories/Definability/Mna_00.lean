import equational_theories.Equations.All
import equational_theories.EquationLawConversion
import equational_theories.Preorder
import equational_theories.Generated.Equation1
import equational_theories.Generated.MagmaEgg.small._001
import equational_theories.Generated.MagmaEgg.small._002
import equational_theories.Generated.MagmaEgg.small._004
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_wz_yx_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_yx_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_zx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_zx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_zy
import equational_theories.Generated.TrivialBruteforce.theorems.Apply
import equational_theories.Generated.TrivialBruteforce.theorems.NthRewrites
import equational_theories.Generated.TrivialBruteforce.theorems.RewriteHypothesis
import equational_theories.Generated.VampireProven.Proofs1
import equational_theories.Generated.VampireProven.Proofs10
import equational_theories.Generated.VampireProven.Proofs11
import equational_theories.Generated.VampireProven.Proofs12
import equational_theories.Generated.VampireProven.Proofs13
import equational_theories.Generated.VampireProven.Proofs2
import equational_theories.Generated.VampireProven.Proofs5
import equational_theories.Generated.VampireProven.Proofs8
import equational_theories.Generated.VampireProven.Proofs9

open Law Law.MagmaLaw

/-- Law 106 implies law 834, along 106 → 841 → 1261 → 834. -/
theorem Law106_implies_Law834 : Law106.implies Law834 := fun {_G} _ h ↦
  Law834.models_iff.mpr (Equation1261_implies_Equation834 _ (Equation841_implies_Equation1261 _ (Apply.Equation106_implies_Equation841 _ (Law106.models_iff.mp h))))

/-- Law 109 implies law 844, along 109 → 851 → 844. -/
theorem Law109_implies_Law844 : Law109.implies Law844 := fun {_G} _ h ↦
  Law844.models_iff.mpr (SimpleRewrites.Equation851_implies_Equation844 _ (Apply.Equation109_implies_Equation851 _ (Law109.models_iff.mp h)))

/-- Law 111 implies law 1049, along 111 → 1068 → 1052 → 1049. -/
theorem Law111_implies_Law1049 : Law111.implies Law1049 := fun {_G} _ h ↦
  Law1049.models_iff.mpr (SimpleRewrites.Equation1052_implies_Equation1049 _ (SimpleRewrites.Equation1068_implies_Equation1052 _ (Apply.Equation111_implies_Equation1068 _ (Law111.models_iff.mp h))))

/-- Law 723 implies law 72, along 723 → 909 → 72. -/
theorem Law723_implies_Law72 : Law723.implies Law72 := fun {_G} _ h ↦
  Law72.models_iff.mpr (Equation909_implies_Equation72 _ (Equation723_implies_Equation909 _ (Law723.models_iff.mp h)))

/-- Law 841 implies law 834, along 841 → 1261 → 834. -/
theorem Law841_implies_Law834 : Law841.implies Law834 := fun {_G} _ h ↦
  Law834.models_iff.mpr (Equation1261_implies_Equation834 _ (Equation841_implies_Equation1261 _ (Law841.models_iff.mp h)))

/-- Law 849 implies law 844, along 849 → 851 → 844. -/
theorem Law849_implies_Law844 : Law849.implies Law844 := fun {_G} _ h ↦
  Law844.models_iff.mpr (SimpleRewrites.Equation851_implies_Equation844 _ (Equation849_implies_Equation851 _ (Law849.models_iff.mp h)))

/-- Law 947 implies law 72, along 947 → 723 → 909 → 72. -/
theorem Law947_implies_Law72 : Law947.implies Law72 := fun {_G} _ h ↦
  Law72.models_iff.mpr (Equation909_implies_Equation72 _ (Equation723_implies_Equation909 _ (Equation947_implies_Equation723 _ (Law947.models_iff.mp h))))

/-- Law 1060 implies law 844, along 1060 → 1257 → 851 → 844. -/
theorem Law1060_implies_Law844 : Law1060.implies Law844 := fun {_G} _ h ↦
  Law844.models_iff.mpr (SimpleRewrites.Equation851_implies_Equation844 _ (Equation1257_implies_Equation851 _ (Equation1060_implies_Equation1257 _ (Law1060.models_iff.mp h))))

/-- Law 1068 implies law 1049, along 1068 → 1052 → 1049. -/
theorem Law1068_implies_Law1049 : Law1068.implies Law1049 := fun {_G} _ h ↦
  Law1049.models_iff.mpr (SimpleRewrites.Equation1052_implies_Equation1049 _ (SimpleRewrites.Equation1068_implies_Equation1052 _ (Law1068.models_iff.mp h)))

/-- Law 1246 implies law 834, along 1246 → 106 → 841 → 1261 → 834. -/
theorem Law1246_implies_Law834 : Law1246.implies Law834 := fun {_G} _ h ↦
  Law834.models_iff.mpr (Equation1261_implies_Equation834 _ (Equation841_implies_Equation1261 _ (Apply.Equation106_implies_Equation841 _ (Equation1246_implies_Equation106 _ (Law1246.models_iff.mp h)))))

/-- Law 1247 implies law 834, along 1247 → 1246 → 106 → 841 → 1261 → 834. -/
theorem Law1247_implies_Law834 : Law1247.implies Law834 := fun {_G} _ h ↦
  Law834.models_iff.mpr (Equation1261_implies_Equation834 _ (Equation841_implies_Equation1261 _ (Apply.Equation106_implies_Equation841 _ (Equation1246_implies_Equation106 _ (SimpleRewrites.Equation1247_implies_Equation1246 _ (Law1247.models_iff.mp h))))))

/-- Law 1257 implies law 844, along 1257 → 851 → 844. -/
theorem Law1257_implies_Law844 : Law1257.implies Law844 := fun {_G} _ h ↦
  Law844.models_iff.mpr (SimpleRewrites.Equation851_implies_Equation844 _ (Equation1257_implies_Equation851 _ (Law1257.models_iff.mp h)))

/-- Law 1265 implies law 1049, along 1265 → 1068 → 1052 → 1049. -/
theorem Law1265_implies_Law1049 : Law1265.implies Law1049 := fun {_G} _ h ↦
  Law1049.models_iff.mpr (SimpleRewrites.Equation1052_implies_Equation1049 _ (SimpleRewrites.Equation1068_implies_Equation1052 _ (Equation1265_implies_Equation1068 _ (Law1265.models_iff.mp h))))

/-- Law 1506 implies law 72, along 1506 → 723 → 909 → 72. -/
theorem Law1506_implies_Law72 : Law1506.implies Law72 := fun {_G} _ h ↦
  Law72.models_iff.mpr (Equation909_implies_Equation72 _ (Equation723_implies_Equation909 _ (Equation1506_implies_Equation723 _ (Law1506.models_iff.mp h))))

/-- Law 1560 implies law 916, along 1560 → 960 → 916. -/
theorem Law1560_implies_Law916 : Law1560.implies Law916 := fun {_G} _ h ↦
  Law916.models_iff.mpr (SimpleRewrites.Equation960_implies_Equation916 _ (Equation1560_implies_Equation960 _ (Law1560.models_iff.mp h)))

/-- Law 2536 implies law 2712, along 2536 → 3180 → 2712. -/
theorem Law2536_implies_Law2712 : Law2536.implies Law2712 := fun {_G} _ h ↦
  Law2712.models_iff.mpr (Equation3180_implies_Equation2712 _ (Equation2536_implies_Equation3180 _ (Law2536.models_iff.mp h)))

/-- Law 3503 implies law 3499, along 3503 → 3487 → 3499. -/
theorem Law3503_implies_Law3499 : Law3503.implies Law3499 := fun {_G} _ h ↦
  Law3499.models_iff.mpr (Equation3487_implies_Equation3499 _ (SimpleRewrites.Equation3503_implies_Equation3487 _ (Law3503.models_iff.mp h)))

/-- Law 3744 implies law 326, along 3744 → 3736 → 3715 → 326. -/
theorem Law3744_implies_Law326 : Law3744.implies Law326 := fun {_G} _ h ↦
  Law326.models_iff.mpr (NthRewrites.Equation3715_implies_Equation326 _ (SimpleRewrites.Equation3736_implies_Equation3715 _ (SimpleRewrites.Equation3744_implies_Equation3736 _ (Law3744.models_iff.mp h))))

/-- Law 3869 implies law 1, along 3869 → 3867 → 3862 → 1. -/
theorem Law3869_implies_Law1 : Law3869.implies Law1 := fun {_G} _ h ↦
  Law1.models_iff.mpr (Equation3862_implies_Equation1 _ (SimpleRewrites.Equation3867_implies_Equation3862 _ (SimpleRewrites.Equation3869_implies_Equation3867 _ (Law3869.models_iff.mp h))))

/-- Law 3929 implies law 4381, along 3929 → 4474 → 4381. -/
theorem Law3929_implies_Law4381 : Law3929.implies Law4381 := fun {_G} _ h ↦
  Law4381.models_iff.mpr (SimpleRewrites.Equation4474_implies_Equation4381 _ (Equation3929_implies_Equation4474 _ (Law3929.models_iff.mp h)))

/-- Law 3951 implies law 1, along 3951 → 3862 → 1. -/
theorem Law3951_implies_Law1 : Law3951.implies Law1 := fun {_G} _ h ↦
  Law1.models_iff.mpr (Equation3862_implies_Equation1 _ (SimpleRewrites.Equation3951_implies_Equation3862 _ (Law3951.models_iff.mp h)))

/-- Law 4447 implies law 4434, along 4447 → 4463 → 4434. -/
theorem Law4447_implies_Law4434 : Law4447.implies Law4434 := fun {_G} _ h ↦
  Law4434.models_iff.mpr (SimpleRewrites.Equation4463_implies_Equation4434 _ (RewriteHypothesis.Equation4447_implies_Equation4463 _ (Law4447.models_iff.mp h)))

/-- Law 4464 implies law 4456, along 4464 → 4448 → 4456. -/
theorem Law4464_implies_Law4456 : Law4464.implies Law4456 := fun {_G} _ h ↦
  Law4456.models_iff.mpr (Equation4448_implies_Equation4456 _ (SimpleRewrites.Equation4464_implies_Equation4448 _ (Law4464.models_iff.mp h)))

/-- Law 4514 implies law 4401, along 4514 → 4518 → 4401. -/
theorem Law4514_implies_Law4401 : Law4514.implies Law4401 := fun {_G} _ h ↦
  Law4401.models_iff.mpr (SimpleRewrites.Equation4518_implies_Equation4401 _ (Equation4514_implies_Equation4518 _ (Law4514.models_iff.mp h)))

/-- Law 4527 implies law 4423, along 4527 → 4572 → 4423. -/
theorem Law4527_implies_Law4423 : Law4527.implies Law4423 := fun {_G} _ h ↦
  Law4423.models_iff.mpr (SimpleRewrites.Equation4572_implies_Equation4423 _ (Equation4527_implies_Equation4572 _ (Law4527.models_iff.mp h)))

/-- Law 4535 implies law 4411, along 4535 → 4577 → 4427 → 4411. -/
theorem Law4535_implies_Law4411 : Law4535.implies Law4411 := fun {_G} _ h ↦
  Law4411.models_iff.mpr (SimpleRewrites.Equation4427_implies_Equation4411 _ (SimpleRewrites.Equation4577_implies_Equation4427 _ (Equation4535_implies_Equation4577 _ (Law4535.models_iff.mp h))))

/-- Law 4548 implies law 4423, along 4548 → 4527 → 4572 → 4423. -/
theorem Law4548_implies_Law4423 : Law4548.implies Law4423 := fun {_G} _ h ↦
  Law4423.models_iff.mpr (SimpleRewrites.Equation4572_implies_Equation4423 _ (Equation4527_implies_Equation4572 _ (Equation4548_implies_Equation4527 _ (Law4548.models_iff.mp h))))

/-- Law 4552 implies law 4411, along 4552 → 4567 → 4562 → 4535 → 4577 → 4427 → 4411. -/
theorem Law4552_implies_Law4411 : Law4552.implies Law4411 := fun {_G} _ h ↦
  Law4411.models_iff.mpr (SimpleRewrites.Equation4427_implies_Equation4411 _ (SimpleRewrites.Equation4577_implies_Equation4427 _ (Equation4535_implies_Equation4577 _ (Equation4562_implies_Equation4535 _ (Equation4567_implies_Equation4562 _ (Equation4552_implies_Equation4567 _ (Law4552.models_iff.mp h)))))))

/-- Law 4562 implies law 4411, along 4562 → 4535 → 4577 → 4427 → 4411. -/
theorem Law4562_implies_Law4411 : Law4562.implies Law4411 := fun {_G} _ h ↦
  Law4411.models_iff.mpr (SimpleRewrites.Equation4427_implies_Equation4411 _ (SimpleRewrites.Equation4577_implies_Equation4427 _ (Equation4535_implies_Equation4577 _ (Equation4562_implies_Equation4535 _ (Law4562.models_iff.mp h)))))

/-- Law 4567 implies law 4411, along 4567 → 4562 → 4535 → 4577 → 4427 → 4411. -/
theorem Law4567_implies_Law4411 : Law4567.implies Law4411 := fun {_G} _ h ↦
  Law4411.models_iff.mpr (SimpleRewrites.Equation4427_implies_Equation4411 _ (SimpleRewrites.Equation4577_implies_Equation4427 _ (Equation4535_implies_Equation4577 _ (Equation4562_implies_Equation4535 _ (Equation4567_implies_Equation4562 _ (Law4567.models_iff.mp h))))))

/-- Law 4577 implies law 4411, along 4577 → 4427 → 4411. -/
theorem Law4577_implies_Law4411 : Law4577.implies Law4411 := fun {_G} _ h ↦
  Law4411.models_iff.mpr (SimpleRewrites.Equation4427_implies_Equation4411 _ (SimpleRewrites.Equation4577_implies_Equation4427 _ (Law4577.models_iff.mp h)))

/-- Law 4633 implies law 1, along 4633 → 4584 → 1. -/
theorem Law4633_implies_Law1 : Law4633.implies Law1 := fun {_G} _ h ↦
  Law1.models_iff.mpr (Equation4584_implies_Equation1 _ (RewriteHypothesis.Equation4633_implies_Equation4584 _ (Law4633.models_iff.mp h)))

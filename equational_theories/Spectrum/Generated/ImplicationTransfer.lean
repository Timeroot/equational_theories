import equational_theories.Spectrum.Full
import equational_theories.Generated.EquationSearch.theorems.Combined
import equational_theories.Generated.MagmaEgg.small._000
import equational_theories.Generated.MagmaEgg.small._001
import equational_theories.Generated.MagmaEgg.small._002
import equational_theories.Generated.MagmaEgg.small._003
import equational_theories.Generated.MagmaEgg.small._004
import equational_theories.Generated.MagmaEgg.small._005
import equational_theories.Generated.MagmaEgg.small._006
import equational_theories.Generated.MagmaEgg.small._007
import equational_theories.Generated.MagmaEgg.small._008
import equational_theories.Generated.MagmaEgg.small._009
import equational_theories.Generated.MagmaEgg.small._010
import equational_theories.Generated.MagmaEgg.small._011
import equational_theories.Generated.MagmaEgg.small._012
import equational_theories.Generated.MagmaEgg.small._013
import equational_theories.Generated.MagmaEgg.small._015
import equational_theories.Generated.MagmaEgg.small._016
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_vu
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_vu_wy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_vu_wz_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_wx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_wy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_wz
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_wz_zx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_wz_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_ux
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_ux_vu
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uz
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_vu
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_vy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_zx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_zy
import equational_theories.Generated.Singleton
import equational_theories.Generated.TrivialBruteforce.theorems.Apply
import equational_theories.Generated.TrivialBruteforce.theorems.Apply2
import equational_theories.Generated.TrivialBruteforce.theorems.RewriteHypothesisAndGoal
import equational_theories.Generated.VampireProven.Proofs1
import equational_theories.Generated.VampireProven.Proofs11
import equational_theories.Generated.VampireProven.Proofs12
import equational_theories.Generated.VampireProven.Proofs13
import equational_theories.Generated.VampireProven.Proofs2
import equational_theories.Generated.VampireProven.Proofs3
import equational_theories.Generated.VampireProven.Proofs4
import equational_theories.Generated.VampireProven.Proofs5
import equational_theories.Generated.VampireProven.Proofs6
import equational_theories.Generated.VampireProven.Proofs7
import equational_theories.Generated.VampireProven.Proofs8
import equational_theories.Subgraph

/-! Generated implication and duality transfers. No new proof assumptions. -/

open Law Law.MagmaLaw
namespace Spectrum.ImplicationTransfer

theorem sub_6_2 : Law6.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law6.models_iff (Fin n) M).mp hM
  exact Subgraph.Equation6_implies_Equation2 (Fin n) h

theorem sub_7_2 : Law7.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law7.models_iff (Fin n) M).mp hM
  exact Subgraph.Equation7_implies_Equation2 (Fin n) h

theorem sub_15_71 : Law15.Subspectral Law71 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law71.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law15.models_iff (Fin n) M).mp hM
  exact Apply.Equation15_implies_Equation71 (Fin n) h

theorem sub_18_1799 : Law18.Subspectral Law1799 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1799.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law18.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation18_implies_Equation1799 (Fin n) h

theorem sub_20_17 : Law20.Subspectral Law17 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law17.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law20.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation20_implies_Equation17 (Fin n) h

theorem sub_32_3199 : Law32.Subspectral Law3199 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3199.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law32.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation32_implies_Equation3199 (Fin n) h

theorem sub_33_3252 : Law33.Subspectral Law3252 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3252.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law33.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation33_implies_Equation3252 (Fin n) h

theorem sub_35_33 : Law35.Subspectral Law33 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law33.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law35.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation35_implies_Equation33 (Fin n) h

theorem sub_37_36 : Law37.Subspectral Law36 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law36.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law37.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation37_implies_Equation36 (Fin n) h

theorem sub_63_271 : Law63.Subspectral Law271 := by
  exact (spectrum_eq_of_isDual dual_63).subset

theorem sub_64_1555 : Law64.Subspectral Law1555 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1555.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law64.models_iff (Fin n) M).mp hM
  exact Apply.Equation64_implies_Equation1555 (Fin n) h

theorem sub_66_170 : Law66.Subspectral Law170 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law170.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law66.models_iff (Fin n) M).mp hM
  exact Equation66_implies_Equation170 (Fin n) h

theorem sub_66_281 : Law66.Subspectral Law281 := by
  exact (spectrum_eq_of_isDual dual_66).subset

theorem sub_71_6 : Law71.Subspectral Law6 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law6.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law71.models_iff (Fin n) M).mp hM
  exact Equation71_implies_Equation6 (Fin n) h

theorem sub_73_274 : Law73.Subspectral Law274 := by
  exact (spectrum_eq_of_isDual dual_73).subset

theorem sub_74_1005 : Law74.Subspectral Law1005 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1005.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law74.models_iff (Fin n) M).mp hM
  exact Equation74_implies_Equation1005 (Fin n) h

theorem sub_79_789 : Law79.Subspectral Law789 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law789.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law79.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation79_implies_Equation789 (Fin n) h

theorem sub_80_799 : Law80.Subspectral Law799 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law799.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law80.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation80_implies_Equation799 (Fin n) h

theorem sub_81_74 : Law81.Subspectral Law74 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law74.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law81.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation81_implies_Equation74 (Fin n) h

theorem sub_89_2 : Law89.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law89.models_iff (Fin n) M).mp hM
  exact Singleton.Equation89_implies_Equation2 (Fin n) h

theorem sub_91_89 : Law91.Subspectral Law89 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law89.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law91.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation91_implies_Equation89 (Fin n) h

theorem sub_92_91 : Law92.Subspectral Law91 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law91.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law92.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation92_implies_Equation91 (Fin n) h

theorem sub_93_925 : Law93.Subspectral Law925 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law925.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law93.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation93_implies_Equation925 (Fin n) h

theorem sub_95_91 : Law95.Subspectral Law91 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law91.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law95.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation95_implies_Equation91 (Fin n) h

theorem sub_98_976 : Law98.Subspectral Law976 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law976.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law98.models_iff (Fin n) M).mp hM
  exact Apply.Equation98_implies_Equation976 (Fin n) h

theorem sub_115_219 : Law115.Subspectral Law219 := by
  exact (spectrum_eq_of_isDual dual_115).subset

theorem sub_115_2734 : Law115.Subspectral Law2734 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2734.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law115.models_iff (Fin n) M).mp hM
  exact Equation115_implies_Equation2734 (Fin n) h

theorem sub_116_1758 : Law116.Subspectral Law1758 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1758.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law116.models_iff (Fin n) M).mp hM
  exact Apply.Equation116_implies_Equation1758 (Fin n) h

theorem sub_118_229 : Law118.Subspectral Law229 := by
  exact (spectrum_eq_of_isDual dual_118).subset

theorem sub_119_888 : Law119.Subspectral Law888 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law888.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law119.models_iff (Fin n) M).mp hM
  exact Apply.Equation119_implies_Equation888 (Fin n) h

theorem sub_121_1105 : Law121.Subspectral Law1105 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1105.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law121.models_iff (Fin n) M).mp hM
  exact Apply.Equation121_implies_Equation1105 (Fin n) h

theorem sub_122_1770 : Law122.Subspectral Law1770 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1770.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law122.models_iff (Fin n) M).mp hM
  exact Apply.Equation122_implies_Equation1770 (Fin n) h

theorem sub_123_1771 : Law123.Subspectral Law1771 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1771.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law123.models_iff (Fin n) M).mp hM
  exact Apply.Equation123_implies_Equation1771 (Fin n) h

theorem sub_125_73 : Law125.Subspectral Law73 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law73.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law125.models_iff (Fin n) M).mp hM
  exact Equation125_implies_Equation73 (Fin n) h

theorem sub_125_222 : Law125.Subspectral Law222 := by
  exact (spectrum_eq_of_isDual dual_125).subset

theorem sub_126_915 : Law126.Subspectral Law915 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law915.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law126.models_iff (Fin n) M).mp hM
  exact Apply.Equation126_implies_Equation915 (Fin n) h

theorem sub_128_1222 : Law128.Subspectral Law1222 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1222.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law128.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation128_implies_Equation1222 (Fin n) h

theorem sub_129_128 : Law129.Subspectral Law128 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law128.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law129.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation129_implies_Equation128 (Fin n) h

theorem sub_133_1329 : Law133.Subspectral Law1329 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1329.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law133.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation133_implies_Equation1329 (Fin n) h

theorem sub_135_1401 : Law135.Subspectral Law1401 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1401.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law135.models_iff (Fin n) M).mp hM
  exact Apply.Equation135_implies_Equation1401 (Fin n) h

theorem sub_136_1809 : Law136.Subspectral Law1809 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1809.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law136.models_iff (Fin n) M).mp hM
  exact Apply.Equation136_implies_Equation1809 (Fin n) h

theorem sub_137_959 : Law137.Subspectral Law959 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law959.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law137.models_iff (Fin n) M).mp hM
  exact Apply.Equation137_implies_Equation959 (Fin n) h

theorem sub_140_1399 : Law140.Subspectral Law1399 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1399.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law140.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation140_implies_Equation1399 (Fin n) h

theorem sub_141_139 : Law141.Subspectral Law139 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law139.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law141.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation141_implies_Equation139 (Fin n) h

theorem sub_141_1409 : Law141.Subspectral Law1409 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1409.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law141.models_iff (Fin n) M).mp hM
  exact Apply.Equation141_implies_Equation1409 (Fin n) h

theorem sub_143_1425 : Law143.Subspectral Law1425 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1425.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law143.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation143_implies_Equation1425 (Fin n) h

theorem sub_144_2 : Law144.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law144.models_iff (Fin n) M).mp hM
  exact Singleton.Equation144_implies_Equation2 (Fin n) h

theorem sub_145_144 : Law145.Subspectral Law144 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law144.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law145.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation145_implies_Equation144 (Fin n) h

theorem sub_147_2 : Law147.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law147.models_iff (Fin n) M).mp hM
  exact Singleton.Equation147_implies_Equation2 (Fin n) h

theorem sub_148_2 : Law148.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law148.models_iff (Fin n) M).mp hM
  exact Singleton.Equation148_implies_Equation2 (Fin n) h

theorem sub_149_2 : Law149.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law149.models_iff (Fin n) M).mp hM
  exact Singleton.Equation149_implies_Equation2 (Fin n) h

theorem sub_150_147 : Law150.Subspectral Law147 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law147.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law150.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation150_implies_Equation147 (Fin n) h

theorem sub_150_149 : Law150.Subspectral Law149 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law149.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law150.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation150_implies_Equation149 (Fin n) h

theorem sub_168_1487 : Law168.Subspectral Law1487 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1487.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law168.models_iff (Fin n) M).mp hM
  exact Apply.Equation168_implies_Equation1487 (Fin n) h

theorem sub_170_66 : Law170.Subspectral Law66 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law66.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law170.models_iff (Fin n) M).mp hM
  exact Equation170_implies_Equation66 (Fin n) h

theorem sub_170_177 : Law170.Subspectral Law177 := by
  exact (spectrum_eq_of_isDual dual_170).subset

theorem sub_174_2176 : Law174.Subspectral Law2176 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2176.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law174.models_iff (Fin n) M).mp hM
  exact Apply.Equation174_implies_Equation2176 (Fin n) h

theorem sub_175_1514 : Law175.Subspectral Law1514 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1514.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law175.models_iff (Fin n) M).mp hM
  exact Apply.Equation175_implies_Equation1514 (Fin n) h

theorem sub_177_170 : Law177.Subspectral Law170 := by
  exact (spectrum_eq_of_isDual dual_177).subset

theorem sub_180_18 : Law180.Subspectral Law18 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law18.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law180.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation180_implies_Equation18 (Fin n) h

theorem sub_183_1829 : Law183.Subspectral Law1829 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1829.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law183.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation183_implies_Equation1829 (Fin n) h

theorem sub_184_1831 : Law184.Subspectral Law1831 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1831.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law184.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation184_implies_Equation1831 (Fin n) h

theorem sub_185_178 : Law185.Subspectral Law178 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law178.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law185.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation185_implies_Equation178 (Fin n) h

theorem sub_187_482 : Law187.Subspectral Law482 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law482.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law187.models_iff (Fin n) M).mp hM
  exact Equation187_implies_Equation482 (Fin n) h

theorem sub_188_2215 : Law188.Subspectral Law2215 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2215.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law188.models_iff (Fin n) M).mp hM
  exact Apply.Equation188_implies_Equation2215 (Fin n) h

theorem sub_192_191 : Law192.Subspectral Law191 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law191.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law192.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation192_implies_Equation191 (Fin n) h

theorem sub_193_171 : Law193.Subspectral Law171 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law171.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law193.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation193_implies_Equation171 (Fin n) h

theorem sub_193_191 : Law193.Subspectral Law191 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law191.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law193.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation193_implies_Equation191 (Fin n) h

theorem sub_195_1948 : Law195.Subspectral Law1948 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1948.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law195.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation195_implies_Equation1948 (Fin n) h

theorem sub_196_1957 : Law196.Subspectral Law1957 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1957.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law196.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation196_implies_Equation1957 (Fin n) h

theorem sub_197_196 : Law197.Subspectral Law196 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law196.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law197.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation197_implies_Equation196 (Fin n) h

theorem sub_199_191 : Law199.Subspectral Law191 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law191.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law199.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation199_implies_Equation191 (Fin n) h

theorem sub_201_2008 : Law201.Subspectral Law2008 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2008.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law201.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation201_implies_Equation2008 (Fin n) h

theorem sub_202_193 : Law202.Subspectral Law193 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law193.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law202.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation202_implies_Equation193 (Fin n) h

theorem sub_219_115 : Law219.Subspectral Law115 := by
  exact (spectrum_eq_of_isDual dual_219).subset

theorem sub_220_2773 : Law220.Subspectral Law2773 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2773.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law220.models_iff (Fin n) M).mp hM
  exact Apply.Equation220_implies_Equation2773 (Fin n) h

theorem sub_222_125 : Law222.Subspectral Law125 := by
  exact (spectrum_eq_of_isDual dual_222).subset

theorem sub_227_1920 : Law227.Subspectral Law1920 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1920.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law227.models_iff (Fin n) M).mp hM
  exact Apply.Equation227_implies_Equation1920 (Fin n) h

theorem sub_229_118 : Law229.Subspectral Law118 := by
  exact (spectrum_eq_of_isDual dual_229).subset

theorem sub_235_2346 : Law235.Subspectral Law2346 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2346.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law235.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation235_implies_Equation2346 (Fin n) h

theorem sub_236_2358 : Law236.Subspectral Law2358 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2358.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law236.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation236_implies_Equation2358 (Fin n) h

theorem sub_241_240 : Law241.Subspectral Law240 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law240.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law241.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation241_implies_Equation240 (Fin n) h

theorem sub_243_2429 : Law243.Subspectral Law2429 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2429.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law243.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation243_implies_Equation2429 (Fin n) h

theorem sub_244_2439 : Law244.Subspectral Law2439 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2439.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law244.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation244_implies_Equation2439 (Fin n) h

theorem sub_271_63 : Law271.Subspectral Law63 := by
  exact (spectrum_eq_of_isDual dual_271).subset

theorem sub_272_3179 : Law272.Subspectral Law3179 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3179.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law272.models_iff (Fin n) M).mp hM
  exact Apply.Equation272_implies_Equation3179 (Fin n) h

theorem sub_274_73 : Law274.Subspectral Law73 := by
  exact (spectrum_eq_of_isDual dual_274).subset

theorem sub_275_2106 : Law275.Subspectral Law2106 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2106.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law275.models_iff (Fin n) M).mp hM
  exact Apply.Equation275_implies_Equation2106 (Fin n) h

theorem sub_277_2729 : Law277.Subspectral Law2729 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2729.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law277.models_iff (Fin n) M).mp hM
  exact Apply.Equation277_implies_Equation2729 (Fin n) h

theorem sub_279_278 : Law279.Subspectral Law278 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law278.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law279.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation279_implies_Equation278 (Fin n) h

theorem sub_281_66 : Law281.Subspectral Law66 := by
  exact (spectrum_eq_of_isDual dual_281).subset

theorem sub_282_2133 : Law282.Subspectral Law2133 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2133.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law282.models_iff (Fin n) M).mp hM
  exact Apply.Equation282_implies_Equation2133 (Fin n) h

theorem sub_284_2839 : Law284.Subspectral Law2839 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2839.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law284.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation284_implies_Equation2839 (Fin n) h

theorem sub_287_285 : Law287.Subspectral Law285 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law285.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law287.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation287_implies_Equation285 (Fin n) h

theorem sub_288_284 : Law288.Subspectral Law284 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law284.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law288.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation288_implies_Equation284 (Fin n) h

theorem sub_289_285 : Law289.Subspectral Law285 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law285.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law289.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation289_implies_Equation285 (Fin n) h

theorem sub_291_67 : Law291.Subspectral Law67 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law67.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law291.models_iff (Fin n) M).mp hM
  exact Equation291_implies_Equation67 (Fin n) h

theorem sub_292_1123 : Law292.Subspectral Law1123 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1123.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law292.models_iff (Fin n) M).mp hM
  exact Equation292_implies_Equation1123 (Fin n) h

theorem sub_296_2955 : Law296.Subspectral Law2955 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2955.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law296.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation296_implies_Equation2955 (Fin n) h

theorem sub_297_285 : Law297.Subspectral Law285 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law285.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law297.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation297_implies_Equation285 (Fin n) h

theorem sub_300_2999 : Law300.Subspectral Law2999 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2999.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law300.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation300_implies_Equation2999 (Fin n) h

theorem sub_467_3140 : Law467.Subspectral Law3140 := by
  exact (spectrum_eq_of_isDual dual_467).subset

theorem sub_471_472 : Law471.Subspectral Law472 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law472.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law471.models_iff (Fin n) M).mp hM
  exact Equation471_implies_Equation472 (Fin n) h

theorem sub_472_465 : Law472.Subspectral Law465 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law465.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law472.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation472_implies_Equation465 (Fin n) h

theorem sub_474_3113 : Law474.Subspectral Law3113 := by
  exact (spectrum_eq_of_isDual dual_474).subset

theorem sub_481_3161 : Law481.Subspectral Law3161 := by
  exact (spectrum_eq_of_isDual dual_481).subset

theorem sub_482_475 : Law482.Subspectral Law475 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law475.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law482.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation482_implies_Equation475 (Fin n) h

theorem sub_485_2 : Law485.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law485.models_iff (Fin n) M).mp hM
  exact Equation485_implies_Equation2 (Fin n) h

theorem sub_488_2788 : Law488.Subspectral Law2788 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2788.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law488.models_iff (Fin n) M).mp hM
  exact Equation488_implies_Equation2788 (Fin n) h

theorem sub_490_589 : Law490.Subspectral Law589 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law589.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law490.models_iff (Fin n) M).mp hM
  exact Equation490_implies_Equation589 (Fin n) h

theorem sub_493_2991 : Law493.Subspectral Law2991 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2991.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law493.models_iff (Fin n) M).mp hM
  exact Equation493_implies_Equation2991 (Fin n) h

theorem sub_496_2713 : Law496.Subspectral Law2713 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2713.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law496.models_iff (Fin n) M).mp hM
  exact Equation496_implies_Equation2713 (Fin n) h

theorem sub_499_486 : Law499.Subspectral Law486 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law486.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law499.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation499_implies_Equation486 (Fin n) h

theorem sub_501_3106 : Law501.Subspectral Law3106 := by
  exact (spectrum_eq_of_isDual dual_501).subset

theorem sub_502_2 : Law502.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law502.models_iff (Fin n) M).mp hM
  exact Equation502_implies_Equation2 (Fin n) h

theorem sub_505_2 : Law505.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law505.models_iff (Fin n) M).mp hM
  exact Equation505_implies_Equation2 (Fin n) h

theorem sub_507_890 : Law507.Subspectral Law890 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law890.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law507.models_iff (Fin n) M).mp hM
  exact Equation507_implies_Equation890 (Fin n) h

theorem sub_509_502 : Law509.Subspectral Law502 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law502.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law509.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation509_implies_Equation502 (Fin n) h

theorem sub_512_2 : Law512.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law512.models_iff (Fin n) M).mp hM
  exact Equation512_implies_Equation2 (Fin n) h

theorem sub_514_37 : Law514.Subspectral Law37 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law37.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law514.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation514_implies_Equation37 (Fin n) h

theorem sub_515_2 : Law515.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law515.models_iff (Fin n) M).mp hM
  exact Singleton.Equation515_implies_Equation2 (Fin n) h

theorem sub_517_2 : Law517.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law517.models_iff (Fin n) M).mp hM
  exact Singleton.Equation517_implies_Equation2 (Fin n) h

theorem sub_518_2 : Law518.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law518.models_iff (Fin n) M).mp hM
  exact Singleton.Equation518_implies_Equation2 (Fin n) h

theorem sub_519_515 : Law519.Subspectral Law515 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law515.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law519.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation519_implies_Equation515 (Fin n) h

theorem sub_519_518 : Law519.Subspectral Law518 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law518.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law519.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation519_implies_Equation518 (Fin n) h

theorem sub_521_2918 : Law521.Subspectral Law2918 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2918.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law521.models_iff (Fin n) M).mp hM
  exact Equation521_implies_Equation2918 (Fin n) h

theorem sub_523_502 : Law523.Subspectral Law502 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law502.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law523.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation523_implies_Equation502 (Fin n) h

theorem sub_525_519 : Law525.Subspectral Law519 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law519.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law525.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation525_implies_Equation519 (Fin n) h

theorem sub_526_2 : Law526.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law526.models_iff (Fin n) M).mp hM
  exact Singleton.Equation526_implies_Equation2 (Fin n) h

theorem sub_529_2 : Law529.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law529.models_iff (Fin n) M).mp hM
  exact Singleton.Equation529_implies_Equation2 (Fin n) h

theorem sub_530_2 : Law530.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law530.models_iff (Fin n) M).mp hM
  exact Singleton.Equation530_implies_Equation2 (Fin n) h

theorem sub_531_529 : Law531.Subspectral Law529 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law529.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law531.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation531_implies_Equation529 (Fin n) h

theorem sub_531_530 : Law531.Subspectral Law530 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law530.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law531.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation531_implies_Equation530 (Fin n) h

theorem sub_533_521 : Law533.Subspectral Law521 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law521.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law533.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation533_implies_Equation521 (Fin n) h

theorem sub_535_534 : Law535.Subspectral Law534 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law534.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law535.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation535_implies_Equation534 (Fin n) h

theorem sub_536_509 : Law536.Subspectral Law509 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law509.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law536.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation536_implies_Equation509 (Fin n) h

theorem sub_538_2772 : Law538.Subspectral Law2772 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2772.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law538.models_iff (Fin n) M).mp hM
  exact Equation538_implies_Equation2772 (Fin n) h

theorem sub_539_2 : Law539.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law539.models_iff (Fin n) M).mp hM
  exact Equation539_implies_Equation2 (Fin n) h

theorem sub_540_465 : Law540.Subspectral Law465 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law465.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law540.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation540_implies_Equation465 (Fin n) h

theorem sub_542_2 : Law542.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law542.models_iff (Fin n) M).mp hM
  exact Equation542_implies_Equation2 (Fin n) h

theorem sub_544_468 : Law544.Subspectral Law468 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law468.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law544.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation544_implies_Equation468 (Fin n) h

theorem sub_544_542 : Law544.Subspectral Law542 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law542.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law544.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation544_implies_Equation542 (Fin n) h

theorem sub_546_1967 : Law546.Subspectral Law1967 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1967.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law546.models_iff (Fin n) M).mp hM
  exact Equation546_implies_Equation1967 (Fin n) h

theorem sub_546_3185 : Law546.Subspectral Law3185 := by
  exact (spectrum_eq_of_isDual dual_546).subset

theorem sub_551_547 : Law551.Subspectral Law547 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law547.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law551.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation551_implies_Equation547 (Fin n) h

theorem sub_553_548 : Law553.Subspectral Law548 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law548.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law553.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation553_implies_Equation548 (Fin n) h

theorem sub_555_874 : Law555.Subspectral Law874 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law874.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law555.models_iff (Fin n) M).mp hM
  exact Equation555_implies_Equation874 (Fin n) h

theorem sub_556_775 : Law556.Subspectral Law775 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law775.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law556.models_iff (Fin n) M).mp hM
  exact Equation556_implies_Equation775 (Fin n) h

theorem sub_556_1131 : Law556.Subspectral Law1131 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1131.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law556.models_iff (Fin n) M).mp hM
  exact Equation556_implies_Equation1131 (Fin n) h

theorem sub_556_1355 : Law556.Subspectral Law1355 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1355.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law556.models_iff (Fin n) M).mp hM
  exact Equation556_implies_Equation1355 (Fin n) h

theorem sub_556_2982 : Law556.Subspectral Law2982 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2982.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law556.models_iff (Fin n) M).mp hM
  exact Equation556_implies_Equation2982 (Fin n) h

theorem sub_556_3128 : Law556.Subspectral Law3128 := by
  exact (spectrum_eq_of_isDual dual_556).subset

theorem sub_560_559 : Law560.Subspectral Law559 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law559.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law560.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation560_implies_Equation559 (Fin n) h

theorem sub_561_559 : Law561.Subspectral Law559 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law559.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law561.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation561_implies_Equation559 (Fin n) h

theorem sub_563_561 : Law563.Subspectral Law561 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law561.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law563.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation563_implies_Equation561 (Fin n) h

theorem sub_565_475 : Law565.Subspectral Law475 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law475.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law565.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation565_implies_Equation475 (Fin n) h

theorem sub_568_567 : Law568.Subspectral Law567 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law567.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law568.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation568_implies_Equation567 (Fin n) h

theorem sub_569_568 : Law569.Subspectral Law568 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law568.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law569.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation569_implies_Equation568 (Fin n) h

theorem sub_570_565 : Law570.Subspectral Law565 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law565.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law570.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation570_implies_Equation565 (Fin n) h

theorem sub_574_465 : Law574.Subspectral Law465 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law465.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law574.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation574_implies_Equation465 (Fin n) h

theorem sub_578_577 : Law578.Subspectral Law577 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law577.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law578.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation578_implies_Equation577 (Fin n) h

theorem sub_582_581 : Law582.Subspectral Law581 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law581.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law582.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation582_implies_Equation581 (Fin n) h

theorem sub_584_576 : Law584.Subspectral Law576 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law576.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law584.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation584_implies_Equation576 (Fin n) h

theorem sub_586_581 : Law586.Subspectral Law581 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law581.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law586.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation586_implies_Equation581 (Fin n) h

theorem sub_587_585 : Law587.Subspectral Law585 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law585.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law587.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation587_implies_Equation585 (Fin n) h

theorem sub_587_586 : Law587.Subspectral Law586 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law586.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law587.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation587_implies_Equation586 (Fin n) h

theorem sub_589_521 : Law589.Subspectral Law521 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law521.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law589.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation589_implies_Equation521 (Fin n) h

theorem sub_591_485 : Law591.Subspectral Law485 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law485.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law591.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation591_implies_Equation485 (Fin n) h

theorem sub_592_540 : Law592.Subspectral Law540 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law540.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law592.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation592_implies_Equation540 (Fin n) h

theorem sub_594_587 : Law594.Subspectral Law587 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law587.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law594.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation594_implies_Equation587 (Fin n) h

theorem sub_597_544 : Law597.Subspectral Law544 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law544.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law597.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation597_implies_Equation544 (Fin n) h

theorem sub_599_597 : Law599.Subspectral Law597 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law597.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law599.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation599_implies_Equation597 (Fin n) h

theorem sub_600_581 : Law600.Subspectral Law581 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law581.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law600.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation600_implies_Equation581 (Fin n) h

theorem sub_601_581 : Law601.Subspectral Law581 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law581.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law601.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation601_implies_Equation581 (Fin n) h

theorem sub_602_600 : Law602.Subspectral Law600 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law600.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law602.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation602_implies_Equation600 (Fin n) h

theorem sub_602_601 : Law602.Subspectral Law601 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law601.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law602.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation602_implies_Equation601 (Fin n) h

theorem sub_605_581 : Law605.Subspectral Law581 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law581.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law605.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation605_implies_Equation581 (Fin n) h

theorem sub_606_581 : Law606.Subspectral Law581 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law581.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law606.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation606_implies_Equation581 (Fin n) h

theorem sub_609_607 : Law609.Subspectral Law607 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law607.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law609.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation609_implies_Equation607 (Fin n) h

theorem sub_611_606 : Law611.Subspectral Law606 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law606.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law611.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation611_implies_Equation606 (Fin n) h

theorem sub_612_2 : Law612.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law612.models_iff (Fin n) M).mp hM
  exact Singleton.Equation612_implies_Equation2 (Fin n) h

theorem sub_613_612 : Law613.Subspectral Law612 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law612.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law613.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation613_implies_Equation612 (Fin n) h

theorem sub_667_2900 : Law667.Subspectral Law2900 := by
  exact (spectrum_eq_of_isDual dual_667).subset

theorem sub_670_2937 : Law670.Subspectral Law2937 := by
  exact (spectrum_eq_of_isDual dual_670).subset

theorem sub_671_673 : Law671.Subspectral Law673 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law673.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law671.models_iff (Fin n) M).mp hM
  exact Equation671_implies_Equation673 (Fin n) h

theorem sub_673_1294 : Law673.Subspectral Law1294 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1294.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law673.models_iff (Fin n) M).mp hM
  exact Equation673_implies_Equation1294 (Fin n) h

theorem sub_675_668 : Law675.Subspectral Law668 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law668.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law675.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation675_implies_Equation668 (Fin n) h

theorem sub_677_2910 : Law677.Subspectral Law2910 := by
  exact (spectrum_eq_of_isDual dual_677).subset

theorem sub_688_2 : Law688.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law688.models_iff (Fin n) M).mp hM
  exact Equation688_implies_Equation2 (Fin n) h

theorem sub_689_688 : Law689.Subspectral Law688 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law688.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law689.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation689_implies_Equation688 (Fin n) h

theorem sub_691_1976 : Law691.Subspectral Law1976 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1976.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law691.models_iff (Fin n) M).mp hM
  exact Equation691_implies_Equation1976 (Fin n) h

theorem sub_693_681 : Law693.Subspectral Law681 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law681.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law693.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation693_implies_Equation681 (Fin n) h

theorem sub_695_3008 : Law695.Subspectral Law3008 := by
  exact (spectrum_eq_of_isDual dual_695).subset

theorem sub_696_2 : Law696.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law696.models_iff (Fin n) M).mp hM
  exact Equation696_implies_Equation2 (Fin n) h

theorem sub_697_696 : Law697.Subspectral Law696 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law696.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law697.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation697_implies_Equation696 (Fin n) h

theorem sub_699_673 : Law699.Subspectral Law673 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law673.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law699.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation699_implies_Equation673 (Fin n) h

theorem sub_704_2903 : Law704.Subspectral Law2903 := by
  exact (spectrum_eq_of_isDual dual_704).subset

theorem sub_705_2901 : Law705.Subspectral Law2901 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2901.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law705.models_iff (Fin n) M).mp hM
  exact Equation705_implies_Equation2901 (Fin n) h

theorem sub_710_2 : Law710.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law710.models_iff (Fin n) M).mp hM
  exact Equation710_implies_Equation2 (Fin n) h

theorem sub_712_710 : Law712.Subspectral Law710 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law710.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law712.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation712_implies_Equation710 (Fin n) h

theorem sub_717_7 : Law717.Subspectral Law7 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law7.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law717.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation717_implies_Equation7 (Fin n) h

theorem sub_718_2 : Law718.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law718.models_iff (Fin n) M).mp hM
  exact Singleton.Equation718_implies_Equation2 (Fin n) h

theorem sub_720_2 : Law720.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law720.models_iff (Fin n) M).mp hM
  exact Singleton.Equation720_implies_Equation2 (Fin n) h

theorem sub_721_720 : Law721.Subspectral Law720 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law720.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law721.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation721_implies_Equation720 (Fin n) h

theorem sub_722_715 : Law722.Subspectral Law715 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law715.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law722.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation722_implies_Equation715 (Fin n) h

theorem sub_724_2365 : Law724.Subspectral Law2365 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2365.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law724.models_iff (Fin n) M).mp hM
  exact Equation724_implies_Equation2365 (Fin n) h

theorem sub_726_724 : Law726.Subspectral Law724 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law724.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law726.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation726_implies_Equation724 (Fin n) h

theorem sub_728_2 : Law728.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law728.models_iff (Fin n) M).mp hM
  exact Singleton.Equation728_implies_Equation2 (Fin n) h

theorem sub_729_2 : Law729.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law729.models_iff (Fin n) M).mp hM
  exact Singleton.Equation729_implies_Equation2 (Fin n) h

theorem sub_730_728 : Law730.Subspectral Law728 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law728.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law730.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation730_implies_Equation728 (Fin n) h

theorem sub_732_730 : Law732.Subspectral Law730 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law730.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law732.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation732_implies_Equation730 (Fin n) h

theorem sub_733_717 : Law733.Subspectral Law717 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law717.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law733.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation733_implies_Equation717 (Fin n) h

theorem sub_734_733 : Law734.Subspectral Law733 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law733.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law734.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation734_implies_Equation733 (Fin n) h

theorem sub_738_733 : Law738.Subspectral Law733 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law733.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law738.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation738_implies_Equation733 (Fin n) h

theorem sub_739_712 : Law739.Subspectral Law712 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law712.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law739.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation739_implies_Equation712 (Fin n) h

theorem sub_739_722 : Law739.Subspectral Law722 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law722.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law739.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation739_implies_Equation722 (Fin n) h

theorem sub_745_2704 : Law745.Subspectral Law2704 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2704.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law745.models_iff (Fin n) M).mp hM
  exact Equation745_implies_Equation2704 (Fin n) h

theorem sub_749_556 : Law749.Subspectral Law556 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law556.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law749.models_iff (Fin n) M).mp hM
  exact Equation749_implies_Equation556 (Fin n) h

theorem sub_750_751 : Law750.Subspectral Law751 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law751.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law750.models_iff (Fin n) M).mp hM
  exact Equation750_implies_Equation751 (Fin n) h

theorem sub_751_2932 : Law751.Subspectral Law2932 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2932.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law751.models_iff (Fin n) M).mp hM
  exact Equation751_implies_Equation2932 (Fin n) h

theorem sub_753_745 : Law753.Subspectral Law745 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law745.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law753.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation753_implies_Equation745 (Fin n) h

theorem sub_755_674 : Law755.Subspectral Law674 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law674.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law755.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation755_implies_Equation674 (Fin n) h

theorem sub_763_762 : Law763.Subspectral Law762 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law762.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law763.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation763_implies_Equation762 (Fin n) h

theorem sub_764_762 : Law764.Subspectral Law762 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law762.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law764.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation764_implies_Equation762 (Fin n) h

theorem sub_771_770 : Law771.Subspectral Law770 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law770.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law771.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation771_implies_Equation770 (Fin n) h

theorem sub_772_771 : Law772.Subspectral Law771 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law771.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law772.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation772_implies_Equation771 (Fin n) h

theorem sub_773_770 : Law773.Subspectral Law770 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law770.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law773.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation773_implies_Equation770 (Fin n) h

theorem sub_775_2928 : Law775.Subspectral Law2928 := by
  exact (spectrum_eq_of_isDual dual_775).subset

theorem sub_776_792 : Law776.Subspectral Law792 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law792.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law776.models_iff (Fin n) M).mp hM
  exact Equation776_implies_Equation792 (Fin n) h

theorem sub_783_781 : Law783.Subspectral Law781 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law781.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law783.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation783_implies_Equation781 (Fin n) h

theorem sub_790_787 : Law790.Subspectral Law787 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law787.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law790.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation790_implies_Equation787 (Fin n) h

theorem sub_792_1923 : Law792.Subspectral Law1923 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1923.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law792.models_iff (Fin n) M).mp hM
  exact Equation792_implies_Equation1923 (Fin n) h

theorem sub_793_742 : Law793.Subspectral Law742 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law742.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law793.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation793_implies_Equation742 (Fin n) h

theorem sub_800_730 : Law800.Subspectral Law730 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law730.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law800.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation800_implies_Equation730 (Fin n) h

theorem sub_802_800 : Law802.Subspectral Law800 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law800.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law802.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation802_implies_Equation800 (Fin n) h

theorem sub_805_803 : Law805.Subspectral Law803 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law803.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law805.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation805_implies_Equation803 (Fin n) h

theorem sub_807_805 : Law807.Subspectral Law805 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law805.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law807.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation807_implies_Equation805 (Fin n) h

theorem sub_810_809 : Law810.Subspectral Law809 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law809.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law810.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation810_implies_Equation809 (Fin n) h

theorem sub_813_754 : Law813.Subspectral Law754 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law754.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law813.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation813_implies_Equation754 (Fin n) h

theorem sub_873_2734 : Law873.Subspectral Law2734 := by
  exact (spectrum_eq_of_isDual dual_873).subset

theorem sub_874_3114 : Law874.Subspectral Law3114 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3114.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law874.models_iff (Fin n) M).mp hM
  exact Equation874_implies_Equation3114 (Fin n) h

theorem sub_876_2984 : Law876.Subspectral Law2984 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2984.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law876.models_iff (Fin n) M).mp hM
  exact Equation876_implies_Equation2984 (Fin n) h

theorem sub_877_2 : Law877.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law877.models_iff (Fin n) M).mp hM
  exact Equation877_implies_Equation2 (Fin n) h

theorem sub_878_871 : Law878.Subspectral Law871 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law871.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law878.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation878_implies_Equation871 (Fin n) h

theorem sub_880_219 : Law880.Subspectral Law219 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law219.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law880.models_iff (Fin n) M).mp hM
  exact Equation880_implies_Equation219 (Fin n) h

theorem sub_880_2707 : Law880.Subspectral Law2707 := by
  exact (spectrum_eq_of_isDual dual_880).subset

theorem sub_883_2744 : Law883.Subspectral Law2744 := by
  exact (spectrum_eq_of_isDual dual_883).subset

theorem sub_887_2755 : Law887.Subspectral Law2755 := by
  exact (spectrum_eq_of_isDual dual_887).subset

theorem sub_888_881 : Law888.Subspectral Law881 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law881.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law888.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation888_implies_Equation881 (Fin n) h

theorem sub_892_891 : Law892.Subspectral Law891 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law891.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law892.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation892_implies_Equation891 (Fin n) h

theorem sub_894_2 : Law894.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law894.models_iff (Fin n) M).mp hM
  exact Equation894_implies_Equation2 (Fin n) h

theorem sub_895_1571 : Law895.Subspectral Law1571 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1571.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law895.models_iff (Fin n) M).mp hM
  exact Equation895_implies_Equation1571 (Fin n) h

theorem sub_895_2789 : Law895.Subspectral Law2789 := by
  exact (spectrum_eq_of_isDual dual_895).subset

theorem sub_896_894 : Law896.Subspectral Law894 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law894.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law896.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation896_implies_Equation894 (Fin n) h

theorem sub_898_2316 : Law898.Subspectral Law2316 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2316.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law898.models_iff (Fin n) M).mp hM
  exact Equation898_implies_Equation2316 (Fin n) h

theorem sub_898_2805 : Law898.Subspectral Law2805 := by
  exact (spectrum_eq_of_isDual dual_898).subset

theorem sub_899_15 : Law899.Subspectral Law15 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law15.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law899.models_iff (Fin n) M).mp hM
  exact Equation899_implies_Equation15 (Fin n) h

theorem sub_900_884 : Law900.Subspectral Law884 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law884.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law900.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation900_implies_Equation884 (Fin n) h

theorem sub_902_894 : Law902.Subspectral Law894 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law894.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law902.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation902_implies_Equation894 (Fin n) h

theorem sub_903_891 : Law903.Subspectral Law891 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law891.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law903.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation903_implies_Equation891 (Fin n) h

theorem sub_907_2700 : Law907.Subspectral Law2700 := by
  exact (spectrum_eq_of_isDual dual_907).subset

theorem sub_918_2 : Law918.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law918.models_iff (Fin n) M).mp hM
  exact Equation918_implies_Equation2 (Fin n) h

theorem sub_920_92 : Law920.Subspectral Law92 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law92.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law920.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation920_implies_Equation92 (Fin n) h

theorem sub_923_2 : Law923.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law923.models_iff (Fin n) M).mp hM
  exact Singleton.Equation923_implies_Equation2 (Fin n) h

theorem sub_924_2 : Law924.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law924.models_iff (Fin n) M).mp hM
  exact Singleton.Equation924_implies_Equation2 (Fin n) h

theorem sub_925_918 : Law925.Subspectral Law918 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law918.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law925.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation925_implies_Equation918 (Fin n) h

theorem sub_927_741 : Law927.Subspectral Law741 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law741.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law927.models_iff (Fin n) M).mp hM
  exact Equation927_implies_Equation741 (Fin n) h

theorem sub_932_2 : Law932.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law932.models_iff (Fin n) M).mp hM
  exact Singleton.Equation932_implies_Equation2 (Fin n) h

theorem sub_933_932 : Law933.Subspectral Law932 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law932.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law933.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation933_implies_Equation932 (Fin n) h

theorem sub_935_2 : Law935.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law935.models_iff (Fin n) M).mp hM
  exact Singleton.Equation935_implies_Equation2 (Fin n) h

theorem sub_936_2 : Law936.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law936.models_iff (Fin n) M).mp hM
  exact Singleton.Equation936_implies_Equation2 (Fin n) h

theorem sub_937_935 : Law937.Subspectral Law935 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law935.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law937.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation937_implies_Equation935 (Fin n) h

theorem sub_937_936 : Law937.Subspectral Law936 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law936.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law937.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation937_implies_Equation936 (Fin n) h

theorem sub_939_2 : Law939.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law939.models_iff (Fin n) M).mp hM
  exact Singleton.Equation939_implies_Equation2 (Fin n) h

theorem sub_940_2 : Law940.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law940.models_iff (Fin n) M).mp hM
  exact Singleton.Equation940_implies_Equation2 (Fin n) h

theorem sub_941_2 : Law941.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law941.models_iff (Fin n) M).mp hM
  exact Singleton.Equation941_implies_Equation2 (Fin n) h

theorem sub_942_939 : Law942.Subspectral Law939 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law939.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law942.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation942_implies_Equation939 (Fin n) h

theorem sub_942_941 : Law942.Subspectral Law941 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law941.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law942.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation942_implies_Equation941 (Fin n) h

theorem sub_949_2776 : Law949.Subspectral Law2776 := by
  exact (spectrum_eq_of_isDual dual_949).subset

theorem sub_950_948 : Law950.Subspectral Law948 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law948.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law950.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation950_implies_Equation948 (Fin n) h

theorem sub_953_2 : Law953.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law953.models_iff (Fin n) M).mp hM
  exact Subgraph.Equation953_implies_Equation2 (Fin n) h

theorem sub_954_871 : Law954.Subspectral Law871 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law871.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law954.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation954_implies_Equation871 (Fin n) h

theorem sub_956_948 : Law956.Subspectral Law948 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law948.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law956.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation956_implies_Equation948 (Fin n) h

theorem sub_957_953 : Law957.Subspectral Law953 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law953.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law957.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation957_implies_Equation953 (Fin n) h

theorem sub_958_948 : Law958.Subspectral Law948 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law948.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law958.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation958_implies_Equation948 (Fin n) h

theorem sub_959_878 : Law959.Subspectral Law878 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law878.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law959.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation959_implies_Equation878 (Fin n) h

theorem sub_961_3026 : Law961.Subspectral Law3026 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3026.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law961.models_iff (Fin n) M).mp hM
  exact Equation961_implies_Equation3026 (Fin n) h

theorem sub_962_546 : Law962.Subspectral Law546 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law546.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law962.models_iff (Fin n) M).mp hM
  exact Equation962_implies_Equation546 (Fin n) h

theorem sub_962_2722 : Law962.Subspectral Law2722 := by
  exact (spectrum_eq_of_isDual dual_962).subset

theorem sub_965_96 : Law965.Subspectral Law96 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law96.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law965.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation965_implies_Equation96 (Fin n) h

theorem sub_966_2 : Law966.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law966.models_iff (Fin n) M).mp hM
  exact Singleton.Equation966_implies_Equation2 (Fin n) h

theorem sub_969_967 : Law969.Subspectral Law967 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law967.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law969.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation969_implies_Equation967 (Fin n) h

theorem sub_970_97 : Law970.Subspectral Law97 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law97.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law970.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation970_implies_Equation97 (Fin n) h

theorem sub_971_2 : Law971.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law971.models_iff (Fin n) M).mp hM
  exact Singleton.Equation971_implies_Equation2 (Fin n) h

theorem sub_973_2 : Law973.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law973.models_iff (Fin n) M).mp hM
  exact Singleton.Equation973_implies_Equation2 (Fin n) h

theorem sub_974_2 : Law974.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law974.models_iff (Fin n) M).mp hM
  exact Singleton.Equation974_implies_Equation2 (Fin n) h

theorem sub_976_973 : Law976.Subspectral Law973 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law973.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law976.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation976_implies_Equation973 (Fin n) h

theorem sub_983_2 : Law983.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law983.models_iff (Fin n) M).mp hM
  exact Singleton.Equation983_implies_Equation2 (Fin n) h

theorem sub_984_983 : Law984.Subspectral Law983 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law983.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law984.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation984_implies_Equation983 (Fin n) h

theorem sub_986_984 : Law986.Subspectral Law984 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law984.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law986.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation986_implies_Equation984 (Fin n) h

theorem sub_987_2 : Law987.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law987.models_iff (Fin n) M).mp hM
  exact Singleton.Equation987_implies_Equation2 (Fin n) h

theorem sub_988_2 : Law988.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law988.models_iff (Fin n) M).mp hM
  exact Singleton.Equation988_implies_Equation2 (Fin n) h

theorem sub_990_2 : Law990.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law990.models_iff (Fin n) M).mp hM
  exact Singleton.Equation990_implies_Equation2 (Fin n) h

theorem sub_992_982 : Law992.Subspectral Law982 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law982.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law992.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation992_implies_Equation982 (Fin n) h

theorem sub_995_890 : Law995.Subspectral Law890 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law890.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law995.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation995_implies_Equation890 (Fin n) h

theorem sub_996_979 : Law996.Subspectral Law979 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law979.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law996.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation996_implies_Equation979 (Fin n) h

theorem sub_997_891 : Law997.Subspectral Law891 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law891.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law997.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation997_implies_Equation891 (Fin n) h

theorem sub_998_946 : Law998.Subspectral Law946 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law946.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law998.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation998_implies_Equation946 (Fin n) h

theorem sub_1000_894 : Law1000.Subspectral Law894 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law894.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1000.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1000_implies_Equation894 (Fin n) h

theorem sub_1003_896 : Law1003.Subspectral Law896 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law896.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1003.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1003_implies_Equation896 (Fin n) h

theorem sub_1003_1000 : Law1003.Subspectral Law1000 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1000.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1003.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1003_implies_Equation1000 (Fin n) h

theorem sub_1005_2 : Law1005.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1005.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1005_implies_Equation2 (Fin n) h

theorem sub_1006_953 : Law1006.Subspectral Law953 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law953.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1006.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1006_implies_Equation953 (Fin n) h

theorem sub_1007_891 : Law1007.Subspectral Law891 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law891.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1007.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1007_implies_Equation891 (Fin n) h

theorem sub_1010_1008 : Law1010.Subspectral Law1008 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1008.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1010.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1010_implies_Equation1008 (Fin n) h

theorem sub_1019_1018 : Law1019.Subspectral Law1018 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1018.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1019.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1019_implies_Equation1018 (Fin n) h

theorem sub_1074_2 : Law1074.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1074.models_iff (Fin n) M).mp hM
  exact Equation1074_implies_Equation2 (Fin n) h

theorem sub_1076_2531 : Law1076.Subspectral Law2531 := by
  exact (spectrum_eq_of_isDual dual_1076).subset

theorem sub_1079_2 : Law1079.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1079.models_iff (Fin n) M).mp hM
  exact Equation1079_implies_Equation2 (Fin n) h

theorem sub_1080_2 : Law1080.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1080.models_iff (Fin n) M).mp hM
  exact Equation1080_implies_Equation2 (Fin n) h

theorem sub_1081_1079 : Law1081.Subspectral Law1079 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1079.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1081.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1081_implies_Equation1079 (Fin n) h

theorem sub_1081_1080 : Law1081.Subspectral Law1080 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1080.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1081.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1081_implies_Equation1080 (Fin n) h

theorem sub_1083_2504 : Law1083.Subspectral Law2504 := by
  exact (spectrum_eq_of_isDual dual_1083).subset

theorem sub_1084_2 : Law1084.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1084.models_iff (Fin n) M).mp hM
  exact Equation1084_implies_Equation2 (Fin n) h

theorem sub_1089_2 : Law1089.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1089.models_iff (Fin n) M).mp hM
  exact Equation1089_implies_Equation2 (Fin n) h

theorem sub_1093_2 : Law1093.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1093.models_iff (Fin n) M).mp hM
  exact Equation1093_implies_Equation2 (Fin n) h

theorem sub_1094_2 : Law1094.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1094.models_iff (Fin n) M).mp hM
  exact Equation1094_implies_Equation2 (Fin n) h

theorem sub_1095_1074 : Law1095.Subspectral Law1074 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1074.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1095.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1095_implies_Equation1074 (Fin n) h

theorem sub_1097_2 : Law1097.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1097.models_iff (Fin n) M).mp hM
  exact Equation1097_implies_Equation2 (Fin n) h

theorem sub_1099_1097 : Law1099.Subspectral Law1097 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1097.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1099.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1099_implies_Equation1097 (Fin n) h

theorem sub_1105_1097 : Law1105.Subspectral Law1097 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1097.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1105.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1105_implies_Equation1097 (Fin n) h

theorem sub_1106_1102 : Law1106.Subspectral Law1102 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1102.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1106.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1106_implies_Equation1102 (Fin n) h

theorem sub_1110_2497 : Law1110.Subspectral Law2497 := by
  exact (spectrum_eq_of_isDual dual_1110).subset

theorem sub_1111_2 : Law1111.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1111.models_iff (Fin n) M).mp hM
  exact Equation1111_implies_Equation2 (Fin n) h

theorem sub_1114_2 : Law1114.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1114.models_iff (Fin n) M).mp hM
  exact Equation1114_implies_Equation2 (Fin n) h

theorem sub_1116_2 : Law1116.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1116.models_iff (Fin n) M).mp hM
  exact Equation1116_implies_Equation2 (Fin n) h

theorem sub_1121_2 : Law1121.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1121.models_iff (Fin n) M).mp hM
  exact Equation1121_implies_Equation2 (Fin n) h

theorem sub_1123_2 : Law1123.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1123.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1123_implies_Equation2 (Fin n) h

theorem sub_1124_2 : Law1124.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1124.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1124_implies_Equation2 (Fin n) h

theorem sub_1126_2 : Law1126.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1126.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1126_implies_Equation2 (Fin n) h

theorem sub_1127_2 : Law1127.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1127.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1127_implies_Equation2 (Fin n) h

theorem sub_1128_1127 : Law1128.Subspectral Law1127 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1127.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1128.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1128_implies_Equation1127 (Fin n) h

theorem sub_1130_2 : Law1130.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1130.models_iff (Fin n) M).mp hM
  exact Equation1130_implies_Equation2 (Fin n) h

theorem sub_1131_2511 : Law1131.Subspectral Law2511 := by
  exact (spectrum_eq_of_isDual dual_1131).subset

theorem sub_1132_1111 : Law1132.Subspectral Law1111 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1111.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1132.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1132_implies_Equation1111 (Fin n) h

theorem sub_1134_2 : Law1134.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1134.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1134_implies_Equation2 (Fin n) h

theorem sub_1135_2 : Law1135.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1135.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1135_implies_Equation2 (Fin n) h

theorem sub_1136_1134 : Law1136.Subspectral Law1134 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1134.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1136.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1136_implies_Equation1134 (Fin n) h

theorem sub_1138_2 : Law1138.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1138.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1138_implies_Equation2 (Fin n) h

theorem sub_1139_2 : Law1139.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1139.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1139_implies_Equation2 (Fin n) h

theorem sub_1140_1139 : Law1140.Subspectral Law1139 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1139.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1140.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1140_implies_Equation1139 (Fin n) h

theorem sub_1142_2 : Law1142.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1142.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1142_implies_Equation2 (Fin n) h

theorem sub_1143_2 : Law1143.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1143.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1143_implies_Equation2 (Fin n) h

theorem sub_1144_2 : Law1144.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1144.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1144_implies_Equation2 (Fin n) h

theorem sub_1145_1142 : Law1145.Subspectral Law1142 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1142.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1145.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1145_implies_Equation1142 (Fin n) h

theorem sub_1145_1144 : Law1145.Subspectral Law1144 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1144.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1145.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1145_implies_Equation1144 (Fin n) h

theorem sub_1151_689 : Law1151.Subspectral Law689 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law689.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1151.models_iff (Fin n) M).mp hM
  exact Equation1151_implies_Equation689 (Fin n) h

theorem sub_1153_1151 : Law1153.Subspectral Law1151 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1151.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1153.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1153_implies_Equation1151 (Fin n) h

theorem sub_1157_1156 : Law1157.Subspectral Law1156 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1156.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1157.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1157_implies_Equation1156 (Fin n) h

theorem sub_1159_1151 : Law1159.Subspectral Law1151 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1151.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1159.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1159_implies_Equation1151 (Fin n) h

theorem sub_1160_1156 : Law1160.Subspectral Law1156 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1156.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1160.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1160_implies_Equation1156 (Fin n) h

theorem sub_1162_1161 : Law1162.Subspectral Law1161 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1161.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1162.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1162_implies_Equation1161 (Fin n) h

theorem sub_1166_1164 : Law1166.Subspectral Law1164 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1164.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1166.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1166_implies_Equation1164 (Fin n) h

theorem sub_1168_2 : Law1168.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1168.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1168_implies_Equation2 (Fin n) h

theorem sub_1169_2 : Law1169.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1169.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1169_implies_Equation2 (Fin n) h

theorem sub_1170_1168 : Law1170.Subspectral Law1168 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1168.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1170.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1170_implies_Equation1168 (Fin n) h

theorem sub_1176_1172 : Law1176.Subspectral Law1172 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1172.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1176.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1176_implies_Equation1172 (Fin n) h

theorem sub_1179_1170 : Law1179.Subspectral Law1170 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1170.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1179.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1179_implies_Equation1170 (Fin n) h

theorem sub_1182_2 : Law1182.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1182.models_iff (Fin n) M).mp hM
  exact Equation1182_implies_Equation2 (Fin n) h

theorem sub_1193_1185 : Law1193.Subspectral Law1185 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1185.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1193.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1193_implies_Equation1185 (Fin n) h

theorem sub_1196_1195 : Law1196.Subspectral Law1195 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1195.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1196.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1196_implies_Equation1195 (Fin n) h

theorem sub_1198_1147 : Law1198.Subspectral Law1147 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1147.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1198.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1198_implies_Equation1147 (Fin n) h

theorem sub_1201_1149 : Law1201.Subspectral Law1149 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1149.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1201.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1201_implies_Equation1149 (Fin n) h

theorem sub_1206_1205 : Law1206.Subspectral Law1205 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1205.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1206.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1206_implies_Equation1205 (Fin n) h

theorem sub_1211_1209 : Law1211.Subspectral Law1209 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1209.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1211.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1211_implies_Equation1209 (Fin n) h

theorem sub_1216_1215 : Law1216.Subspectral Law1215 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1215.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1216.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1216_implies_Equation1215 (Fin n) h

theorem sub_1222_1145 : Law1222.Subspectral Law1145 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1145.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1222.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1222_implies_Equation1145 (Fin n) h

theorem sub_1277_2 : Law1277.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1277.models_iff (Fin n) M).mp hM
  exact Equation1277_implies_Equation2 (Fin n) h

theorem sub_1279_2328 : Law1279.Subspectral Law2328 := by
  exact (spectrum_eq_of_isDual dual_1279).subset

theorem sub_1282_521 : Law1282.Subspectral Law521 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law521.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1282.models_iff (Fin n) M).mp hM
  exact Equation1282_implies_Equation521 (Fin n) h

theorem sub_1283_2 : Law1283.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1283.models_iff (Fin n) M).mp hM
  exact Equation1283_implies_Equation2 (Fin n) h

theorem sub_1284_1283 : Law1284.Subspectral Law1283 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1283.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1284.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1284_implies_Equation1283 (Fin n) h

theorem sub_1286_2301 : Law1286.Subspectral Law2301 := by
  exact (spectrum_eq_of_isDual dual_1286).subset

theorem sub_1287_468 : Law1287.Subspectral Law468 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law468.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1287.models_iff (Fin n) M).mp hM
  exact Equation1287_implies_Equation468 (Fin n) h

theorem sub_1292_1683 : Law1292.Subspectral Law1683 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1683.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1292.models_iff (Fin n) M).mp hM
  exact Equation1292_implies_Equation1683 (Fin n) h

theorem sub_1294_1287 : Law1294.Subspectral Law1287 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1287.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1294.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1294_implies_Equation1287 (Fin n) h

theorem sub_1296_2901 : Law1296.Subspectral Law2901 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2901.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1296.models_iff (Fin n) M).mp hM
  exact Equation1296_implies_Equation2901 (Fin n) h

theorem sub_1298_1277 : Law1298.Subspectral Law1277 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1277.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1298.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1298_implies_Equation1277 (Fin n) h

theorem sub_1301_2511 : Law1301.Subspectral Law2511 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2511.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1301.models_iff (Fin n) M).mp hM
  exact Equation1301_implies_Equation2511 (Fin n) h

theorem sub_1302_1300 : Law1302.Subspectral Law1300 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1300.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1302.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1302_implies_Equation1300 (Fin n) h

theorem sub_1305_2 : Law1305.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1305.models_iff (Fin n) M).mp hM
  exact Equation1305_implies_Equation2 (Fin n) h

theorem sub_1306_1305 : Law1306.Subspectral Law1305 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1305.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1306.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1306_implies_Equation1305 (Fin n) h

theorem sub_1308_1300 : Law1308.Subspectral Law1300 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1300.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1308.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1308_implies_Equation1300 (Fin n) h

theorem sub_1309_1305 : Law1309.Subspectral Law1305 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1305.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1309.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1309_implies_Equation1305 (Fin n) h

theorem sub_1310_1305 : Law1310.Subspectral Law1305 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1305.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1310.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1310_implies_Equation1305 (Fin n) h

theorem sub_1311_1308 : Law1311.Subspectral Law1308 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1308.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1311.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1311_implies_Equation1308 (Fin n) h

theorem sub_1311_1310 : Law1311.Subspectral Law1310 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1310.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1311.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1311_implies_Equation1310 (Fin n) h

theorem sub_1313_2294 : Law1313.Subspectral Law2294 := by
  exact (spectrum_eq_of_isDual dual_1313).subset

theorem sub_1314_2 : Law1314.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1314.models_iff (Fin n) M).mp hM
  exact Equation1314_implies_Equation2 (Fin n) h

theorem sub_1321_1319 : Law1321.Subspectral Law1319 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1319.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1321.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1321_implies_Equation1319 (Fin n) h

theorem sub_1323_2304 : Law1323.Subspectral Law2304 := by
  exact (spectrum_eq_of_isDual dual_1323).subset

theorem sub_1327_1326 : Law1327.Subspectral Law1326 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1326.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1327.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1327_implies_Equation1326 (Fin n) h

theorem sub_1330_2 : Law1330.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1330.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1330_implies_Equation2 (Fin n) h

theorem sub_1331_1330 : Law1331.Subspectral Law1330 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1330.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1331.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1331_implies_Equation1330 (Fin n) h

theorem sub_1334_2308 : Law1334.Subspectral Law2308 := by
  exact (spectrum_eq_of_isDual dual_1334).subset

theorem sub_1334_2789 : Law1334.Subspectral Law2789 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2789.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1334.models_iff (Fin n) M).mp hM
  exact Equation1334_implies_Equation2789 (Fin n) h

theorem sub_1335_1314 : Law1335.Subspectral Law1314 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1314.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1335.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1335_implies_Equation1314 (Fin n) h

theorem sub_1337_2 : Law1337.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1337.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1337_implies_Equation2 (Fin n) h

theorem sub_1338_2 : Law1338.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1338.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1338_implies_Equation2 (Fin n) h

theorem sub_1339_1337 : Law1339.Subspectral Law1337 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1337.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1339.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1339_implies_Equation1337 (Fin n) h

theorem sub_1341_2 : Law1341.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1341.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1341_implies_Equation2 (Fin n) h

theorem sub_1342_2 : Law1342.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1342.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1342_implies_Equation2 (Fin n) h

theorem sub_1343_1341 : Law1343.Subspectral Law1341 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1341.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1343.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1343_implies_Equation1341 (Fin n) h

theorem sub_1343_1342 : Law1343.Subspectral Law1342 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1342.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1343.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1343_implies_Equation1342 (Fin n) h

theorem sub_1345_2 : Law1345.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1345.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1345_implies_Equation2 (Fin n) h

theorem sub_1346_2 : Law1346.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1346.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1346_implies_Equation2 (Fin n) h

theorem sub_1347_2 : Law1347.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1347.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1347_implies_Equation2 (Fin n) h

theorem sub_1348_1345 : Law1348.Subspectral Law1345 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1345.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1348.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1348_implies_Equation1345 (Fin n) h

theorem sub_1348_1347 : Law1348.Subspectral Law1347 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1347.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1348.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1348_implies_Equation1347 (Fin n) h

theorem sub_1350_3109 : Law1350.Subspectral Law3109 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3109.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1350.models_iff (Fin n) M).mp hM
  exact Equation1350_implies_Equation3109 (Fin n) h

theorem sub_1355_2370 : Law1355.Subspectral Law2370 := by
  exact (spectrum_eq_of_isDual dual_1355).subset

theorem sub_1356_1354 : Law1356.Subspectral Law1354 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1354.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1356.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1356_implies_Equation1354 (Fin n) h

theorem sub_1359_2 : Law1359.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1359.models_iff (Fin n) M).mp hM
  exact Equation1359_implies_Equation2 (Fin n) h

theorem sub_1360_1359 : Law1360.Subspectral Law1359 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1359.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1360.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1360_implies_Equation1359 (Fin n) h

theorem sub_1362_1354 : Law1362.Subspectral Law1354 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1354.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1362.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1362_implies_Equation1354 (Fin n) h

theorem sub_1363_1359 : Law1363.Subspectral Law1359 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1359.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1363.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1363_implies_Equation1359 (Fin n) h

theorem sub_1365_1364 : Law1365.Subspectral Law1364 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1364.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1365.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1365_implies_Equation1364 (Fin n) h

theorem sub_1367_678 : Law1367.Subspectral Law678 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law678.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1367.models_iff (Fin n) M).mp hM
  exact Equation1367_implies_Equation678 (Fin n) h

theorem sub_1368_1587 : Law1368.Subspectral Law1587 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1587.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1368.models_iff (Fin n) M).mp hM
  exact Equation1368_implies_Equation1587 (Fin n) h

theorem sub_1372_2 : Law1372.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1372.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1372_implies_Equation2 (Fin n) h

theorem sub_1373_1371 : Law1373.Subspectral Law1371 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1371.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1373.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1373_implies_Equation1371 (Fin n) h

theorem sub_1375_2 : Law1375.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1375.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1375_implies_Equation2 (Fin n) h

theorem sub_1376_2 : Law1376.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1376.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1376_implies_Equation2 (Fin n) h

theorem sub_1377_1375 : Law1377.Subspectral Law1375 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1375.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1377.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1377_implies_Equation1375 (Fin n) h

theorem sub_1377_1376 : Law1377.Subspectral Law1376 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1376.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1377.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1377_implies_Equation1376 (Fin n) h

theorem sub_1379_2 : Law1379.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1379.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1379_implies_Equation2 (Fin n) h

theorem sub_1380_2 : Law1380.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1380.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1380_implies_Equation2 (Fin n) h

theorem sub_1381_2 : Law1381.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1381.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1381_implies_Equation2 (Fin n) h

theorem sub_1382_1379 : Law1382.Subspectral Law1379 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1379.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1382.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1382_implies_Equation1379 (Fin n) h

theorem sub_1382_1381 : Law1382.Subspectral Law1381 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1381.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1382.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1382_implies_Equation1381 (Fin n) h

theorem sub_1384_2319 : Law1384.Subspectral Law2319 := by
  exact (spectrum_eq_of_isDual dual_1384).subset

theorem sub_1384_2755 : Law1384.Subspectral Law2755 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2755.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1384.models_iff (Fin n) M).mp hM
  exact Equation1384_implies_Equation2755 (Fin n) h

theorem sub_1385_2 : Law1385.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1385.models_iff (Fin n) M).mp hM
  exact Equation1385_implies_Equation2 (Fin n) h

theorem sub_1390_2 : Law1390.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1390.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1390_implies_Equation2 (Fin n) h

theorem sub_1392_2 : Law1392.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1392.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1392_implies_Equation2 (Fin n) h

theorem sub_1393_2 : Law1393.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1393.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1393_implies_Equation2 (Fin n) h

theorem sub_1394_1392 : Law1394.Subspectral Law1392 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1392.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1394.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1394_implies_Equation1392 (Fin n) h

theorem sub_1394_1393 : Law1394.Subspectral Law1393 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1393.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1394.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1394_implies_Equation1393 (Fin n) h

theorem sub_1396_2 : Law1396.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1396.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1396_implies_Equation2 (Fin n) h

theorem sub_1397_2 : Law1397.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1397.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1397_implies_Equation2 (Fin n) h

theorem sub_1398_2 : Law1398.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1398.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1398_implies_Equation2 (Fin n) h

theorem sub_1399_1390 : Law1399.Subspectral Law1390 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1390.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1399.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1399_implies_Equation1390 (Fin n) h

theorem sub_1399_1398 : Law1399.Subspectral Law1398 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1398.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1399.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1399_implies_Equation1398 (Fin n) h

theorem sub_1403_1367 : Law1403.Subspectral Law1367 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1367.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1403.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1403_implies_Equation1367 (Fin n) h

theorem sub_1404_1352 : Law1404.Subspectral Law1352 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1352.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1404.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1404_implies_Equation1352 (Fin n) h

theorem sub_1406_2 : Law1406.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1406.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1406_implies_Equation2 (Fin n) h

theorem sub_1407_2 : Law1407.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1407.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1407_implies_Equation2 (Fin n) h

theorem sub_1408_2 : Law1408.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1408.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1408_implies_Equation2 (Fin n) h

theorem sub_1409_1406 : Law1409.Subspectral Law1406 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1406.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1409.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1409_implies_Equation1406 (Fin n) h

theorem sub_1411_2 : Law1411.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1411.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1411_implies_Equation2 (Fin n) h

theorem sub_1412_2 : Law1412.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1412.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1412_implies_Equation2 (Fin n) h

theorem sub_1413_2 : Law1413.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1413.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1413_implies_Equation2 (Fin n) h

theorem sub_1414_1411 : Law1414.Subspectral Law1411 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1411.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1414.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1414_implies_Equation1411 (Fin n) h

theorem sub_1414_1412 : Law1414.Subspectral Law1412 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1412.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1414.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1414_implies_Equation1412 (Fin n) h

theorem sub_1416_2 : Law1416.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1416.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1416_implies_Equation2 (Fin n) h

theorem sub_1417_2 : Law1417.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1417.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1417_implies_Equation2 (Fin n) h

theorem sub_1418_2 : Law1418.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1418.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1418_implies_Equation2 (Fin n) h

theorem sub_1419_1416 : Law1419.Subspectral Law1416 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1416.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1419.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1419_implies_Equation1416 (Fin n) h

theorem sub_1419_1418 : Law1419.Subspectral Law1418 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1418.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1419.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1419_implies_Equation1418 (Fin n) h

theorem sub_1421_2 : Law1421.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1421.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1421_implies_Equation2 (Fin n) h

theorem sub_1422_2 : Law1422.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1422.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1422_implies_Equation2 (Fin n) h

theorem sub_1423_2 : Law1423.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1423.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1423_implies_Equation2 (Fin n) h

theorem sub_1424_2 : Law1424.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1424.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1424_implies_Equation2 (Fin n) h

theorem sub_1425_1421 : Law1425.Subspectral Law1421 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1421.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1425.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1425_implies_Equation1421 (Fin n) h

theorem sub_1425_1424 : Law1425.Subspectral Law1424 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1424.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1425.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1425_implies_Equation1424 (Fin n) h

theorem sub_1480_2089 : Law1480.Subspectral Law2089 := by
  exact (spectrum_eq_of_isDual dual_1480).subset

theorem sub_1483_2163 : Law1483.Subspectral Law2163 := by
  exact (spectrum_eq_of_isDual dual_1483).subset

theorem sub_1485_2162 : Law1485.Subspectral Law2162 := by
  exact (spectrum_eq_of_isDual dual_1485).subset

theorem sub_1486_2126 : Law1486.Subspectral Law2126 := by
  exact (spectrum_eq_of_isDual dual_1486).subset

theorem sub_1489_2098 : Law1489.Subspectral Law2098 := by
  exact (spectrum_eq_of_isDual dual_1489).subset

theorem sub_1490_874 : Law1490.Subspectral Law874 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law874.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1490.models_iff (Fin n) M).mp hM
  exact Equation1490_implies_Equation874 (Fin n) h

theorem sub_1495_2 : Law1495.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1495.models_iff (Fin n) M).mp hM
  exact Equation1495_implies_Equation2 (Fin n) h

theorem sub_1496_481 : Law1496.Subspectral Law481 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law481.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1496.models_iff (Fin n) M).mp hM
  exact Equation1496_implies_Equation481 (Fin n) h

theorem sub_1496_2146 : Law1496.Subspectral Law2146 := by
  exact (spectrum_eq_of_isDual dual_1496).subset

theorem sub_1497_1495 : Law1497.Subspectral Law1495 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1495.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1497.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1497_implies_Equation1495 (Fin n) h

theorem sub_1500_498 : Law1500.Subspectral Law498 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law498.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1500.models_iff (Fin n) M).mp hM
  exact Equation1500_implies_Equation498 (Fin n) h

theorem sub_1503_2 : Law1503.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1503.models_iff (Fin n) M).mp hM
  exact Equation1503_implies_Equation2 (Fin n) h

theorem sub_1505_1503 : Law1505.Subspectral Law1503 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1503.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1505.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1505_implies_Equation1503 (Fin n) h

theorem sub_1509_1508 : Law1509.Subspectral Law1508 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1508.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1509.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1509_implies_Equation1508 (Fin n) h

theorem sub_1511_1499 : Law1511.Subspectral Law1499 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1499.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1511.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1511_implies_Equation1499 (Fin n) h

theorem sub_1512_1500 : Law1512.Subspectral Law1500 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1500.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1512.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1512_implies_Equation1500 (Fin n) h

theorem sub_1513_1508 : Law1513.Subspectral Law1508 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1508.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1513.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1513_implies_Equation1508 (Fin n) h

theorem sub_1516_2091 : Law1516.Subspectral Law2091 := by
  exact (spectrum_eq_of_isDual dual_1516).subset

theorem sub_1520_2 : Law1520.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1520.models_iff (Fin n) M).mp hM
  exact Equation1520_implies_Equation2 (Fin n) h

theorem sub_1522_2920 : Law1522.Subspectral Law2920 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2920.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1522.models_iff (Fin n) M).mp hM
  exact Equation1522_implies_Equation2920 (Fin n) h

theorem sub_1526_2101 : Law1526.Subspectral Law2101 := by
  exact (spectrum_eq_of_isDual dual_1526).subset

theorem sub_1527_2 : Law1527.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1527.models_iff (Fin n) M).mp hM
  exact Equation1527_implies_Equation2 (Fin n) h

theorem sub_1529_150 : Law1529.Subspectral Law150 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law150.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1529.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1529_implies_Equation150 (Fin n) h

theorem sub_1530_2 : Law1530.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1530.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1530_implies_Equation2 (Fin n) h

theorem sub_1532_2 : Law1532.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1532.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1532_implies_Equation2 (Fin n) h

theorem sub_1533_2 : Law1533.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1533.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1533_implies_Equation2 (Fin n) h

theorem sub_1534_1527 : Law1534.Subspectral Law1527 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1527.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1534.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1534_implies_Equation1527 (Fin n) h

theorem sub_1537_695 : Law1537.Subspectral Law695 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law695.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1537.models_iff (Fin n) M).mp hM
  exact Equation1537_implies_Equation695 (Fin n) h

theorem sub_1538_1536 : Law1538.Subspectral Law1536 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1536.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1538.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1538_implies_Equation1536 (Fin n) h

theorem sub_1540_2 : Law1540.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1540.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1540_implies_Equation2 (Fin n) h

theorem sub_1541_2 : Law1541.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1541.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1541_implies_Equation2 (Fin n) h

theorem sub_1542_1540 : Law1542.Subspectral Law1540 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1540.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1542.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1542_implies_Equation1540 (Fin n) h

theorem sub_1544_2 : Law1544.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1544.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1544_implies_Equation2 (Fin n) h

theorem sub_1545_2 : Law1545.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1545.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1545_implies_Equation2 (Fin n) h

theorem sub_1546_1545 : Law1546.Subspectral Law1545 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1545.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1546.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1546_implies_Equation1545 (Fin n) h

theorem sub_1551_1524 : Law1551.Subspectral Law1524 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1524.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1551.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1551_implies_Equation1524 (Fin n) h

theorem sub_1555_1517 : Law1555.Subspectral Law1517 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1517.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1555.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1555_implies_Equation1517 (Fin n) h

theorem sub_1555_1553 : Law1555.Subspectral Law1553 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1553.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1555.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1555_implies_Equation1553 (Fin n) h

theorem sub_1559_1557 : Law1559.Subspectral Law1557 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1557.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1559.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1559_implies_Equation1557 (Fin n) h

theorem sub_1562_2 : Law1562.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1562.models_iff (Fin n) M).mp hM
  exact Equation1562_implies_Equation2 (Fin n) h

theorem sub_1563_1562 : Law1563.Subspectral Law1562 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1562.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1563.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1563_implies_Equation1562 (Fin n) h

theorem sub_1566_1554 : Law1566.Subspectral Law1554 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1554.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1566.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1566_implies_Equation1554 (Fin n) h

theorem sub_1567_1562 : Law1567.Subspectral Law1562 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1562.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1567.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1567_implies_Equation1562 (Fin n) h

theorem sub_1568_1559 : Law1568.Subspectral Law1559 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1559.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1568.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1568_implies_Equation1559 (Fin n) h

theorem sub_1568_1567 : Law1568.Subspectral Law1567 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1567.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1568.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1568_implies_Equation1567 (Fin n) h

theorem sub_1571_1334 : Law1571.Subspectral Law1334 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1334.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1571.models_iff (Fin n) M).mp hM
  exact Equation1571_implies_Equation1334 (Fin n) h

theorem sub_1571_2113 : Law1571.Subspectral Law2113 := by
  exact (spectrum_eq_of_isDual dual_1571).subset

theorem sub_1578_1576 : Law1578.Subspectral Law1576 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1576.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1578.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1578_implies_Equation1576 (Fin n) h

theorem sub_1583_1582 : Law1583.Subspectral Law1582 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1582.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1583.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1583_implies_Equation1582 (Fin n) h

theorem sub_1585_1497 : Law1585.Subspectral Law1497 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1497.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1585.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1585_implies_Equation1497 (Fin n) h

theorem sub_1585_1572 : Law1585.Subspectral Law1572 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1572.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1585.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1585_implies_Equation1572 (Fin n) h

theorem sub_1587_2116 : Law1587.Subspectral Law2116 := by
  exact (spectrum_eq_of_isDual dual_1587).subset

theorem sub_1587_2805 : Law1587.Subspectral Law2805 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2805.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1587.models_iff (Fin n) M).mp hM
  exact Equation1587_implies_Equation2805 (Fin n) h

theorem sub_1588_2 : Law1588.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1588.models_iff (Fin n) M).mp hM
  exact Equation1588_implies_Equation2 (Fin n) h

theorem sub_1595_1593 : Law1595.Subspectral Law1593 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1593.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1595.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1595_implies_Equation1593 (Fin n) h

theorem sub_1596_1529 : Law1596.Subspectral Law1529 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1529.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1596.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1596_implies_Equation1529 (Fin n) h

theorem sub_1602_1589 : Law1602.Subspectral Law1589 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1589.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1602.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1602_implies_Equation1589 (Fin n) h

theorem sub_1604_1553 : Law1604.Subspectral Law1553 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1553.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1604.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1604_implies_Equation1553 (Fin n) h

theorem sub_1606_1570 : Law1606.Subspectral Law1570 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1570.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1606.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1606_implies_Equation1570 (Fin n) h

theorem sub_1606_1935 : Law1606.Subspectral Law1935 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1935.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1606.models_iff (Fin n) M).mp hM
  exact Equation1606_implies_Equation1935 (Fin n) h

theorem sub_1610_1609 : Law1610.Subspectral Law1609 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1609.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1610.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1610_implies_Equation1609 (Fin n) h

theorem sub_1612_1505 : Law1612.Subspectral Law1505 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1505.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1612.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1612_implies_Equation1505 (Fin n) h

theorem sub_1614_1612 : Law1614.Subspectral Law1612 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1612.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1614.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1614_implies_Equation1612 (Fin n) h

theorem sub_1617_1615 : Law1617.Subspectral Law1615 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1615.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1617.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1617_implies_Equation1615 (Fin n) h

theorem sub_1622_1509 : Law1622.Subspectral Law1509 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1509.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1622.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1622_implies_Equation1509 (Fin n) h

theorem sub_1624_1604 : Law1624.Subspectral Law1604 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1604.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1624.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1624_implies_Equation1604 (Fin n) h

theorem sub_1627_1513 : Law1627.Subspectral Law1513 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1513.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1627.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1627_implies_Equation1513 (Fin n) h

theorem sub_1628_1585 : Law1628.Subspectral Law1585 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1585.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1628.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1628_implies_Equation1585 (Fin n) h

theorem sub_1628_1607 : Law1628.Subspectral Law1607 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1607.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1628.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1628_implies_Equation1607 (Fin n) h

theorem sub_1685_1922 : Law1685.Subspectral Law1922 := by
  exact (spectrum_eq_of_isDual dual_1685).subset

theorem sub_1688_2806 : Law1688.Subspectral Law2806 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2806.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1688.models_iff (Fin n) M).mp hM
  exact Equation1688_implies_Equation2806 (Fin n) h

theorem sub_1689_2 : Law1689.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1689.models_iff (Fin n) M).mp hM
  exact Subgraph.Equation1689_implies_Equation2 (Fin n) h

theorem sub_1692_1895 : Law1692.Subspectral Law1895 := by
  exact (spectrum_eq_of_isDual dual_1692).subset

theorem sub_1698_555 : Law1698.Subspectral Law555 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law555.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1698.models_iff (Fin n) M).mp hM
  exact Equation1698_implies_Equation555 (Fin n) h

theorem sub_1700_1696 : Law1700.Subspectral Law1696 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1696.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1700.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1700_implies_Equation1696 (Fin n) h

theorem sub_1702_747 : Law1702.Subspectral Law747 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law747.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1702.models_iff (Fin n) M).mp hM
  exact Equation1702_implies_Equation747 (Fin n) h

theorem sub_1703_794 : Law1703.Subspectral Law794 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law794.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1703.models_iff (Fin n) M).mp hM
  exact Equation1703_implies_Equation794 (Fin n) h

theorem sub_1706_890 : Law1706.Subspectral Law890 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law890.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1706.models_iff (Fin n) M).mp hM
  exact Equation1706_implies_Equation890 (Fin n) h

theorem sub_1710_695 : Law1710.Subspectral Law695 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law695.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1710.models_iff (Fin n) M).mp hM
  exact Equation1710_implies_Equation695 (Fin n) h

theorem sub_1711_2 : Law1711.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1711.models_iff (Fin n) M).mp hM
  exact Equation1711_implies_Equation2 (Fin n) h

theorem sub_1712_1711 : Law1712.Subspectral Law1711 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1711.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1712.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1712_implies_Equation1711 (Fin n) h

theorem sub_1714_2906 : Law1714.Subspectral Law2906 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2906.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1714.models_iff (Fin n) M).mp hM
  exact Equation1714_implies_Equation2906 (Fin n) h

theorem sub_1715_1711 : Law1715.Subspectral Law1711 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1711.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1715.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1715_implies_Equation1711 (Fin n) h

theorem sub_1719_1888 : Law1719.Subspectral Law1888 := by
  exact (spectrum_eq_of_isDual dual_1719).subset

theorem sub_1720_2 : Law1720.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1720.models_iff (Fin n) M).mp hM
  exact Equation1720_implies_Equation2 (Fin n) h

theorem sub_1725_2 : Law1725.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1725.models_iff (Fin n) M).mp hM
  exact Equation1725_implies_Equation2 (Fin n) h

theorem sub_1727_1720 : Law1727.Subspectral Law1720 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1720.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1727.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1727_implies_Equation1720 (Fin n) h

theorem sub_1732_2 : Law1732.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1732.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1732_implies_Equation2 (Fin n) h

theorem sub_1733_2 : Law1733.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1733.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1733_implies_Equation2 (Fin n) h

theorem sub_1735_1732 : Law1735.Subspectral Law1732 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1732.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1735.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1735_implies_Equation1732 (Fin n) h

theorem sub_1736_2 : Law1736.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1736.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1736_implies_Equation2 (Fin n) h

theorem sub_1737_1730 : Law1737.Subspectral Law1730 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1730.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1737.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1737_implies_Equation1730 (Fin n) h

theorem sub_1744_2 : Law1744.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1744.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1744_implies_Equation2 (Fin n) h

theorem sub_1745_1744 : Law1745.Subspectral Law1744 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1744.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1745.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1745_implies_Equation1744 (Fin n) h

theorem sub_1747_1745 : Law1747.Subspectral Law1745 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1745.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1747.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1747_implies_Equation1745 (Fin n) h

theorem sub_1748_2 : Law1748.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1748.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1748_implies_Equation2 (Fin n) h

theorem sub_1749_1748 : Law1749.Subspectral Law1748 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1748.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1749.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1749_implies_Equation1748 (Fin n) h

theorem sub_1751_1739 : Law1751.Subspectral Law1739 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1739.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1751.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1751_implies_Equation1739 (Fin n) h

theorem sub_1752_2 : Law1752.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1752.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1752_implies_Equation2 (Fin n) h

theorem sub_1753_2 : Law1753.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1753.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1753_implies_Equation2 (Fin n) h

theorem sub_1754_1752 : Law1754.Subspectral Law1752 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1752.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1754.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1754_implies_Equation1752 (Fin n) h

theorem sub_1754_1753 : Law1754.Subspectral Law1753 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1753.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1754.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1754_implies_Equation1753 (Fin n) h

theorem sub_1756_2 : Law1756.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1756.models_iff (Fin n) M).mp hM
  exact Equation1756_implies_Equation2 (Fin n) h

theorem sub_1757_2 : Law1757.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1757.models_iff (Fin n) M).mp hM
  exact Equation1757_implies_Equation2 (Fin n) h

theorem sub_1764_1967 : Law1764.Subspectral Law1967 := by
  exact (spectrum_eq_of_isDual dual_1764).subset

theorem sub_1764_3185 : Law1764.Subspectral Law3185 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3185.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1764.models_iff (Fin n) M).mp hM
  exact Equation1764_implies_Equation3185 (Fin n) h

theorem sub_1768_1756 : Law1768.Subspectral Law1756 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1756.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1768.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1768_implies_Equation1756 (Fin n) h

theorem sub_1769_1757 : Law1769.Subspectral Law1757 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1757.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1769.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1769_implies_Equation1757 (Fin n) h

theorem sub_1770_1689 : Law1770.Subspectral Law1689 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1689.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1770.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1770_implies_Equation1689 (Fin n) h

theorem sub_1771_1690 : Law1771.Subspectral Law1690 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1690.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1771.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1771_implies_Equation1690 (Fin n) h

theorem sub_1773_2 : Law1773.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1773.models_iff (Fin n) M).mp hM
  exact Equation1773_implies_Equation2 (Fin n) h

theorem sub_1775_1693 : Law1775.Subspectral Law1693 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1693.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1775.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1775_implies_Equation1693 (Fin n) h

theorem sub_1778_2 : Law1778.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1778.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1778_implies_Equation2 (Fin n) h

theorem sub_1781_1779 : Law1781.Subspectral Law1779 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1779.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1781.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1781_implies_Equation1779 (Fin n) h

theorem sub_1783_1693 : Law1783.Subspectral Law1693 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1693.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1783.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1783_implies_Equation1693 (Fin n) h

theorem sub_1785_1773 : Law1785.Subspectral Law1773 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1773.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1785.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1785_implies_Equation1773 (Fin n) h

theorem sub_1786_1782 : Law1786.Subspectral Law1782 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1782.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1786.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1786_implies_Equation1782 (Fin n) h

theorem sub_1787_1782 : Law1787.Subspectral Law1782 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1782.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1787.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1787_implies_Equation1782 (Fin n) h

theorem sub_1788_1775 : Law1788.Subspectral Law1775 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1775.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1788.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1788_implies_Equation1775 (Fin n) h

theorem sub_1790_1913 : Law1790.Subspectral Law1913 := by
  exact (spectrum_eq_of_isDual dual_1790).subset

theorem sub_1791_1588 : Law1791.Subspectral Law1588 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1588.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1791.models_iff (Fin n) M).mp hM
  exact Equation1791_implies_Equation1588 (Fin n) h

theorem sub_1794_1788 : Law1794.Subspectral Law1788 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1788.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1794.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1794_implies_Equation1788 (Fin n) h

theorem sub_1796_1795 : Law1796.Subspectral Law1795 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1795.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1796.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1796_implies_Equation1795 (Fin n) h

theorem sub_1800_1799 : Law1800.Subspectral Law1799 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1799.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1800.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1800_implies_Equation1799 (Fin n) h

theorem sub_1802_1800 : Law1802.Subspectral Law1800 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1800.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1802.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1802_implies_Equation1800 (Fin n) h

theorem sub_1805_1792 : Law1805.Subspectral Law1792 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1792.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1805.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1805_implies_Equation1792 (Fin n) h

theorem sub_1807_1756 : Law1807.Subspectral Law1756 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1756.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1807.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1807_implies_Equation1756 (Fin n) h

theorem sub_1808_1757 : Law1808.Subspectral Law1757 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1757.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1808.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1808_implies_Equation1757 (Fin n) h

theorem sub_1809_1773 : Law1809.Subspectral Law1773 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1773.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1809.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1809_implies_Equation1773 (Fin n) h

theorem sub_1812_1760 : Law1812.Subspectral Law1760 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1760.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1812.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1812_implies_Equation1760 (Fin n) h

theorem sub_1815_1813 : Law1815.Subspectral Law1813 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1813.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1815.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1815_implies_Equation1813 (Fin n) h

theorem sub_1817_1815 : Law1817.Subspectral Law1815 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1815.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1817.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1817_implies_Equation1815 (Fin n) h

theorem sub_1819_1818 : Law1819.Subspectral Law1818 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1818.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1819.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1819_implies_Equation1818 (Fin n) h

theorem sub_1820_1704 : Law1820.Subspectral Law1704 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1704.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1820.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1820_implies_Equation1704 (Fin n) h

theorem sub_1822_1820 : Law1822.Subspectral Law1820 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1820.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1822.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1822_implies_Equation1820 (Fin n) h

theorem sub_1823_1757 : Law1823.Subspectral Law1757 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1757.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1823.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1823_implies_Equation1757 (Fin n) h

theorem sub_1825_1712 : Law1825.Subspectral Law1712 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1712.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1825.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1825_implies_Equation1712 (Fin n) h

theorem sub_1825_1823 : Law1825.Subspectral Law1823 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1823.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1825.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1825_implies_Equation1823 (Fin n) h

theorem sub_1827_1825 : Law1827.Subspectral Law1825 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1825.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1827.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1827_implies_Equation1825 (Fin n) h

theorem sub_1886_2108 : Law1886.Subspectral Law2108 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2108.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1886.models_iff (Fin n) M).mp hM
  exact Equation1886_implies_Equation2108 (Fin n) h

theorem sub_1888_1719 : Law1888.Subspectral Law1719 := by
  exact (spectrum_eq_of_isDual dual_1888).subset

theorem sub_1893_1891 : Law1893.Subspectral Law1891 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1891.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1893.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1893_implies_Equation1891 (Fin n) h

theorem sub_1893_1892 : Law1893.Subspectral Law1892 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1892.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1893.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1893_implies_Equation1892 (Fin n) h

theorem sub_1895_1692 : Law1895.Subspectral Law1692 := by
  exact (spectrum_eq_of_isDual dual_1895).subset

theorem sub_1899_1889 : Law1899.Subspectral Law1889 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1889.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1899.models_iff (Fin n) M).mp hM
  exact Equation1899_implies_Equation1889 (Fin n) h

theorem sub_1905_471 : Law1905.Subspectral Law471 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law471.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1905.models_iff (Fin n) M).mp hM
  exact Equation1905_implies_Equation471 (Fin n) h

theorem sub_1906_2 : Law1906.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1906.models_iff (Fin n) M).mp hM
  exact Equation1906_implies_Equation2 (Fin n) h

theorem sub_1907_1906 : Law1907.Subspectral Law1906 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1906.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1907.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1907_implies_Equation1906 (Fin n) h

theorem sub_1909_2 : Law1909.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1909.models_iff (Fin n) M).mp hM
  exact Equation1909_implies_Equation2 (Fin n) h

theorem sub_1911_1909 : Law1911.Subspectral Law1909 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1909.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1911.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1911_implies_Equation1909 (Fin n) h

theorem sub_1913_1790 : Law1913.Subspectral Law1790 := by
  exact (spectrum_eq_of_isDual dual_1913).subset

theorem sub_1913_2776 : Law1913.Subspectral Law2776 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2776.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1913.models_iff (Fin n) M).mp hM
  exact Equation1913_implies_Equation2776 (Fin n) h

theorem sub_1914_2 : Law1914.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1914.models_iff (Fin n) M).mp hM
  exact Equation1914_implies_Equation2 (Fin n) h

theorem sub_1915_1914 : Law1915.Subspectral Law1914 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1914.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1915.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1915_implies_Equation1914 (Fin n) h

theorem sub_1917_1909 : Law1917.Subspectral Law1909 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1909.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1917.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1917_implies_Equation1909 (Fin n) h

theorem sub_1919_1914 : Law1919.Subspectral Law1914 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1914.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1919.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1919_implies_Equation1914 (Fin n) h

theorem sub_1920_1911 : Law1920.Subspectral Law1911 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1911.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1920.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1920_implies_Equation1911 (Fin n) h

theorem sub_1920_1918 : Law1920.Subspectral Law1918 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1918.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1920.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1920_implies_Equation1918 (Fin n) h

theorem sub_1922_1685 : Law1922.Subspectral Law1685 := by
  exact (spectrum_eq_of_isDual dual_1922).subset

theorem sub_1926_173 : Law1926.Subspectral Law173 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law173.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1926.models_iff (Fin n) M).mp hM
  exact Equation1926_implies_Equation173 (Fin n) h

theorem sub_1928_3009 : Law1928.Subspectral Law3009 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3009.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1928.models_iff (Fin n) M).mp hM
  exact Equation1928_implies_Equation3009 (Fin n) h

theorem sub_1936_2 : Law1936.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1936.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1936_implies_Equation2 (Fin n) h

theorem sub_1938_2 : Law1938.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1938.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1938_implies_Equation2 (Fin n) h

theorem sub_1940_1936 : Law1940.Subspectral Law1936 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1936.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1940.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1940_implies_Equation1936 (Fin n) h

theorem sub_1940_1939 : Law1940.Subspectral Law1939 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1939.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1940.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1940_implies_Equation1939 (Fin n) h

theorem sub_1944_1933 : Law1944.Subspectral Law1933 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1933.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1944.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1944_implies_Equation1933 (Fin n) h

theorem sub_1946_2 : Law1946.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1946.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1946_implies_Equation2 (Fin n) h

theorem sub_1947_2 : Law1947.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1947.models_iff (Fin n) M).mp hM
  exact Singleton.Equation1947_implies_Equation2 (Fin n) h

theorem sub_1948_1946 : Law1948.Subspectral Law1946 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1946.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1948.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1948_implies_Equation1946 (Fin n) h

theorem sub_1950_195 : Law1950.Subspectral Law195 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law195.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1950.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1950_implies_Equation195 (Fin n) h

theorem sub_1952_1951 : Law1952.Subspectral Law1951 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1951.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1952.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1952_implies_Equation1951 (Fin n) h

theorem sub_1957_1956 : Law1957.Subspectral Law1956 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1956.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1957.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1957_implies_Equation1956 (Fin n) h

theorem sub_1960_2 : Law1960.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1960.models_iff (Fin n) M).mp hM
  exact Equation1960_implies_Equation2 (Fin n) h

theorem sub_1961_1960 : Law1961.Subspectral Law1960 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1960.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1961.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1961_implies_Equation1960 (Fin n) h

theorem sub_1965_1963 : Law1965.Subspectral Law1963 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1963.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1965.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1965_implies_Equation1963 (Fin n) h

theorem sub_1967_1764 : Law1967.Subspectral Law1764 := by
  exact (spectrum_eq_of_isDual dual_1967).subset

theorem sub_1967_2586 : Law1967.Subspectral Law2586 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2586.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1967.models_iff (Fin n) M).mp hM
  exact Equation1967_implies_Equation2586 (Fin n) h

theorem sub_1968_2 : Law1968.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1968.models_iff (Fin n) M).mp hM
  exact Equation1968_implies_Equation2 (Fin n) h

theorem sub_1969_1968 : Law1969.Subspectral Law1968 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1968.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1969.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1969_implies_Equation1968 (Fin n) h

theorem sub_1972_1960 : Law1972.Subspectral Law1960 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1960.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1972.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1972_implies_Equation1960 (Fin n) h

theorem sub_1974_1965 : Law1974.Subspectral Law1965 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1965.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1974.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1974_implies_Equation1965 (Fin n) h

theorem sub_1981_1980 : Law1981.Subspectral Law1980 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1980.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1981.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1981_implies_Equation1980 (Fin n) h

theorem sub_1982_1981 : Law1982.Subspectral Law1981 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1981.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1982.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1982_implies_Equation1981 (Fin n) h

theorem sub_1989_1988 : Law1989.Subspectral Law1988 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1988.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1989.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation1989_implies_Equation1988 (Fin n) h

theorem sub_1991_1990 : Law1991.Subspectral Law1990 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1990.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1991.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation1991_implies_Equation1990 (Fin n) h

theorem sub_1993_1710 : Law1993.Subspectral Law1710 := by
  exact (spectrum_eq_of_isDual dual_1993).subset

theorem sub_1994_2922 : Law1994.Subspectral Law2922 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2922.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law1994.models_iff (Fin n) M).mp hM
  exact Equation1994_implies_Equation2922 (Fin n) h

theorem sub_2001_200 : Law2001.Subspectral Law200 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law200.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2001.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2001_implies_Equation200 (Fin n) h

theorem sub_2003_2002 : Law2003.Subspectral Law2002 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2002.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2003.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2003_implies_Equation2002 (Fin n) h

theorem sub_2006_1998 : Law2006.Subspectral Law1998 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1998.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2006.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2006_implies_Equation1998 (Fin n) h

theorem sub_2010_1942 : Law2010.Subspectral Law1942 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1942.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2010.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2010_implies_Equation1942 (Fin n) h

theorem sub_2011_1994 : Law2011.Subspectral Law1994 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1994.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2011.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2011_implies_Equation1994 (Fin n) h

theorem sub_2013_1907 : Law2013.Subspectral Law1907 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1907.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2013.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2013_implies_Equation1907 (Fin n) h

theorem sub_2013_1961 : Law2013.Subspectral Law1961 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1961.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2013.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2013_implies_Equation1961 (Fin n) h

theorem sub_2016_1998 : Law2016.Subspectral Law1998 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1998.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2016.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2016_implies_Equation1998 (Fin n) h

theorem sub_2017_1998 : Law2017.Subspectral Law1998 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1998.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2017.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2017_implies_Equation1998 (Fin n) h

theorem sub_2018_2015 : Law2018.Subspectral Law2015 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2015.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2018.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2018_implies_Equation2015 (Fin n) h

theorem sub_2028_2027 : Law2028.Subspectral Law2027 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2027.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2028.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2028_implies_Equation2027 (Fin n) h

theorem sub_2034_1957 : Law2034.Subspectral Law1957 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1957.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2034.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2034_implies_Equation1957 (Fin n) h

theorem sub_2034_2033 : Law2034.Subspectral Law2033 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2033.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2034.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2034_implies_Equation2033 (Fin n) h

theorem sub_2089_1480 : Law2089.Subspectral Law1480 := by
  exact (spectrum_eq_of_isDual dual_2089).subset

theorem sub_2091_1516 : Law2091.Subspectral Law1516 := by
  exact (spectrum_eq_of_isDual dual_2091).subset

theorem sub_2092_3141 : Law2092.Subspectral Law3141 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3141.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2092.models_iff (Fin n) M).mp hM
  exact Equation2092_implies_Equation3141 (Fin n) h

theorem sub_2094_2 : Law2094.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2094.models_iff (Fin n) M).mp hM
  exact Equation2094_implies_Equation2 (Fin n) h

theorem sub_2095_2 : Law2095.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2095.models_iff (Fin n) M).mp hM
  exact Equation2095_implies_Equation2 (Fin n) h

theorem sub_2098_1489 : Law2098.Subspectral Law1489 := by
  exact (spectrum_eq_of_isDual dual_2098).subset

theorem sub_2101_1526 : Law2101.Subspectral Law1526 := by
  exact (spectrum_eq_of_isDual dual_2101).subset

theorem sub_2104_2 : Law2104.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2104.models_iff (Fin n) M).mp hM
  exact Equation2104_implies_Equation2 (Fin n) h

theorem sub_2105_1537 : Law2105.Subspectral Law1537 := by
  exact (spectrum_eq_of_isDual dual_2105).subset

theorem sub_2105_2755 : Law2105.Subspectral Law2755 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2755.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2105.models_iff (Fin n) M).mp hM
  exact Equation2105_implies_Equation2755 (Fin n) h

theorem sub_2108_2911 : Law2108.Subspectral Law2911 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2911.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2108.models_iff (Fin n) M).mp hM
  exact Equation2108_implies_Equation2911 (Fin n) h

theorem sub_2109_2717 : Law2109.Subspectral Law2717 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2717.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2109.models_iff (Fin n) M).mp hM
  exact Equation2109_implies_Equation2717 (Fin n) h

theorem sub_2110_2108 : Law2110.Subspectral Law2108 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2108.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2110.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2110_implies_Equation2108 (Fin n) h

theorem sub_2112_995 : Law2112.Subspectral Law995 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law995.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2112.models_iff (Fin n) M).mp hM
  exact Equation2112_implies_Equation995 (Fin n) h

theorem sub_2113_1334 : Law2113.Subspectral Law1334 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1334.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2113.models_iff (Fin n) M).mp hM
  exact Equation2113_implies_Equation1334 (Fin n) h

theorem sub_2114_2092 : Law2114.Subspectral Law2092 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2092.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2114.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2114_implies_Equation2092 (Fin n) h

theorem sub_2114_2112 : Law2114.Subspectral Law2112 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2112.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2114.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2114_implies_Equation2112 (Fin n) h

theorem sub_2118_2117 : Law2118.Subspectral Law2117 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2117.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2118.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2118_implies_Equation2117 (Fin n) h

theorem sub_2121_2117 : Law2121.Subspectral Law2117 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2117.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2121.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2121_implies_Equation2117 (Fin n) h

theorem sub_2123_2096 : Law2123.Subspectral Law2096 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2096.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2123.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2123_implies_Equation2096 (Fin n) h

theorem sub_2123_2106 : Law2123.Subspectral Law2106 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2106.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2123.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2123_implies_Equation2106 (Fin n) h

theorem sub_2126_1486 : Law2126.Subspectral Law1486 := by
  exact (spectrum_eq_of_isDual dual_2126).subset

theorem sub_2131_2 : Law2131.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2131.models_iff (Fin n) M).mp hM
  exact Equation2131_implies_Equation2 (Fin n) h

theorem sub_2133_2131 : Law2133.Subspectral Law2131 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2131.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2133.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2133_implies_Equation2131 (Fin n) h

theorem sub_2136_2 : Law2136.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2136.models_iff (Fin n) M).mp hM
  exact Equation2136_implies_Equation2 (Fin n) h

theorem sub_2141_2138 : Law2141.Subspectral Law2138 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2138.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2141.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2141_implies_Equation2138 (Fin n) h

theorem sub_2143_2142 : Law2143.Subspectral Law2142 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2142.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2143.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2143_implies_Equation2142 (Fin n) h

theorem sub_2146_1496 : Law2146.Subspectral Law1496 := by
  exact (spectrum_eq_of_isDual dual_2146).subset

theorem sub_2147_2145 : Law2147.Subspectral Law2145 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2145.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2147.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2147_implies_Equation2145 (Fin n) h

theorem sub_2150_2138 : Law2150.Subspectral Law2138 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2138.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2150.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2150_implies_Equation2138 (Fin n) h

theorem sub_2151_2149 : Law2151.Subspectral Law2149 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2149.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2151.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2151_implies_Equation2149 (Fin n) h

theorem sub_2153_2138 : Law2153.Subspectral Law2138 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2138.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2153.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2153_implies_Equation2138 (Fin n) h

theorem sub_2155_2154 : Law2155.Subspectral Law2154 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2154.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2155.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2155_implies_Equation2154 (Fin n) h

theorem sub_2157_2155 : Law2157.Subspectral Law2155 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2155.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2157.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2157_implies_Equation2155 (Fin n) h

theorem sub_2158_2154 : Law2158.Subspectral Law2154 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2154.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2158.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2158_implies_Equation2154 (Fin n) h

theorem sub_2159_2154 : Law2159.Subspectral Law2154 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2154.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2159.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2159_implies_Equation2154 (Fin n) h

theorem sub_2160_2133 : Law2160.Subspectral Law2133 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2133.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2160.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2160_implies_Equation2133 (Fin n) h

theorem sub_2162_1485 : Law2162.Subspectral Law1485 := by
  exact (spectrum_eq_of_isDual dual_2162).subset

theorem sub_2163_1483 : Law2163.Subspectral Law1483 := by
  exact (spectrum_eq_of_isDual dual_2163).subset

theorem sub_2164_168 : Law2164.Subspectral Law168 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law168.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2164.models_iff (Fin n) M).mp hM
  exact Equation2164_implies_Equation168 (Fin n) h

theorem sub_2166_876 : Law2166.Subspectral Law876 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law876.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2166.models_iff (Fin n) M).mp hM
  exact Equation2166_implies_Equation876 (Fin n) h

theorem sub_2174_2166 : Law2174.Subspectral Law2166 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2166.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2174.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2174_implies_Equation2166 (Fin n) h

theorem sub_2176_2095 : Law2176.Subspectral Law2095 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2095.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2176.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2176_implies_Equation2095 (Fin n) h

theorem sub_2184_2138 : Law2184.Subspectral Law2138 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2138.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2184.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2184_implies_Equation2138 (Fin n) h

theorem sub_2185_2183 : Law2185.Subspectral Law2183 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2183.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2185.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2185_implies_Equation2183 (Fin n) h

theorem sub_2189_2188 : Law2189.Subspectral Law2188 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2188.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2189.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2189_implies_Equation2188 (Fin n) h

theorem sub_2191_2189 : Law2191.Subspectral Law2189 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2189.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2191.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2191_implies_Equation2189 (Fin n) h

theorem sub_2192_2188 : Law2192.Subspectral Law2188 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2188.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2192.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2192_implies_Equation2188 (Fin n) h

theorem sub_2193_2188 : Law2193.Subspectral Law2188 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2188.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2193.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2193_implies_Equation2188 (Fin n) h

theorem sub_2194_2185 : Law2194.Subspectral Law2185 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2185.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2194.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2194_implies_Equation2185 (Fin n) h

theorem sub_2197_2 : Law2197.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2197.models_iff (Fin n) M).mp hM
  exact Equation2197_implies_Equation2 (Fin n) h

theorem sub_2201_2138 : Law2201.Subspectral Law2138 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2138.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2201.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2201_implies_Equation2138 (Fin n) h

theorem sub_2202_2200 : Law2202.Subspectral Law2200 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2200.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2202.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2202_implies_Equation2200 (Fin n) h

theorem sub_2206_2205 : Law2206.Subspectral Law2205 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2205.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2206.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2206_implies_Equation2205 (Fin n) h

theorem sub_2208_2206 : Law2208.Subspectral Law2206 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2206.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2208.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2208_implies_Equation2206 (Fin n) h

theorem sub_2209_2205 : Law2209.Subspectral Law2205 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2205.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2209.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2209_implies_Equation2205 (Fin n) h

theorem sub_2210_2205 : Law2210.Subspectral Law2205 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2205.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2210.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2210_implies_Equation2205 (Fin n) h

theorem sub_2215_2197 : Law2215.Subspectral Law2197 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2197.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2215.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2215_implies_Equation2197 (Fin n) h

theorem sub_2216_6 : Law2216.Subspectral Law6 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law6.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2216.models_iff (Fin n) M).mp hM
  exact Equation2216_implies_Equation6 (Fin n) h

theorem sub_2218_2200 : Law2218.Subspectral Law2200 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2200.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2218.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2218_implies_Equation2200 (Fin n) h

theorem sub_2221_2218 : Law2221.Subspectral Law2218 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2218.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2221.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2221_implies_Equation2218 (Fin n) h

theorem sub_2224_2205 : Law2224.Subspectral Law2205 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2205.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2224.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2224_implies_Equation2205 (Fin n) h

theorem sub_2225_2205 : Law2225.Subspectral Law2205 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2205.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2225.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2225_implies_Equation2205 (Fin n) h

theorem sub_2226_2224 : Law2226.Subspectral Law2224 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2224.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2226.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2226_implies_Equation2224 (Fin n) h

theorem sub_2228_2226 : Law2228.Subspectral Law2226 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2226.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2228.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2228_implies_Equation2226 (Fin n) h

theorem sub_2229_2205 : Law2229.Subspectral Law2205 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2205.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2229.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2229_implies_Equation2205 (Fin n) h

theorem sub_2231_2230 : Law2231.Subspectral Law2230 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2230.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2231.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2231_implies_Equation2230 (Fin n) h

theorem sub_2294_1313 : Law2294.Subspectral Law1313 := by
  exact (spectrum_eq_of_isDual dual_2294).subset

theorem sub_2295_2508 : Law2295.Subspectral Law2508 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2508.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2295.models_iff (Fin n) M).mp hM
  exact Equation2295_implies_Equation2508 (Fin n) h

theorem sub_2299_2292 : Law2299.Subspectral Law2292 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2292.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2299.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2299_implies_Equation2292 (Fin n) h

theorem sub_2301_1286 : Law2301.Subspectral Law1286 := by
  exact (spectrum_eq_of_isDual dual_2301).subset

theorem sub_2302_223 : Law2302.Subspectral Law223 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law223.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2302.models_iff (Fin n) M).mp hM
  exact Equation2302_implies_Equation223 (Fin n) h

theorem sub_2304_1323 : Law2304.Subspectral Law1323 := by
  exact (spectrum_eq_of_isDual dual_2304).subset

theorem sub_2309_2302 : Law2309.Subspectral Law2302 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2302.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2309.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2309_implies_Equation2302 (Fin n) h

theorem sub_2312_2523 : Law2312.Subspectral Law2523 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2523.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2312.models_iff (Fin n) M).mp hM
  exact Equation2312_implies_Equation2523 (Fin n) h

theorem sub_2315_2 : Law2315.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2315.models_iff (Fin n) M).mp hM
  exact Equation2315_implies_Equation2 (Fin n) h

theorem sub_2316_1368 : Law2316.Subspectral Law1368 := by
  exact (spectrum_eq_of_isDual dual_2316).subset

theorem sub_2317_2305 : Law2317.Subspectral Law2305 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2305.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2317.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2317_implies_Equation2305 (Fin n) h

theorem sub_2320_2523 : Law2320.Subspectral Law2523 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2523.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2320.models_iff (Fin n) M).mp hM
  exact Equation2320_implies_Equation2523 (Fin n) h

theorem sub_2321_2292 : Law2321.Subspectral Law2292 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2292.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2321.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2321_implies_Equation2292 (Fin n) h

theorem sub_2323_2315 : Law2323.Subspectral Law2315 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2315.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2323.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2323_implies_Equation2315 (Fin n) h

theorem sub_2324_2312 : Law2324.Subspectral Law2312 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2312.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2324.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2324_implies_Equation2312 (Fin n) h

theorem sub_2324_2527 : Law2324.Subspectral Law2527 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2527.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2324.models_iff (Fin n) M).mp hM
  exact Equation2324_implies_Equation2527 (Fin n) h

theorem sub_2326_2313 : Law2326.Subspectral Law2313 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2313.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2326.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2326_implies_Equation2313 (Fin n) h

theorem sub_2328_1279 : Law2328.Subspectral Law1279 := by
  exact (spectrum_eq_of_isDual dual_2328).subset

theorem sub_2334_2 : Law2334.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2334.models_iff (Fin n) M).mp hM
  exact Equation2334_implies_Equation2 (Fin n) h

theorem sub_2336_2329 : Law2336.Subspectral Law2329 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2329.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2336.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2336_implies_Equation2329 (Fin n) h

theorem sub_2341_2 : Law2341.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2341.models_iff (Fin n) M).mp hM
  exact Singleton.Equation2341_implies_Equation2 (Fin n) h

theorem sub_2344_2 : Law2344.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2344.models_iff (Fin n) M).mp hM
  exact Singleton.Equation2344_implies_Equation2 (Fin n) h

theorem sub_2348_2 : Law2348.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2348.models_iff (Fin n) M).mp hM
  exact Equation2348_implies_Equation2 (Fin n) h

theorem sub_2350_2348 : Law2350.Subspectral Law2348 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2348.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2350.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2350_implies_Equation2348 (Fin n) h

theorem sub_2356_2354 : Law2356.Subspectral Law2354 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2354.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2356.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2356_implies_Equation2354 (Fin n) h

theorem sub_2366_2603 : Law2366.Subspectral Law2603 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2603.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2366.models_iff (Fin n) M).mp hM
  exact Equation2366_implies_Equation2603 (Fin n) h

theorem sub_2369_2 : Law2369.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2369.models_iff (Fin n) M).mp hM
  exact Equation2369_implies_Equation2 (Fin n) h

theorem sub_2370_1355 : Law2370.Subspectral Law1355 := by
  exact (spectrum_eq_of_isDual dual_2370).subset

theorem sub_2370_3128 : Law2370.Subspectral Law3128 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3128.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2370.models_iff (Fin n) M).mp hM
  exact Equation2370_implies_Equation3128 (Fin n) h

theorem sub_2371_2369 : Law2371.Subspectral Law2369 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2369.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2371.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2371_implies_Equation2369 (Fin n) h

theorem sub_2374_2603 : Law2374.Subspectral Law2603 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2603.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2374.models_iff (Fin n) M).mp hM
  exact Equation2374_implies_Equation2603 (Fin n) h

theorem sub_2383_1301 : Law2383.Subspectral Law1301 := by
  exact (spectrum_eq_of_isDual dual_2383).subset

theorem sub_2383_3128 : Law2383.Subspectral Law3128 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3128.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2383.models_iff (Fin n) M).mp hM
  exact Equation2383_implies_Equation3128 (Fin n) h

theorem sub_2386_237 : Law2386.Subspectral Law237 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law237.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2386.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2386_implies_Equation237 (Fin n) h

theorem sub_2387_2386 : Law2387.Subspectral Law2386 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2386.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2387.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2387_implies_Equation2386 (Fin n) h

theorem sub_2400_2603 : Law2400.Subspectral Law2603 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2603.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2400.models_iff (Fin n) M).mp hM
  exact Equation2400_implies_Equation2603 (Fin n) h

theorem sub_2497_1110 : Law2497.Subspectral Law1110 := by
  exact (spectrum_eq_of_isDual dual_2497).subset

theorem sub_2498_2305 : Law2498.Subspectral Law2305 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2305.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2498.models_iff (Fin n) M).mp hM
  exact Equation2498_implies_Equation2305 (Fin n) h

theorem sub_2500_291 : Law2500.Subspectral Law291 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law291.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2500.models_iff (Fin n) M).mp hM
  exact Equation2500_implies_Equation291 (Fin n) h

theorem sub_2502_2495 : Law2502.Subspectral Law2495 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2495.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2502.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2502_implies_Equation2495 (Fin n) h

theorem sub_2504_1083 : Law2504.Subspectral Law1083 := by
  exact (spectrum_eq_of_isDual dual_2504).subset

theorem sub_2510_2 : Law2510.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2510.models_iff (Fin n) M).mp hM
  exact Equation2510_implies_Equation2 (Fin n) h

theorem sub_2511_1131 : Law2511.Subspectral Law1131 := by
  exact (spectrum_eq_of_isDual dual_2511).subset

theorem sub_2511_3128 : Law2511.Subspectral Law3128 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3128.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2511.models_iff (Fin n) M).mp hM
  exact Equation2511_implies_Equation3128 (Fin n) h

theorem sub_2512_2505 : Law2512.Subspectral Law2505 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2505.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2512.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2512_implies_Equation2505 (Fin n) h

theorem sub_2520_2518 : Law2520.Subspectral Law2518 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2518.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2520.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2520_implies_Equation2518 (Fin n) h

theorem sub_2524_2495 : Law2524.Subspectral Law2495 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2495.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2524.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2524_implies_Equation2495 (Fin n) h

theorem sub_2527_2515 : Law2527.Subspectral Law2515 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2515.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2527.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2527_implies_Equation2515 (Fin n) h

theorem sub_2529_2516 : Law2529.Subspectral Law2516 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2516.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2529.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2529_implies_Equation2516 (Fin n) h

theorem sub_2531_1076 : Law2531.Subspectral Law1076 := by
  exact (spectrum_eq_of_isDual dual_2531).subset

theorem sub_2535_30 : Law2535.Subspectral Law30 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law30.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2535.models_iff (Fin n) M).mp hM
  exact Equation2535_implies_Equation30 (Fin n) h

theorem sub_2539_2532 : Law2539.Subspectral Law2532 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2532.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2539.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2539_implies_Equation2532 (Fin n) h

theorem sub_2542_30 : Law2542.Subspectral Law30 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law30.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2542.models_iff (Fin n) M).mp hM
  exact Equation2542_implies_Equation30 (Fin n) h

theorem sub_2545_2544 : Law2545.Subspectral Law2544 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2544.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2545.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2545_implies_Equation2544 (Fin n) h

theorem sub_2549_2547 : Law2549.Subspectral Law2547 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2547.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2549.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2549_implies_Equation2547 (Fin n) h

theorem sub_2549_2548 : Law2549.Subspectral Law2548 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2548.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2549.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2549_implies_Equation2548 (Fin n) h

theorem sub_2553_2551 : Law2553.Subspectral Law2551 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2551.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2553.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2553_implies_Equation2551 (Fin n) h

theorem sub_2556_2544 : Law2556.Subspectral Law2544 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2544.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2556.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2556_implies_Equation2544 (Fin n) h

theorem sub_2557_2555 : Law2557.Subspectral Law2555 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2555.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2557.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2557_implies_Equation2555 (Fin n) h

theorem sub_2559_2544 : Law2559.Subspectral Law2544 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2544.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2559.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2559_implies_Equation2544 (Fin n) h

theorem sub_2561_2560 : Law2561.Subspectral Law2560 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2560.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2561.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2561_implies_Equation2560 (Fin n) h

theorem sub_2563_2561 : Law2563.Subspectral Law2561 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2561.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2563.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2563_implies_Equation2561 (Fin n) h

theorem sub_2564_2560 : Law2564.Subspectral Law2560 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2560.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2564.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2564_implies_Equation2560 (Fin n) h

theorem sub_2566_2565 : Law2566.Subspectral Law2565 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2565.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2566.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2566_implies_Equation2565 (Fin n) h

theorem sub_2569_240 : Law2569.Subspectral Law240 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law240.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2569.models_iff (Fin n) M).mp hM
  exact Equation2569_implies_Equation240 (Fin n) h

theorem sub_2582_2501 : Law2582.Subspectral Law2501 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2501.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2582.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2582_implies_Equation2501 (Fin n) h

theorem sub_2586_1790 : Law2586.Subspectral Law1790 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1790.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2586.models_iff (Fin n) M).mp hM
  exact Equation2586_implies_Equation1790 (Fin n) h

theorem sub_2590_2544 : Law2590.Subspectral Law2544 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2544.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2590.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2590_implies_Equation2544 (Fin n) h

theorem sub_2591_2589 : Law2591.Subspectral Law2589 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2589.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2591.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2591_implies_Equation2589 (Fin n) h

theorem sub_2593_2544 : Law2593.Subspectral Law2544 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2544.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2593.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2593_implies_Equation2544 (Fin n) h

theorem sub_2595_2594 : Law2595.Subspectral Law2594 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2594.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2595.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2595_implies_Equation2594 (Fin n) h

theorem sub_2598_2594 : Law2598.Subspectral Law2594 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2594.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2598.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2598_implies_Equation2594 (Fin n) h

theorem sub_2600_2599 : Law2600.Subspectral Law2599 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2599.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2600.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2600_implies_Equation2599 (Fin n) h

theorem sub_2603_2577 : Law2603.Subspectral Law2577 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2577.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2603.models_iff (Fin n) M).mp hM
  exact Equation2603_implies_Equation2577 (Fin n) h

theorem sub_2604_2603 : Law2604.Subspectral Law2603 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2603.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2604.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2604_implies_Equation2603 (Fin n) h

theorem sub_2608_2606 : Law2608.Subspectral Law2606 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2606.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2608.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2608_implies_Equation2606 (Fin n) h

theorem sub_2610_2544 : Law2610.Subspectral Law2544 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2544.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2610.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2610_implies_Equation2544 (Fin n) h

theorem sub_2612_2611 : Law2612.Subspectral Law2611 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2611.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2612.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2612_implies_Equation2611 (Fin n) h

theorem sub_2614_2612 : Law2614.Subspectral Law2612 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2612.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2614.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2614_implies_Equation2612 (Fin n) h

theorem sub_2615_2611 : Law2615.Subspectral Law2611 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2611.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2615.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2615_implies_Equation2611 (Fin n) h

theorem sub_2616_2611 : Law2616.Subspectral Law2611 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2611.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2616.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2616_implies_Equation2611 (Fin n) h

theorem sub_2617_2616 : Law2617.Subspectral Law2616 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2616.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2617.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2617_implies_Equation2616 (Fin n) h

theorem sub_2619_2568 : Law2619.Subspectral Law2568 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2568.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2619.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2619_implies_Equation2568 (Fin n) h

theorem sub_2621_2515 : Law2621.Subspectral Law2515 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2515.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2621.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2621_implies_Equation2515 (Fin n) h

theorem sub_2622_2570 : Law2622.Subspectral Law2570 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2570.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2622.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2622_implies_Equation2570 (Fin n) h

theorem sub_2622_2621 : Law2622.Subspectral Law2621 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2621.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2622.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2622_implies_Equation2621 (Fin n) h

theorem sub_2625_2624 : Law2625.Subspectral Law2624 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2624.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2625.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2625_implies_Equation2624 (Fin n) h

theorem sub_2626_2625 : Law2626.Subspectral Law2625 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2625.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2626.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2626_implies_Equation2625 (Fin n) h

theorem sub_2627_2624 : Law2627.Subspectral Law2624 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2624.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2627.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2627_implies_Equation2624 (Fin n) h

theorem sub_2629_2627 : Law2629.Subspectral Law2627 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2627.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2629.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2629_implies_Equation2627 (Fin n) h

theorem sub_2630_2611 : Law2630.Subspectral Law2611 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2611.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2630.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2630_implies_Equation2611 (Fin n) h

theorem sub_2631_2611 : Law2631.Subspectral Law2611 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2611.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2631.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2631_implies_Equation2611 (Fin n) h

theorem sub_2632_2630 : Law2632.Subspectral Law2630 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2630.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2632.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2632_implies_Equation2630 (Fin n) h

theorem sub_2635_2611 : Law2635.Subspectral Law2611 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2611.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2635.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2635_implies_Equation2611 (Fin n) h

theorem sub_2636_2611 : Law2636.Subspectral Law2611 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2611.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2636.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2636_implies_Equation2611 (Fin n) h

theorem sub_2637_2636 : Law2637.Subspectral Law2636 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2636.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2637.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2637_implies_Equation2636 (Fin n) h

theorem sub_2639_2637 : Law2639.Subspectral Law2637 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2637.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2639.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2639_implies_Equation2637 (Fin n) h

theorem sub_2641_2636 : Law2641.Subspectral Law2636 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2636.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2641.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2641_implies_Equation2636 (Fin n) h

theorem sub_2643_2566 : Law2643.Subspectral Law2566 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2566.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2643.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2643_implies_Equation2566 (Fin n) h

theorem sub_2698_2 : Law2698.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2698.models_iff (Fin n) M).mp hM
  exact Equation2698_implies_Equation2 (Fin n) h

theorem sub_2700_907 : Law2700.Subspectral Law907 := by
  exact (spectrum_eq_of_isDual dual_2700).subset

theorem sub_2701_675 : Law2701.Subspectral Law675 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law675.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2701.models_iff (Fin n) M).mp hM
  exact Equation2701_implies_Equation675 (Fin n) h

theorem sub_2703_187 : Law2703.Subspectral Law187 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law187.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2703.models_iff (Fin n) M).mp hM
  exact Equation2703_implies_Equation187 (Fin n) h

theorem sub_2704_69 : Law2704.Subspectral Law69 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law69.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2704.models_iff (Fin n) M).mp hM
  exact Equation2704_implies_Equation69 (Fin n) h

theorem sub_2705_2698 : Law2705.Subspectral Law2698 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2698.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2705.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2705_implies_Equation2698 (Fin n) h

theorem sub_2707_880 : Law2707.Subspectral Law880 := by
  exact (spectrum_eq_of_isDual dual_2707).subset

theorem sub_2708_2 : Law2708.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2708.models_iff (Fin n) M).mp hM
  exact Equation2708_implies_Equation2 (Fin n) h

theorem sub_2711_30 : Law2711.Subspectral Law30 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law30.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2711.models_iff (Fin n) M).mp hM
  exact Equation2711_implies_Equation30 (Fin n) h

theorem sub_2717_688 : Law2717.Subspectral Law688 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law688.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2717.models_iff (Fin n) M).mp hM
  exact Equation2717_implies_Equation688 (Fin n) h

theorem sub_2718_2 : Law2718.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2718.models_iff (Fin n) M).mp hM
  exact Equation2718_implies_Equation2 (Fin n) h

theorem sub_2719_2718 : Law2719.Subspectral Law2718 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2718.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2719.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2719_implies_Equation2718 (Fin n) h

theorem sub_2722_962 : Law2722.Subspectral Law962 := by
  exact (spectrum_eq_of_isDual dual_2722).subset

theorem sub_2722_1913 : Law2722.Subspectral Law1913 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1913.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2722.models_iff (Fin n) M).mp hM
  exact Equation2722_implies_Equation1913 (Fin n) h

theorem sub_2727_2726 : Law2727.Subspectral Law2726 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2726.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2727.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2727_implies_Equation2726 (Fin n) h

theorem sub_2730_2726 : Law2730.Subspectral Law2726 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2726.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2730.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2730_implies_Equation2726 (Fin n) h

theorem sub_2731_2726 : Law2731.Subspectral Law2726 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2726.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2731.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2731_implies_Equation2726 (Fin n) h

theorem sub_2734_873 : Law2734.Subspectral Law873 := by
  exact (spectrum_eq_of_isDual dual_2734).subset

theorem sub_2740_2 : Law2740.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2740.models_iff (Fin n) M).mp hM
  exact Equation2740_implies_Equation2 (Fin n) h

theorem sub_2742_2738 : Law2742.Subspectral Law2738 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2738.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2742.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2742_implies_Equation2738 (Fin n) h

theorem sub_2744_883 : Law2744.Subspectral Law883 := by
  exact (spectrum_eq_of_isDual dual_2744).subset

theorem sub_2752_2751 : Law2752.Subspectral Law2751 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2751.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2752.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2752_implies_Equation2751 (Fin n) h

theorem sub_2755_887 : Law2755.Subspectral Law887 := by
  exact (spectrum_eq_of_isDual dual_2755).subset

theorem sub_2755_1537 : Law2755.Subspectral Law1537 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1537.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2755.models_iff (Fin n) M).mp hM
  exact Equation2755_implies_Equation1537 (Fin n) h

theorem sub_2755_2105 : Law2755.Subspectral Law2105 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2105.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2755.models_iff (Fin n) M).mp hM
  exact Equation2755_implies_Equation2105 (Fin n) h

theorem sub_2755_2319 : Law2755.Subspectral Law2319 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2319.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2755.models_iff (Fin n) M).mp hM
  exact Equation2755_implies_Equation2319 (Fin n) h

theorem sub_2756_2754 : Law2756.Subspectral Law2754 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2754.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2756.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2756_implies_Equation2754 (Fin n) h

theorem sub_2758_2752 : Law2758.Subspectral Law2752 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2752.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2758.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2758_implies_Equation2752 (Fin n) h

theorem sub_2762_2760 : Law2762.Subspectral Law2760 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2760.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2762.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2762_implies_Equation2760 (Fin n) h

theorem sub_2767_2759 : Law2767.Subspectral Law2759 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2759.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2767.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2767_implies_Equation2759 (Fin n) h

theorem sub_2769_2768 : Law2769.Subspectral Law2768 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2768.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2769.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2769_implies_Equation2768 (Fin n) h

theorem sub_2775_2382 : Law2775.Subspectral Law2382 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2382.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2775.models_iff (Fin n) M).mp hM
  exact Equation2775_implies_Equation2382 (Fin n) h

theorem sub_2776_949 : Law2776.Subspectral Law949 := by
  exact (spectrum_eq_of_isDual dual_2776).subset

theorem sub_2776_3185 : Law2776.Subspectral Law3185 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3185.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2776.models_iff (Fin n) M).mp hM
  exact Equation2776_implies_Equation3185 (Fin n) h

theorem sub_2780_2 : Law2780.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2780.models_iff (Fin n) M).mp hM
  exact Equation2780_implies_Equation2 (Fin n) h

theorem sub_2785_2780 : Law2785.Subspectral Law2780 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2780.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2785.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2785_implies_Equation2780 (Fin n) h

theorem sub_2788_538 : Law2788.Subspectral Law538 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law538.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2788.models_iff (Fin n) M).mp hM
  exact Equation2788_implies_Equation538 (Fin n) h

theorem sub_2789_895 : Law2789.Subspectral Law895 := by
  exact (spectrum_eq_of_isDual dual_2789).subset

theorem sub_2789_898 : Law2789.Subspectral Law898 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law898.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2789.models_iff (Fin n) M).mp hM
  exact Equation2789_implies_Equation898 (Fin n) h

theorem sub_2794_2793 : Law2794.Subspectral Law2793 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2793.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2794.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2794_implies_Equation2793 (Fin n) h

theorem sub_2801_2797 : Law2801.Subspectral Law2797 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2797.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2801.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2801_implies_Equation2797 (Fin n) h

theorem sub_2803_2800 : Law2803.Subspectral Law2800 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2800.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2803.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2803_implies_Equation2800 (Fin n) h

theorem sub_2803_2802 : Law2803.Subspectral Law2802 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2802.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2803.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2803_implies_Equation2802 (Fin n) h

theorem sub_2805_898 : Law2805.Subspectral Law898 := by
  exact (spectrum_eq_of_isDual dual_2805).subset

theorem sub_2806_1351 : Law2806.Subspectral Law1351 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1351.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2806.models_iff (Fin n) M).mp hM
  exact Equation2806_implies_Equation1351 (Fin n) h

theorem sub_2811_2809 : Law2811.Subspectral Law2809 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2809.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2811.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2811_implies_Equation2809 (Fin n) h

theorem sub_2813_2811 : Law2813.Subspectral Law2811 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2811.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2813.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2813_implies_Equation2811 (Fin n) h

theorem sub_2814_2813 : Law2814.Subspectral Law2813 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2813.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2814.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2814_implies_Equation2813 (Fin n) h

theorem sub_2818_2810 : Law2818.Subspectral Law2810 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2810.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2818.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2818_implies_Equation2810 (Fin n) h

theorem sub_2820_2819 : Law2820.Subspectral Law2819 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2819.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2820.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2820_implies_Equation2819 (Fin n) h

theorem sub_2825_2790 : Law2825.Subspectral Law2790 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2790.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2825.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2825_implies_Equation2790 (Fin n) h

theorem sub_2828_2810 : Law2828.Subspectral Law2810 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2810.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2828.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2828_implies_Equation2810 (Fin n) h

theorem sub_2830_2827 : Law2830.Subspectral Law2827 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2827.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2830.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2830_implies_Equation2827 (Fin n) h

theorem sub_2835_2815 : Law2835.Subspectral Law2815 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2815.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2835.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2835_implies_Equation2815 (Fin n) h

theorem sub_2835_2834 : Law2835.Subspectral Law2834 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2834.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2835.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2835_implies_Equation2834 (Fin n) h

theorem sub_2840_2837 : Law2840.Subspectral Law2837 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2837.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2840.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2840_implies_Equation2837 (Fin n) h

theorem sub_2842_2832 : Law2842.Subspectral Law2832 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2832.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2842.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2842_implies_Equation2832 (Fin n) h

theorem sub_2846_2845 : Law2846.Subspectral Law2845 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2845.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2846.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2846_implies_Equation2845 (Fin n) h

theorem sub_2900_667 : Law2900.Subspectral Law667 := by
  exact (spectrum_eq_of_isDual dual_2900).subset

theorem sub_2901_1499 : Law2901.Subspectral Law1499 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1499.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2901.models_iff (Fin n) M).mp hM
  exact Equation2901_implies_Equation1499 (Fin n) h

theorem sub_2903_704 : Law2903.Subspectral Law704 := by
  exact (spectrum_eq_of_isDual dual_2903).subset

theorem sub_2904_30 : Law2904.Subspectral Law30 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law30.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2904.models_iff (Fin n) M).mp hM
  exact Equation2904_implies_Equation30 (Fin n) h

theorem sub_2906_494 : Law2906.Subspectral Law494 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law494.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2906.models_iff (Fin n) M).mp hM
  exact Equation2906_implies_Equation494 (Fin n) h

theorem sub_2908_3148 : Law2908.Subspectral Law3148 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3148.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2908.models_iff (Fin n) M).mp hM
  exact Equation2908_implies_Equation3148 (Fin n) h

theorem sub_2910_677 : Law2910.Subspectral Law677 := by
  exact (spectrum_eq_of_isDual dual_2910).subset

theorem sub_2916_2010 : Law2916.Subspectral Law2010 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2010.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2916.models_iff (Fin n) M).mp hM
  exact Equation2916_implies_Equation2010 (Fin n) h

theorem sub_2918_2911 : Law2918.Subspectral Law2911 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2911.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2918.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2918_implies_Equation2911 (Fin n) h

theorem sub_2920_1151 : Law2920.Subspectral Law1151 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1151.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2920.models_iff (Fin n) M).mp hM
  exact Equation2920_implies_Equation1151 (Fin n) h

theorem sub_2920_2729 : Law2920.Subspectral Law2729 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2729.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2920.models_iff (Fin n) M).mp hM
  exact Equation2920_implies_Equation2729 (Fin n) h

theorem sub_2921_890 : Law2921.Subspectral Law890 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law890.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2921.models_iff (Fin n) M).mp hM
  exact Equation2921_implies_Equation890 (Fin n) h

theorem sub_2924_1147 : Law2924.Subspectral Law1147 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1147.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2924.models_iff (Fin n) M).mp hM
  exact Equation2924_implies_Equation1147 (Fin n) h

theorem sub_2928_749 : Law2928.Subspectral Law749 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law749.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2928.models_iff (Fin n) M).mp hM
  exact Equation2928_implies_Equation749 (Fin n) h

theorem sub_2929_2 : Law2929.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2929.models_iff (Fin n) M).mp hM
  exact Equation2929_implies_Equation2 (Fin n) h

theorem sub_2930_2929 : Law2930.Subspectral Law2929 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2929.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2930.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2930_implies_Equation2929 (Fin n) h

theorem sub_2933_3136 : Law2933.Subspectral Law3136 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3136.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2933.models_iff (Fin n) M).mp hM
  exact Equation2933_implies_Equation3136 (Fin n) h

theorem sub_2935_2930 : Law2935.Subspectral Law2930 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2930.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2935.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2935_implies_Equation2930 (Fin n) h

theorem sub_2937_670 : Law2937.Subspectral Law670 := by
  exact (spectrum_eq_of_isDual dual_2937).subset

theorem sub_2938_2922 : Law2938.Subspectral Law2922 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2922.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2938.models_iff (Fin n) M).mp hM
  exact Equation2938_implies_Equation2922 (Fin n) h

theorem sub_2943_3123 : Law2943.Subspectral Law3123 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3123.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2943.models_iff (Fin n) M).mp hM
  exact Equation2943_implies_Equation3123 (Fin n) h

theorem sub_2945_1317 : Law2945.Subspectral Law1317 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1317.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2945.models_iff (Fin n) M).mp hM
  exact Equation2945_implies_Equation1317 (Fin n) h

theorem sub_2951_2950 : Law2951.Subspectral Law2950 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2950.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2951.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2951_implies_Equation2950 (Fin n) h

theorem sub_2953_2950 : Law2953.Subspectral Law2950 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2950.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2953.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2953_implies_Equation2950 (Fin n) h

theorem sub_2955_2948 : Law2955.Subspectral Law2948 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2948.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2955.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2955_implies_Equation2948 (Fin n) h

theorem sub_2959_2938 : Law2959.Subspectral Law2938 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2938.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2959.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2959_implies_Equation2938 (Fin n) h

theorem sub_2962_2950 : Law2962.Subspectral Law2950 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2950.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2962.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2962_implies_Equation2950 (Fin n) h

theorem sub_2963_2961 : Law2963.Subspectral Law2961 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2961.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2963.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2963_implies_Equation2961 (Fin n) h

theorem sub_2965_2950 : Law2965.Subspectral Law2950 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2950.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2965.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2965_implies_Equation2950 (Fin n) h

theorem sub_2967_2966 : Law2967.Subspectral Law2966 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2966.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2967.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2967_implies_Equation2966 (Fin n) h

theorem sub_2969_2967 : Law2969.Subspectral Law2967 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2967.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2969.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2969_implies_Equation2967 (Fin n) h

theorem sub_2972_2955 : Law2972.Subspectral Law2955 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2955.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2972.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2972_implies_Equation2955 (Fin n) h

theorem sub_2974_1683 : Law2974.Subspectral Law1683 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1683.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2974.models_iff (Fin n) M).mp hM
  exact Equation2974_implies_Equation1683 (Fin n) h

theorem sub_2976_2938 : Law2976.Subspectral Law2938 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2938.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2976.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2976_implies_Equation2938 (Fin n) h

theorem sub_2980_2978 : Law2980.Subspectral Law2978 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2978.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2980.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2980_implies_Equation2978 (Fin n) h

theorem sub_2982_749 : Law2982.Subspectral Law749 := by
  exact (spectrum_eq_of_isDual dual_2982).subset

theorem sub_2983_1294 : Law2983.Subspectral Law1294 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1294.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2983.models_iff (Fin n) M).mp hM
  exact Equation2983_implies_Equation1294 (Fin n) h

theorem sub_2987_3190 : Law2987.Subspectral Law3190 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3190.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2987.models_iff (Fin n) M).mp hM
  exact Equation2987_implies_Equation3190 (Fin n) h

theorem sub_2989_2980 : Law2989.Subspectral Law2980 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2980.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2989.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2989_implies_Equation2980 (Fin n) h

theorem sub_2989_2988 : Law2989.Subspectral Law2988 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2988.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2989.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2989_implies_Equation2988 (Fin n) h

theorem sub_2991_1706 : Law2991.Subspectral Law1706 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1706.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2991.models_iff (Fin n) M).mp hM
  exact Equation2991_implies_Equation1706 (Fin n) h

theorem sub_2993_2911 : Law2993.Subspectral Law2911 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2911.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2993.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2993_implies_Equation2911 (Fin n) h

theorem sub_2996_2995 : Law2996.Subspectral Law2995 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2995.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2996.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation2996_implies_Equation2995 (Fin n) h

theorem sub_2997_2995 : Law2997.Subspectral Law2995 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2995.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2997.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2997_implies_Equation2995 (Fin n) h

theorem sub_2999_2950 : Law2999.Subspectral Law2950 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2950.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law2999.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation2999_implies_Equation2950 (Fin n) h

theorem sub_3001_3000 : Law3001.Subspectral Law3000 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3000.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3001.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3001_implies_Equation3000 (Fin n) h

theorem sub_3003_2995 : Law3003.Subspectral Law2995 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2995.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3003.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3003_implies_Equation2995 (Fin n) h

theorem sub_3004_3003 : Law3004.Subspectral Law3003 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3003.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3004.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3004_implies_Equation3003 (Fin n) h

theorem sub_3005_2995 : Law3005.Subspectral Law2995 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2995.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3005.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3005_implies_Equation2995 (Fin n) h

theorem sub_3006_3003 : Law3006.Subspectral Law3003 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3003.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3006.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3006_implies_Equation3003 (Fin n) h

theorem sub_3006_3005 : Law3006.Subspectral Law3005 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3005.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3006.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3006_implies_Equation3005 (Fin n) h

theorem sub_3008_695 : Law3008.Subspectral Law695 := by
  exact (spectrum_eq_of_isDual dual_3008).subset

theorem sub_3008_1710 : Law3008.Subspectral Law1710 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1710.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3008.models_iff (Fin n) M).mp hM
  exact Equation3008_implies_Equation1710 (Fin n) h

theorem sub_3009_475 : Law3009.Subspectral Law475 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law475.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3009.models_iff (Fin n) M).mp hM
  exact Equation3009_implies_Equation475 (Fin n) h

theorem sub_3014_3012 : Law3014.Subspectral Law3012 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3012.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3014.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3014_implies_Equation3012 (Fin n) h

theorem sub_3018_3017 : Law3018.Subspectral Law3017 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3017.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3018.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3018_implies_Equation3017 (Fin n) h

theorem sub_3020_3012 : Law3020.Subspectral Law3012 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3012.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3020.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3020_implies_Equation3012 (Fin n) h

theorem sub_3025_2920 : Law3025.Subspectral Law2920 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2920.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3025.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3025_implies_Equation2920 (Fin n) h

theorem sub_3027_3119 : Law3027.Subspectral Law3119 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3119.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3027.models_iff (Fin n) M).mp hM
  exact Equation3027_implies_Equation3119 (Fin n) h

theorem sub_3028_2993 : Law3028.Subspectral Law2993 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2993.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3028.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3028_implies_Equation2993 (Fin n) h

theorem sub_3030_303 : Law3030.Subspectral Law303 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law303.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3030.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3030_implies_Equation303 (Fin n) h

theorem sub_3031_3030 : Law3031.Subspectral Law3030 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3030.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3031.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3031_implies_Equation3030 (Fin n) h

theorem sub_3035_3033 : Law3035.Subspectral Law3033 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3033.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3035.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3035_implies_Equation3033 (Fin n) h

theorem sub_3037_3036 : Law3037.Subspectral Law3036 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3036.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3037.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3037_implies_Equation3036 (Fin n) h

theorem sub_3038_3036 : Law3038.Subspectral Law3036 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3036.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3038.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3038_implies_Equation3036 (Fin n) h

theorem sub_3040_304 : Law3040.Subspectral Law304 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law304.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3040.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3040_implies_Equation304 (Fin n) h

theorem sub_3041_3017 : Law3041.Subspectral Law3017 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3017.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3041.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3041_implies_Equation3017 (Fin n) h

theorem sub_3045_3040 : Law3045.Subspectral Law3040 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3040.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3045.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3045_implies_Equation3040 (Fin n) h

theorem sub_3049_3043 : Law3049.Subspectral Law3043 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3043.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3049.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3049_implies_Equation3043 (Fin n) h

theorem sub_3104_2 : Law3104.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3104.models_iff (Fin n) M).mp hM
  exact Equation3104_implies_Equation2 (Fin n) h

theorem sub_3106_501 : Law3106.Subspectral Law501 := by
  exact (spectrum_eq_of_isDual dual_3106).subset

theorem sub_3113_474 : Law3113.Subspectral Law474 := by
  exact (spectrum_eq_of_isDual dual_3113).subset

theorem sub_3117_1886 : Law3117.Subspectral Law1886 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1886.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3117.models_iff (Fin n) M).mp hM
  exact Equation3117_implies_Equation1886 (Fin n) h

theorem sub_3123_507 : Law3123.Subspectral Law507 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law507.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3123.models_iff (Fin n) M).mp hM
  exact Equation3123_implies_Equation507 (Fin n) h

theorem sub_3124_2 : Law3124.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3124.models_iff (Fin n) M).mp hM
  exact Equation3124_implies_Equation2 (Fin n) h

theorem sub_3125_3104 : Law3125.Subspectral Law3104 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3104.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3125.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3125_implies_Equation3104 (Fin n) h

theorem sub_3128_556 : Law3128.Subspectral Law556 := by
  exact (spectrum_eq_of_isDual dual_3128).subset

theorem sub_3128_1301 : Law3128.Subspectral Law1301 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1301.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3128.models_iff (Fin n) M).mp hM
  exact Equation3128_implies_Equation1301 (Fin n) h

theorem sub_3129_3107 : Law3129.Subspectral Law3107 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3107.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3129.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3129_implies_Equation3107 (Fin n) h

theorem sub_3136_3124 : Law3136.Subspectral Law3124 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3124.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3136.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3136_implies_Equation3124 (Fin n) h

theorem sub_3138_3125 : Law3138.Subspectral Law3125 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3125.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3138.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3138_implies_Equation3125 (Fin n) h

theorem sub_3140_467 : Law3140.Subspectral Law467 := by
  exact (spectrum_eq_of_isDual dual_3140).subset

theorem sub_3144_1490 : Law3144.Subspectral Law1490 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1490.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3144.models_iff (Fin n) M).mp hM
  exact Equation3144_implies_Equation1490 (Fin n) h

theorem sub_3148_3146 : Law3148.Subspectral Law3146 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3146.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3148.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3148_implies_Equation3146 (Fin n) h

theorem sub_3151_908 : Law3151.Subspectral Law908 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law908.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3151.models_iff (Fin n) M).mp hM
  exact Equation3151_implies_Equation908 (Fin n) h

theorem sub_3153_306 : Law3153.Subspectral Law306 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law306.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3153.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3153_implies_Equation306 (Fin n) h

theorem sub_3154_2 : Law3154.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3154.models_iff (Fin n) M).mp hM
  exact Singleton.Equation3154_implies_Equation2 (Fin n) h

theorem sub_3156_2 : Law3156.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3156.models_iff (Fin n) M).mp hM
  exact Singleton.Equation3156_implies_Equation2 (Fin n) h

theorem sub_3158_3157 : Law3158.Subspectral Law3157 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3157.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3158.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3158_implies_Equation3157 (Fin n) h

theorem sub_3161_481 : Law3161.Subspectral Law481 := by
  exact (spectrum_eq_of_isDual dual_3161).subset

theorem sub_3162_293 : Law3162.Subspectral Law293 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law293.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3162.models_iff (Fin n) M).mp hM
  exact Equation3162_implies_Equation293 (Fin n) h

theorem sub_3164_3158 : Law3164.Subspectral Law3158 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3158.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3164.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3164_implies_Equation3158 (Fin n) h

theorem sub_3165_3164 : Law3165.Subspectral Law3164 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3164.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3165.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3165_implies_Equation3164 (Fin n) h

theorem sub_3168_3166 : Law3168.Subspectral Law3166 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3166.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3168.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3168_implies_Equation3166 (Fin n) h

theorem sub_3170_3169 : Law3170.Subspectral Law3169 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3169.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3170.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3170_implies_Equation3169 (Fin n) h

theorem sub_3177_1765 : Law3177.Subspectral Law1765 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1765.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3177.models_iff (Fin n) M).mp hM
  exact Equation3177_implies_Equation1765 (Fin n) h

theorem sub_3178_2 : Law3178.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3178.models_iff (Fin n) M).mp hM
  exact Equation3178_implies_Equation2 (Fin n) h

theorem sub_3185_546 : Law3185.Subspectral Law546 := by
  exact (spectrum_eq_of_isDual dual_3185).subset

theorem sub_3185_2722 : Law3185.Subspectral Law2722 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2722.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3185.models_iff (Fin n) M).mp hM
  exact Equation3185_implies_Equation2722 (Fin n) h

theorem sub_3187_3104 : Law3187.Subspectral Law3104 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3104.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3187.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3187_implies_Equation3104 (Fin n) h

theorem sub_3189_3146 : Law3189.Subspectral Law3146 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3146.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3189.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3189_implies_Equation3146 (Fin n) h

theorem sub_3194_884 : Law3194.Subspectral Law884 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law884.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3194.models_iff (Fin n) M).mp hM
  exact Equation3194_implies_Equation884 (Fin n) h

theorem sub_3196_3194 : Law3196.Subspectral Law3194 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3194.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3196.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3196_implies_Equation3194 (Fin n) h

theorem sub_3199_3198 : Law3199.Subspectral Law3198 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3198.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3199.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3199_implies_Equation3198 (Fin n) h

theorem sub_3200_3198 : Law3200.Subspectral Law3198 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3198.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3200.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3200_implies_Equation3198 (Fin n) h

theorem sub_3202_3200 : Law3202.Subspectral Law3200 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3200.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3202.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3202_implies_Equation3200 (Fin n) h

theorem sub_3204_3203 : Law3204.Subspectral Law3203 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3203.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3204.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3204_implies_Equation3203 (Fin n) h

theorem sub_3206_3198 : Law3206.Subspectral Law3198 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3198.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3206.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3206_implies_Equation3198 (Fin n) h

theorem sub_3207_3206 : Law3207.Subspectral Law3206 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3206.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3207.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3207_implies_Equation3206 (Fin n) h

theorem sub_3208_3198 : Law3208.Subspectral Law3198 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3198.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3208.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3208_implies_Equation3198 (Fin n) h

theorem sub_3209_3208 : Law3209.Subspectral Law3208 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3208.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3209.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3209_implies_Equation3208 (Fin n) h

theorem sub_3212_2 : Law3212.Subspectral Law2 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3212.models_iff (Fin n) M).mp hM
  exact Equation3212_implies_Equation2 (Fin n) h

theorem sub_3213_3104 : Law3213.Subspectral Law3104 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3104.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3213.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3213_implies_Equation3104 (Fin n) h

theorem sub_3217_3215 : Law3217.Subspectral Law3215 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3215.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3217.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3217_implies_Equation3215 (Fin n) h

theorem sub_3219_3217 : Law3219.Subspectral Law3217 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3217.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3219.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3219_implies_Equation3217 (Fin n) h

theorem sub_3223_3215 : Law3223.Subspectral Law3215 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3215.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3223.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3223_implies_Equation3215 (Fin n) h

theorem sub_3226_3213 : Law3226.Subspectral Law3213 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3213.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3226.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3226_implies_Equation3213 (Fin n) h

theorem sub_3228_3123 : Law3228.Subspectral Law3123 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3123.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3228.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3228_implies_Equation3123 (Fin n) h

theorem sub_3233_3226 : Law3233.Subspectral Law3226 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3226.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3233.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3233_implies_Equation3226 (Fin n) h

theorem sub_3234_3233 : Law3234.Subspectral Law3233 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3233.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3234.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3234_implies_Equation3233 (Fin n) h

theorem sub_3235_3216 : Law3235.Subspectral Law3216 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3216.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3235.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3235_implies_Equation3216 (Fin n) h

theorem sub_3236_3129 : Law3236.Subspectral Law3129 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3129.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3236.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3236_implies_Equation3129 (Fin n) h

theorem sub_3238_3236 : Law3238.Subspectral Law3236 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3236.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3238.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3238_implies_Equation3236 (Fin n) h

theorem sub_3239_3186 : Law3239.Subspectral Law3186 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3186.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3239.models_iff (Fin n) M).mp hM
  exact SimpleRewrites.Equation3239_implies_Equation3186 (Fin n) h

theorem sub_3243_3241 : Law3243.Subspectral Law3241 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3241.models_iff (Fin n) M).mpr ?_⟩
  have h := (@Law3243.models_iff (Fin n) M).mp hM
  exact RewriteHypothesisAndGoal.Equation3243_implies_Equation3241 (Fin n) h

theorem sub_17_577 : Law17.Subspectral Law577 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_17, spectrum_eq_of_isDual dual_577]
  exact sub_32_3199

theorem sub_21_613 : Law21.Subspectral Law613 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_21, spectrum_eq_of_isDual dual_613]
  exact sub_33_3252

theorem sub_22_18 : Law22.Subspectral Law18 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_22, spectrum_eq_of_isDual dual_18]
  exact sub_37_36

theorem sub_30_293 : Law30.Subspectral Law293 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_30, spectrum_eq_of_isDual dual_293]
  exact sub_15_71

theorem sub_36_1936 : Law36.Subspectral Law1936 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_36, spectrum_eq_of_isDual dual_1936]
  exact sub_18_1799

theorem sub_64_472 : Law64.Subspectral Law472 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_64, spectrum_eq_of_isDual dual_472]
  exact sub_272_3179

theorem sub_67_2544 : Law67.Subspectral Law2544 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_67, spectrum_eq_of_isDual dual_2544]
  exact sub_292_1123

theorem sub_69_292 : Law69.Subspectral Law292 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_69, spectrum_eq_of_isDual dual_292]
  exact sub_291_67

theorem sub_70_1567 : Law70.Subspectral Law1567 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_70, spectrum_eq_of_isDual dual_1567]
  exact sub_282_2133

theorem sub_76_925 : Law76.Subspectral Law925 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_76, spectrum_eq_of_isDual dual_925]
  exact sub_284_2839

theorem sub_77_766 : Law77.Subspectral Law766 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_77, spectrum_eq_of_isDual dual_766]
  exact sub_300_2999

theorem sub_83_995 : Law83.Subspectral Law995 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_83, spectrum_eq_of_isDual dual_995]
  exact sub_277_2729

theorem sub_84_1606 : Law84.Subspectral Law1606 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_84, spectrum_eq_of_isDual dual_1606]
  exact sub_275_2106

theorem sub_85_74 : Law85.Subspectral Law74 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_85, spectrum_eq_of_isDual dual_74]
  exact sub_279_278

theorem sub_87_92 : Law87.Subspectral Law92 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_87, spectrum_eq_of_isDual dual_92]
  exact sub_287_285

theorem sub_88_809 : Law88.Subspectral Law809 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_88, spectrum_eq_of_isDual dual_809]
  exact sub_296_2955

theorem sub_96_92 : Law96.Subspectral Law92 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_96, spectrum_eq_of_isDual dual_92]
  exact sub_297_285

theorem sub_97_92 : Law97.Subspectral Law92 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_97, spectrum_eq_of_isDual dual_92]
  exact sub_289_285

theorem sub_116_878 : Law116.Subspectral Law878 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_116, spectrum_eq_of_isDual dual_878]
  exact sub_220_2773

theorem sub_123_119 : Law123.Subspectral Law119 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_123, spectrum_eq_of_isDual dual_119]
  exact sub_241_240

theorem sub_131_1414 : Law131.Subspectral Law1414 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_131, spectrum_eq_of_isDual dual_1414]
  exact sub_243_2429

theorem sub_132_1398 : Law132.Subspectral Law1398 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_132, spectrum_eq_of_isDual dual_1398]
  exact sub_236_2358

theorem sub_139_1418 : Law139.Subspectral Law1418 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_139, spectrum_eq_of_isDual dual_1418]
  exact sub_235_2346

theorem sub_140_1348 : Law140.Subspectral Law1348 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_140, spectrum_eq_of_isDual dual_1348]
  exact sub_244_2439

theorem sub_168_2164 : Law168.Subspectral Law2164 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_168, spectrum_eq_of_isDual dual_2164]
  exact sub_168_1487

theorem sub_171_1497 : Law171.Subspectral Law1497 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_171, spectrum_eq_of_isDual dual_1497]
  exact sub_188_2215

theorem sub_173_3230 : Law173.Subspectral Law3230 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_173, spectrum_eq_of_isDual dual_3230]
  exact sub_187_482

theorem sub_178_1524 : Law178.Subspectral Law1524 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_178, spectrum_eq_of_isDual dual_1524]
  exact sub_174_2176

theorem sub_181_1830 : Law181.Subspectral Law1830 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_181, spectrum_eq_of_isDual dual_1830]
  exact sub_196_1957

theorem sub_189_2216 : Law189.Subspectral Law2216 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_189, spectrum_eq_of_isDual dual_2216]
  exact sub_175_1514

theorem sub_191_1991 : Law191.Subspectral Law1991 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_191, spectrum_eq_of_isDual dual_1991]
  exact sub_183_1829

theorem sub_192_183 : Law192.Subspectral Law183 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_192, spectrum_eq_of_isDual dual_183]
  exact sub_192_191

theorem sub_195_1818 : Law195.Subspectral Law1818 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_195, spectrum_eq_of_isDual dual_1818]
  exact sub_195_1948

theorem sub_197_181 : Law197.Subspectral Law181 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_197, spectrum_eq_of_isDual dual_181]
  exact sub_197_196

theorem sub_199_183 : Law199.Subspectral Law183 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_199, spectrum_eq_of_isDual dual_183]
  exact sub_199_191

theorem sub_200_183 : Law200.Subspectral Law183 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_200, spectrum_eq_of_isDual dual_183]
  exact sub_193_191

theorem sub_219_873 : Law219.Subspectral Law873 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_219, spectrum_eq_of_isDual dual_873]
  exact sub_115_2734

theorem sub_220_1893 : Law220.Subspectral Law1893 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_220, spectrum_eq_of_isDual dual_1893]
  exact sub_116_1758

theorem sub_223_1903 : Law223.Subspectral Law1903 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_223, spectrum_eq_of_isDual dual_1903]
  exact sub_136_1809

theorem sub_225_2323 : Law225.Subspectral Law2323 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_225, spectrum_eq_of_isDual dual_2323]
  exact sub_135_1401

theorem sub_226_2785 : Law226.Subspectral Law2785 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_226, spectrum_eq_of_isDual dual_2785]
  exact sub_126_915

theorem sub_230_1930 : Law230.Subspectral Law1930 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_230, spectrum_eq_of_isDual dual_1930]
  exact sub_122_1770

theorem sub_232_2643 : Law232.Subspectral Law2643 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_232, spectrum_eq_of_isDual dual_2643]
  exact sub_128_1222

theorem sub_233_2 : Law233.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_233, spectrum_eq_of_isDual dual_2]
  exact sub_144_2

theorem sub_237_2 : Law237.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_237, spectrum_eq_of_isDual dual_2]
  exact sub_149_2

theorem sub_239_2619 : Law239.Subspectral Law2619 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_239, spectrum_eq_of_isDual dual_2619]
  exact sub_121_1105

theorem sub_240_2824 : Law240.Subspectral Law2824 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_240, spectrum_eq_of_isDual dual_2824]
  exact sub_119_888

theorem sub_241_1974 : Law241.Subspectral Law1974 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_241, spectrum_eq_of_isDual dual_1974]
  exact sub_123_1771

theorem sub_244_2434 : Law244.Subspectral Law2434 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_244, spectrum_eq_of_isDual dual_2434]
  exact sub_140_1399

theorem sub_245_2 : Law245.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_245, spectrum_eq_of_isDual dual_2]
  exact sub_148_2

theorem sub_247_2440 : Law247.Subspectral Law2440 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_247, spectrum_eq_of_isDual dual_2440]
  exact sub_143_1425

theorem sub_248_232 : Law248.Subspectral Law232 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_248, spectrum_eq_of_isDual dual_232]
  exact sub_129_128

theorem sub_249_233 : Law249.Subspectral Law233 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_249, spectrum_eq_of_isDual dual_233]
  exact sub_145_144

theorem sub_251_2 : Law251.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_251, spectrum_eq_of_isDual dual_2]
  exact sub_147_2

theorem sub_252_235 : Law252.Subspectral Law235 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_252, spectrum_eq_of_isDual dual_235]
  exact sub_141_139

theorem sub_253_2386 : Law253.Subspectral Law2386 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_253, spectrum_eq_of_isDual dual_2386]
  exact sub_133_1329

theorem sub_254_237 : Law254.Subspectral Law237 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_254, spectrum_eq_of_isDual dual_237]
  exact sub_150_149

theorem sub_272_2096 : Law272.Subspectral Law2096 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_272, spectrum_eq_of_isDual dual_2096]
  exact sub_64_1555

theorem sub_278_2832 : Law278.Subspectral Law2832 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_278, spectrum_eq_of_isDual dual_2832]
  exact sub_74_1005

theorem sub_285_299 : Law285.Subspectral Law299 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_285, spectrum_eq_of_isDual dual_299]
  exact sub_92_91

theorem sub_293_6 : Law293.Subspectral Law6 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_293, spectrum_eq_of_isDual dual_6]
  exact sub_71_6

theorem sub_295_2967 : Law295.Subspectral Law2967 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_295, spectrum_eq_of_isDual dual_2967]
  exact sub_79_789

theorem sub_299_304 : Law299.Subspectral Law304 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_299, spectrum_eq_of_isDual dual_304]
  exact sub_91_89

theorem sub_301_2839 : Law301.Subspectral Law2839 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_301, spectrum_eq_of_isDual dual_2839]
  exact sub_93_925

theorem sub_303_299 : Law303.Subspectral Law299 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_303, spectrum_eq_of_isDual dual_299]
  exact sub_95_91

theorem sub_304_2 : Law304.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_304, spectrum_eq_of_isDual dual_2]
  exact sub_89_2

theorem sub_305_278 : Law305.Subspectral Law278 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_305, spectrum_eq_of_isDual dual_278]
  exact sub_81_74

theorem sub_306_2844 : Law306.Subspectral Law2844 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_306, spectrum_eq_of_isDual dual_2844]
  exact sub_98_976

theorem sub_465_2 : Law465.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_465, spectrum_eq_of_isDual dual_2]
  exact sub_3104_2

theorem sub_468_2 : Law468.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_468, spectrum_eq_of_isDual dual_2]
  exact sub_3178_2

theorem sub_470_1926 : Law470.Subspectral Law1926 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_470, spectrum_eq_of_isDual dual_1926]
  exact sub_3177_1765

theorem sub_475_2 : Law475.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_475, spectrum_eq_of_isDual dual_2]
  exact sub_3124_2

theorem sub_478_2 : Law478.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_478, spectrum_eq_of_isDual dual_2]
  exact sub_3212_2

theorem sub_480_2806 : Law480.Subspectral Law2806 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_480, spectrum_eq_of_isDual dual_2806]
  exact sub_3194_884

theorem sub_484_3181 : Law484.Subspectral Law3181 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_484, spectrum_eq_of_isDual dual_3181]
  exact sub_3123_507

theorem sub_486_465 : Law486.Subspectral Law465 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_486, spectrum_eq_of_isDual dual_465]
  exact sub_3125_3104

theorem sub_493_2704 : Law493.Subspectral Law2704 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_493, spectrum_eq_of_isDual dual_2704]
  exact sub_3151_908

theorem sub_494_465 : Law494.Subspectral Law465 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_494, spectrum_eq_of_isDual dual_465]
  exact sub_3213_3104

theorem sub_496_484 : Law496.Subspectral Law484 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_496, spectrum_eq_of_isDual dual_484]
  exact sub_3228_3123

theorem sub_497_480 : Law497.Subspectral Law480 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_497, spectrum_eq_of_isDual dual_480]
  exact sub_3196_3194

theorem sub_498_71 : Law498.Subspectral Law71 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_498, spectrum_eq_of_isDual dual_71]
  exact sub_3162_293

theorem sub_514_98 : Law514.Subspectral Law98 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_514, spectrum_eq_of_isDual dual_98]
  exact sub_3153_306

theorem sub_527_505 : Law527.Subspectral Law505 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_527, spectrum_eq_of_isDual dual_505]
  exact sub_3239_3186

theorem sub_533_607 : Law533.Subspectral Law607 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_533, spectrum_eq_of_isDual dual_607]
  exact sub_3233_3226

theorem sub_534_517 : Law534.Subspectral Law517 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_534, spectrum_eq_of_isDual dual_517]
  exact sub_3208_3198

theorem sub_546_962 : Law546.Subspectral Law962 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_546, spectrum_eq_of_isDual dual_962]
  exact sub_3185_2722

theorem sub_547_2109 : Law547.Subspectral Law2109 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_547, spectrum_eq_of_isDual dual_2109]
  exact sub_3144_1490

theorem sub_548_465 : Law548.Subspectral Law465 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_548, spectrum_eq_of_isDual dual_465]
  exact sub_3187_3104

theorem sub_550_542 : Law550.Subspectral Law542 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_550, spectrum_eq_of_isDual dual_542]
  exact sub_3189_3146

theorem sub_552_542 : Law552.Subspectral Law542 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_552, spectrum_eq_of_isDual dual_542]
  exact sub_3148_3146

theorem sub_556_2383 : Law556.Subspectral Law2383 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_556, spectrum_eq_of_isDual dual_2383]
  exact sub_3128_1301

theorem sub_557_475 : Law557.Subspectral Law475 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_557, spectrum_eq_of_isDual dual_475]
  exact sub_3136_3124

theorem sub_559_2 : Law559.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_559, spectrum_eq_of_isDual dual_2]
  exact sub_3156_2

theorem sub_563_585 : Law563.Subspectral Law585 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_563, spectrum_eq_of_isDual dual_585]
  exact sub_3202_3200

theorem sub_564_525 : Law564.Subspectral Law525 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_564, spectrum_eq_of_isDual dual_525]
  exact sub_3165_3164

theorem sub_567_517 : Law567.Subspectral Law517 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_567, spectrum_eq_of_isDual dual_517]
  exact sub_3206_3198

theorem sub_573_1683 : Law573.Subspectral Law1683 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_573, spectrum_eq_of_isDual dual_1683]
  exact sub_3117_1886

theorem sub_576_600 : Law576.Subspectral Law600 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_576, spectrum_eq_of_isDual dual_600]
  exact sub_3168_3166

theorem sub_577_517 : Law577.Subspectral Law517 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_577, spectrum_eq_of_isDual dual_517]
  exact sub_3199_3198

theorem sub_580_605 : Law580.Subspectral Law605 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_580, spectrum_eq_of_isDual dual_605]
  exact sub_3219_3217

theorem sub_581_2 : Law581.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_581, spectrum_eq_of_isDual dual_2]
  exact sub_3154_2

theorem sub_584_602 : Law584.Subspectral Law602 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_584, spectrum_eq_of_isDual dual_602]
  exact sub_3243_3241

theorem sub_585_517 : Law585.Subspectral Law517 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_585, spectrum_eq_of_isDual dual_517]
  exact sub_3200_3198

theorem sub_586_518 : Law586.Subspectral Law518 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_586, spectrum_eq_of_isDual dual_518]
  exact sub_3170_3169

theorem sub_590_539 : Law590.Subspectral Law539 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_590, spectrum_eq_of_isDual dual_539]
  exact sub_3129_3107

theorem sub_592_486 : Law592.Subspectral Law486 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_592, spectrum_eq_of_isDual dual_486]
  exact sub_3138_3125

theorem sub_595_533 : Law595.Subspectral Law533 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_595, spectrum_eq_of_isDual dual_533]
  exact sub_3234_3233

theorem sub_596_567 : Law596.Subspectral Law567 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_596, spectrum_eq_of_isDual dual_567]
  exact sub_3207_3206

theorem sub_601_526 : Law601.Subspectral Law526 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_601, spectrum_eq_of_isDual dual_526]
  exact sub_3204_3203

theorem sub_604_529 : Law604.Subspectral Law529 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_604, spectrum_eq_of_isDual dual_529]
  exact sub_3223_3215

theorem sub_605_529 : Law605.Subspectral Law529 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_605, spectrum_eq_of_isDual dual_529]
  exact sub_3217_3215

theorem sub_606_530 : Law606.Subspectral Law530 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_606, spectrum_eq_of_isDual dual_530]
  exact sub_3158_3157

theorem sub_607_494 : Law607.Subspectral Law494 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_607, spectrum_eq_of_isDual dual_494]
  exact sub_3226_3213

theorem sub_610_590 : Law610.Subspectral Law590 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_610, spectrum_eq_of_isDual dual_590]
  exact sub_3236_3129

theorem sub_611_534 : Law611.Subspectral Law534 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_611, spectrum_eq_of_isDual dual_534]
  exact sub_3209_3208

theorem sub_668_2108 : Law668.Subspectral Law2108 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_668, spectrum_eq_of_isDual dual_2108]
  exact sub_2901_1499

theorem sub_674_689 : Law674.Subspectral Law689 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_674, spectrum_eq_of_isDual dual_689]
  exact sub_2938_2922

theorem sub_675_674 : Law675.Subspectral Law674 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_675, spectrum_eq_of_isDual dual_674]
  exact sub_2976_2938

theorem sub_678_2717 : Law678.Subspectral Law2717 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_678, spectrum_eq_of_isDual dual_2717]
  exact sub_2921_890

theorem sub_681_3124 : Law681.Subspectral Law3124 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_681, spectrum_eq_of_isDual dual_3124]
  exact sub_3009_475

theorem sub_683_1942 : Law683.Subspectral Law1942 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_683, spectrum_eq_of_isDual dual_1942]
  exact sub_2991_1706

theorem sub_685_555 : Law685.Subspectral Law555 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_685, spectrum_eq_of_isDual dual_555]
  exact sub_3027_3119

theorem sub_687_995 : Law687.Subspectral Law995 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_687, spectrum_eq_of_isDual dual_995]
  exact sub_2920_2729

theorem sub_695_1993 : Law695.Subspectral Law1993 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_695, spectrum_eq_of_isDual dual_1993]
  exact sub_3008_1710

theorem sub_700_688 : Law700.Subspectral Law688 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_700, spectrum_eq_of_isDual dual_688]
  exact sub_2993_2911

theorem sub_701_674 : Law701.Subspectral Law674 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_701, spectrum_eq_of_isDual dual_674]
  exact sub_2959_2938

theorem sub_702_700 : Law702.Subspectral Law700 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_702, spectrum_eq_of_isDual dual_700]
  exact sub_3028_2993

theorem sub_708_2418 : Law708.Subspectral Law2418 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_708, spectrum_eq_of_isDual dual_2418]
  exact sub_2983_1294

theorem sub_715_2 : Law715.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_715, spectrum_eq_of_isDual dual_2]
  exact sub_2929_2

theorem sub_736_95 : Law736.Subspectral Law95 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_736, spectrum_eq_of_isDual dual_95]
  exact sub_3030_303

theorem sub_737_720 : Law737.Subspectral Law720 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_737, spectrum_eq_of_isDual dual_720]
  exact sub_3005_2995

theorem sub_741_3213 : Law741.Subspectral Law3213 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_741, spectrum_eq_of_isDual dual_3213]
  exact sub_2906_494

theorem sub_742_15 : Law742.Subspectral Law15 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_742, spectrum_eq_of_isDual dual_15]
  exact sub_2904_30

theorem sub_743_552 : Law743.Subspectral Law552 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_743, spectrum_eq_of_isDual dual_552]
  exact sub_2908_3148

theorem sub_745_484 : Law745.Subspectral Law484 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_745, spectrum_eq_of_isDual dual_484]
  exact sub_2943_3123

theorem sub_747_544 : Law747.Subspectral Law544 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_747, spectrum_eq_of_isDual dual_544]
  exact sub_2987_3190

theorem sub_754_710 : Law754.Subspectral Law710 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_754, spectrum_eq_of_isDual dual_710]
  exact sub_2980_2978

theorem sub_756_712 : Law756.Subspectral Law712 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_756, spectrum_eq_of_isDual dual_712]
  exact sub_2989_2988

theorem sub_758_1714 : Law758.Subspectral Law1714 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_758, spectrum_eq_of_isDual dual_1714]
  exact sub_2916_2010

theorem sub_760_557 : Law760.Subspectral Law557 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_760, spectrum_eq_of_isDual dual_557]
  exact sub_2933_3136

theorem sub_762_717 : Law762.Subspectral Law717 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_762, spectrum_eq_of_isDual dual_717]
  exact sub_2953_2950

theorem sub_766_717 : Law766.Subspectral Law717 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_766, spectrum_eq_of_isDual dual_717]
  exact sub_2999_2950

theorem sub_767_717 : Law767.Subspectral Law717 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_767, spectrum_eq_of_isDual dual_717]
  exact sub_2962_2950

theorem sub_768_730 : Law768.Subspectral Law730 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_768, spectrum_eq_of_isDual dual_730]
  exact sub_3037_3036

theorem sub_770_720 : Law770.Subspectral Law720 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_770, spectrum_eq_of_isDual dual_720]
  exact sub_3003_2995

theorem sub_777_715 : Law777.Subspectral Law715 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_777, spectrum_eq_of_isDual dual_715]
  exact sub_2930_2929

theorem sub_779_717 : Law779.Subspectral Law717 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_779, spectrum_eq_of_isDual dual_717]
  exact sub_2965_2950

theorem sub_780_720 : Law780.Subspectral Law720 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_780, spectrum_eq_of_isDual dual_720]
  exact sub_2996_2995

theorem sub_781_718 : Law781.Subspectral Law718 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_781, spectrum_eq_of_isDual dual_718]
  exact sub_3041_3017

theorem sub_784_717 : Law784.Subspectral Law717 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_784, spectrum_eq_of_isDual dual_717]
  exact sub_2951_2950

theorem sub_785_718 : Law785.Subspectral Law718 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_785, spectrum_eq_of_isDual dual_718]
  exact sub_3018_3017

theorem sub_787_89 : Law787.Subspectral Law89 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_787, spectrum_eq_of_isDual dual_89]
  exact sub_3040_304

theorem sub_788_720 : Law788.Subspectral Law720 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_788, spectrum_eq_of_isDual dual_720]
  exact sub_2997_2995

theorem sub_789_721 : Law789.Subspectral Law721 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_789, spectrum_eq_of_isDual dual_721]
  exact sub_2967_2966

theorem sub_794_688 : Law794.Subspectral Law688 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_794, spectrum_eq_of_isDual dual_688]
  exact sub_2918_2911

theorem sub_795_777 : Law795.Subspectral Law777 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_795, spectrum_eq_of_isDual dual_777]
  exact sub_2935_2930

theorem sub_797_789 : Law797.Subspectral Law789 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_797, spectrum_eq_of_isDual dual_789]
  exact sub_2969_2967

theorem sub_798_736 : Law798.Subspectral Law736 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_798, spectrum_eq_of_isDual dual_736]
  exact sub_3031_3030

theorem sub_799_770 : Law799.Subspectral Law770 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_799, spectrum_eq_of_isDual dual_770]
  exact sub_3004_3003

theorem sub_802_813 : Law802.Subspectral Law813 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_802, spectrum_eq_of_isDual dual_813]
  exact sub_3035_3033

theorem sub_803_728 : Law803.Subspectral Law728 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_803, spectrum_eq_of_isDual dual_728]
  exact sub_2963_2961

theorem sub_804_729 : Law804.Subspectral Law729 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_804, spectrum_eq_of_isDual dual_729]
  exact sub_3001_3000

theorem sub_805_730 : Law805.Subspectral Law730 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_805, spectrum_eq_of_isDual dual_730]
  exact sub_3038_3036

theorem sub_807_732 : Law807.Subspectral Law732 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_807, spectrum_eq_of_isDual dual_732]
  exact sub_3020_3012

theorem sub_808_732 : Law808.Subspectral Law732 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_808, spectrum_eq_of_isDual dual_732]
  exact sub_3014_3012

theorem sub_809_696 : Law809.Subspectral Law696 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_809, spectrum_eq_of_isDual dual_696]
  exact sub_2955_2948

theorem sub_812_787 : Law812.Subspectral Law787 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_812, spectrum_eq_of_isDual dual_787]
  exact sub_3045_3040

theorem sub_814_737 : Law814.Subspectral Law737 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_814, spectrum_eq_of_isDual dual_737]
  exact sub_3006_3005

theorem sub_815_809 : Law815.Subspectral Law809 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_815, spectrum_eq_of_isDual dual_809]
  exact sub_2972_2955

theorem sub_816_790 : Law816.Subspectral Law790 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_816, spectrum_eq_of_isDual dual_790]
  exact sub_3049_3043

theorem sub_871_2 : Law871.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_871, spectrum_eq_of_isDual dual_2]
  exact sub_2698_2

theorem sub_881_2 : Law881.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_881, spectrum_eq_of_isDual dual_2]
  exact sub_2718_2

theorem sub_884_2295 : Law884.Subspectral Law2295 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_884, spectrum_eq_of_isDual dual_2295]
  exact sub_2806_1351

theorem sub_886_3109 : Law886.Subspectral Law3109 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_886, spectrum_eq_of_isDual dual_3109]
  exact sub_2788_538

theorem sub_887_1384 : Law887.Subspectral Law1384 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_887, spectrum_eq_of_isDual dual_1384]
  exact sub_2755_2319

theorem sub_887_1537 : Law887.Subspectral Law1537 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_887, spectrum_eq_of_isDual dual_1537]
  exact sub_2755_2105

theorem sub_887_2105 : Law887.Subspectral Law2105 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_887, spectrum_eq_of_isDual dual_2105]
  exact sub_2755_1537

theorem sub_890_2911 : Law890.Subspectral Law2911 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_890, spectrum_eq_of_isDual dual_2911]
  exact sub_2717_688

theorem sub_891_2 : Law891.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_891, spectrum_eq_of_isDual dual_2]
  exact sub_2708_2

theorem sub_892_881 : Law892.Subspectral Law881 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_892, spectrum_eq_of_isDual dual_881]
  exact sub_2719_2718

theorem sub_904_894 : Law904.Subspectral Law894 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_904, spectrum_eq_of_isDual dual_894]
  exact sub_2756_2754

theorem sub_905_903 : Law905.Subspectral Law903 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_905, spectrum_eq_of_isDual dual_903]
  exact sub_2825_2790

theorem sub_908_291 : Law908.Subspectral Law291 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_908, spectrum_eq_of_isDual dual_291]
  exact sub_2704_69

theorem sub_911_2 : Law911.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_911, spectrum_eq_of_isDual dual_2]
  exact sub_2780_2

theorem sub_913_1292 : Law913.Subspectral Law1292 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_913, spectrum_eq_of_isDual dual_1292]
  exact sub_2775_2382

theorem sub_915_911 : Law915.Subspectral Law911 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_915, spectrum_eq_of_isDual dual_911]
  exact sub_2785_2780

theorem sub_921_986 : Law921.Subspectral Law986 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_921, spectrum_eq_of_isDual dual_986]
  exact sub_2814_2813

theorem sub_929_918 : Law929.Subspectral Law918 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_929, spectrum_eq_of_isDual dual_918]
  exact sub_2731_2726

theorem sub_931_1012 : Law931.Subspectral Law1012 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_931, spectrum_eq_of_isDual dual_1012]
  exact sub_2758_2752

theorem sub_944_173 : Law944.Subspectral Law173 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_944, spectrum_eq_of_isDual dual_173]
  exact sub_2703_187

theorem sub_945_2976 : Law945.Subspectral Law2976 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_945, spectrum_eq_of_isDual dual_2976]
  exact sub_2701_675

theorem sub_946_871 : Law946.Subspectral Law871 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_946, spectrum_eq_of_isDual dual_871]
  exact sub_2705_2698

theorem sub_948_2 : Law948.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_948, spectrum_eq_of_isDual dual_2]
  exact sub_2740_2

theorem sub_949_546 : Law949.Subspectral Law546 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_949, spectrum_eq_of_isDual dual_546]
  exact sub_2776_3185

theorem sub_962_1790 : Law962.Subspectral Law1790 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_962, spectrum_eq_of_isDual dual_1790]
  exact sub_2722_1913

theorem sub_963_918 : Law963.Subspectral Law918 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_963, spectrum_eq_of_isDual dual_918]
  exact sub_2730_2726

theorem sub_967_966 : Law967.Subspectral Law966 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_967, spectrum_eq_of_isDual dual_966]
  exact sub_2818_2810

theorem sub_975_970 : Law975.Subspectral Law970 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_975, spectrum_eq_of_isDual dual_970]
  exact sub_2767_2759

theorem sub_979_15 : Law979.Subspectral Law15 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_979, spectrum_eq_of_isDual dual_15]
  exact sub_2711_30

theorem sub_980_918 : Law980.Subspectral Law918 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_980, spectrum_eq_of_isDual dual_918]
  exact sub_2727_2726

theorem sub_982_1006 : Law982.Subspectral Law1006 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_982, spectrum_eq_of_isDual dual_1006]
  exact sub_2762_2760

theorem sub_986_1011 : Law986.Subspectral Law1011 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_986, spectrum_eq_of_isDual dual_1011]
  exact sub_2813_2811

theorem sub_991_983 : Law991.Subspectral Law983 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_991, spectrum_eq_of_isDual dual_983]
  exact sub_2794_2793

theorem sub_993_990 : Law993.Subspectral Law990 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_993, spectrum_eq_of_isDual dual_990]
  exact sub_2840_2837

theorem sub_1001_966 : Law1001.Subspectral Law966 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1001, spectrum_eq_of_isDual dual_966]
  exact sub_2828_2810

theorem sub_1002_932 : Law1002.Subspectral Law932 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1002, spectrum_eq_of_isDual dual_932]
  exact sub_2801_2797

theorem sub_1008_971 : Law1008.Subspectral Law971 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1008, spectrum_eq_of_isDual dual_971]
  exact sub_2835_2834

theorem sub_1011_935 : Law1011.Subspectral Law935 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1011, spectrum_eq_of_isDual dual_935]
  exact sub_2811_2809

theorem sub_1012_936 : Law1012.Subspectral Law936 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1012, spectrum_eq_of_isDual dual_936]
  exact sub_2752_2751

theorem sub_1013_937 : Law1013.Subspectral Law937 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1013, spectrum_eq_of_isDual dual_937]
  exact sub_2820_2819

theorem sub_1015_1005 : Law1015.Subspectral Law1005 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1015, spectrum_eq_of_isDual dual_1005]
  exact sub_2842_2832

theorem sub_1016_939 : Law1016.Subspectral Law939 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1016, spectrum_eq_of_isDual dual_939]
  exact sub_2830_2827

theorem sub_1017_940 : Law1017.Subspectral Law940 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1017, spectrum_eq_of_isDual dual_940]
  exact sub_2803_2802

theorem sub_1018_941 : Law1018.Subspectral Law941 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1018, spectrum_eq_of_isDual dual_941]
  exact sub_2769_2768

theorem sub_1019_942 : Law1019.Subspectral Law942 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1019, spectrum_eq_of_isDual dual_942]
  exact sub_2846_2845

theorem sub_1077_119 : Law1077.Subspectral Law119 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1077, spectrum_eq_of_isDual dual_119]
  exact sub_2569_240

theorem sub_1087_1114 : Law1087.Subspectral Law1114 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1087, spectrum_eq_of_isDual dual_1114]
  exact sub_2603_2577

theorem sub_1091_1084 : Law1091.Subspectral Law1084 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1091, spectrum_eq_of_isDual dual_1084]
  exact sub_2621_2515

theorem sub_1098_1913 : Law1098.Subspectral Law1913 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1098, spectrum_eq_of_isDual dual_1913]
  exact sub_2586_1790

theorem sub_1102_15 : Law1102.Subspectral Law15 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1102, spectrum_eq_of_isDual dual_15]
  exact sub_2542_30

theorem sub_1103_1087 : Law1103.Subspectral Law1087 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1103, spectrum_eq_of_isDual dual_1087]
  exact sub_2604_2603

theorem sub_1105_1079 : Law1105.Subspectral Law1079 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1105, spectrum_eq_of_isDual dual_1079]
  exact sub_2619_2568

theorem sub_1107_1097 : Law1107.Subspectral Law1097 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1107, spectrum_eq_of_isDual dual_1097]
  exact sub_2553_2551

theorem sub_1108_1081 : Law1108.Subspectral Law1081 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1108, spectrum_eq_of_isDual dual_1081]
  exact sub_2622_2570

theorem sub_1118_1111 : Law1118.Subspectral Law1111 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1118, spectrum_eq_of_isDual dual_1111]
  exact sub_2582_2501

theorem sub_1128_1124 : Law1128.Subspectral Law1124 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1128, spectrum_eq_of_isDual dual_1124]
  exact sub_2636_2611

theorem sub_1131_556 : Law1131.Subspectral Law556 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1131, spectrum_eq_of_isDual dual_556]
  exact sub_2511_3128

theorem sub_1136_1124 : Law1136.Subspectral Law1124 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1136, spectrum_eq_of_isDual dual_1124]
  exact sub_2630_2611

theorem sub_1140_1124 : Law1140.Subspectral Law1124 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1140, spectrum_eq_of_isDual dual_1124]
  exact sub_2616_2611

theorem sub_1147_69 : Law1147.Subspectral Law69 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1147, spectrum_eq_of_isDual dual_69]
  exact sub_2500_291

theorem sub_1148_1385 : Law1148.Subspectral Law1385 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1148, spectrum_eq_of_isDual dual_1385]
  exact sub_2498_2305

theorem sub_1149_1074 : Law1149.Subspectral Law1074 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1149, spectrum_eq_of_isDual dual_1074]
  exact sub_2502_2495

theorem sub_1156_15 : Law1156.Subspectral Law15 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1156, spectrum_eq_of_isDual dual_15]
  exact sub_2535_30

theorem sub_1161_1080 : Law1161.Subspectral Law1080 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1161, spectrum_eq_of_isDual dual_1080]
  exact sub_2539_2532

theorem sub_1164_2 : Law1164.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1164, spectrum_eq_of_isDual dual_2]
  exact sub_2510_2

theorem sub_1166_1084 : Law1166.Subspectral Law1084 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1166, spectrum_eq_of_isDual dual_1084]
  exact sub_2527_2515

theorem sub_1170_1124 : Law1170.Subspectral Law1124 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1170, spectrum_eq_of_isDual dual_1124]
  exact sub_2615_2611

theorem sub_1172_1123 : Law1172.Subspectral Law1123 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1172, spectrum_eq_of_isDual dual_1123]
  exact sub_2593_2544

theorem sub_1173_1123 : Law1173.Subspectral Law1123 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1173, spectrum_eq_of_isDual dual_1123]
  exact sub_2556_2544

theorem sub_1174_1124 : Law1174.Subspectral Law1124 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1174, spectrum_eq_of_isDual dual_1124]
  exact sub_2631_2611

theorem sub_1177_1204 : Law1177.Subspectral Law1204 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1177, spectrum_eq_of_isDual dual_1204]
  exact sub_2626_2625

theorem sub_1178_1127 : Law1178.Subspectral Law1127 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1178, spectrum_eq_of_isDual dual_1127]
  exact sub_2564_2560

theorem sub_1179_1128 : Law1179.Subspectral Law1128 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1179, spectrum_eq_of_isDual dual_1128]
  exact sub_2641_2636

theorem sub_1183_1074 : Law1183.Subspectral Law1074 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1183, spectrum_eq_of_isDual dual_1074]
  exact sub_2524_2495

theorem sub_1185_1123 : Law1185.Subspectral Law1123 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1185, spectrum_eq_of_isDual dual_1123]
  exact sub_2559_2544

theorem sub_1186_1123 : Law1186.Subspectral Law1123 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1186, spectrum_eq_of_isDual dual_1123]
  exact sub_2590_2544

theorem sub_1187_1124 : Law1187.Subspectral Law1124 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1187, spectrum_eq_of_isDual dual_1124]
  exact sub_2635_2611

theorem sub_1189_1123 : Law1189.Subspectral Law1123 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1189, spectrum_eq_of_isDual dual_1123]
  exact sub_2610_2544

theorem sub_1190_1123 : Law1190.Subspectral Law1123 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1190, spectrum_eq_of_isDual dual_1123]
  exact sub_2545_2544

theorem sub_1191_1124 : Law1191.Subspectral Law1124 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1191, spectrum_eq_of_isDual dual_1124]
  exact sub_2612_2611

theorem sub_1194_1126 : Law1194.Subspectral Law1126 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1194, spectrum_eq_of_isDual dual_1126]
  exact sub_2591_2589

theorem sub_1195_1127 : Law1195.Subspectral Law1127 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1195, spectrum_eq_of_isDual dual_1127]
  exact sub_2561_2560

theorem sub_1196_1128 : Law1196.Subspectral Law1128 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1196, spectrum_eq_of_isDual dual_1128]
  exact sub_2637_2636

theorem sub_1199_1130 : Law1199.Subspectral Law1130 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1199, spectrum_eq_of_isDual dual_1130]
  exact sub_2520_2518

theorem sub_1200_1094 : Law1200.Subspectral Law1094 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1200, spectrum_eq_of_isDual dual_1094]
  exact sub_2512_2505

theorem sub_1201_1095 : Law1201.Subspectral Law1095 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1201, spectrum_eq_of_isDual dual_1095]
  exact sub_2529_2516

theorem sub_1203_1195 : Law1203.Subspectral Law1195 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1203, spectrum_eq_of_isDual dual_1195]
  exact sub_2563_2561

theorem sub_1204_1142 : Law1204.Subspectral Law1142 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1204, spectrum_eq_of_isDual dual_1142]
  exact sub_2625_2624

theorem sub_1205_1135 : Law1205.Subspectral Law1135 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1205, spectrum_eq_of_isDual dual_1135]
  exact sub_2598_2594

theorem sub_1208_1219 : Law1208.Subspectral Law1219 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1208, spectrum_eq_of_isDual dual_1219]
  exact sub_2629_2627

theorem sub_1209_1134 : Law1209.Subspectral Law1134 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1209, spectrum_eq_of_isDual dual_1134]
  exact sub_2557_2555

theorem sub_1210_1135 : Law1210.Subspectral Law1135 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1210, spectrum_eq_of_isDual dual_1135]
  exact sub_2595_2594

theorem sub_1211_1136 : Law1211.Subspectral Law1136 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1211, spectrum_eq_of_isDual dual_1136]
  exact sub_2632_2630

theorem sub_1213_1191 : Law1213.Subspectral Law1191 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1213, spectrum_eq_of_isDual dual_1191]
  exact sub_2614_2612

theorem sub_1214_1138 : Law1214.Subspectral Law1138 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1214, spectrum_eq_of_isDual dual_1138]
  exact sub_2608_2606

theorem sub_1215_1139 : Law1215.Subspectral Law1139 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1215, spectrum_eq_of_isDual dual_1139]
  exact sub_2549_2548

theorem sub_1216_1140 : Law1216.Subspectral Law1140 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1216, spectrum_eq_of_isDual dual_1140]
  exact sub_2617_2616

theorem sub_1218_1196 : Law1218.Subspectral Law1196 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1218, spectrum_eq_of_isDual dual_1196]
  exact sub_2639_2637

theorem sub_1219_1142 : Law1219.Subspectral Law1142 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1219, spectrum_eq_of_isDual dual_1142]
  exact sub_2627_2624

theorem sub_1220_1143 : Law1220.Subspectral Law1143 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1220, spectrum_eq_of_isDual dual_1143]
  exact sub_2600_2599

theorem sub_1221_1144 : Law1221.Subspectral Law1144 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1221, spectrum_eq_of_isDual dual_1144]
  exact sub_2566_2565

theorem sub_1280_1087 : Law1280.Subspectral Law1087 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1280, spectrum_eq_of_isDual dual_1087]
  exact sub_2366_2603

theorem sub_1290_1087 : Law1290.Subspectral Law1087 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1290, spectrum_eq_of_isDual dual_1087]
  exact sub_2400_2603

theorem sub_1297_136 : Law1297.Subspectral Law136 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1297, spectrum_eq_of_isDual dual_136]
  exact sub_2302_223

theorem sub_1300_2 : Law1300.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1300, spectrum_eq_of_isDual dual_2]
  exact sub_2348_2

theorem sub_1301_556 : Law1301.Subspectral Law556 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1301, spectrum_eq_of_isDual dual_556]
  exact sub_2383_3128

theorem sub_1310_1300 : Law1310.Subspectral Law1300 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1310, spectrum_eq_of_isDual dual_1300]
  exact sub_2350_2348

theorem sub_1317_1087 : Law1317.Subspectral Law1087 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1317, spectrum_eq_of_isDual dual_1087]
  exact sub_2374_2603

theorem sub_1319_2 : Law1319.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1319, spectrum_eq_of_isDual dual_2]
  exact sub_2369_2

theorem sub_1324_1121 : Law1324.Subspectral Law1121 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1324, spectrum_eq_of_isDual dual_1121]
  exact sub_2320_2523

theorem sub_1326_2 : Law1326.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1326, spectrum_eq_of_isDual dual_2]
  exact sub_2341_2

theorem sub_1329_149 : Law1329.Subspectral Law149 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1329, spectrum_eq_of_isDual dual_149]
  exact sub_2386_237

theorem sub_1333_2 : Law1333.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1333, spectrum_eq_of_isDual dual_2]
  exact sub_2315_2

theorem sub_1351_1182 : Law1351.Subspectral Law1182 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1351, spectrum_eq_of_isDual dual_1182]
  exact sub_2295_2508

theorem sub_1352_1277 : Law1352.Subspectral Law1277 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1352, spectrum_eq_of_isDual dual_1277]
  exact sub_2299_2292

theorem sub_1354_2 : Law1354.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1354, spectrum_eq_of_isDual dual_2]
  exact sub_2334_2

theorem sub_1355_556 : Law1355.Subspectral Law556 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1355, spectrum_eq_of_isDual dual_556]
  exact sub_2370_3128

theorem sub_1363_1319 : Law1363.Subspectral Law1319 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1363, spectrum_eq_of_isDual dual_1319]
  exact sub_2371_2369

theorem sub_1364_1283 : Law1364.Subspectral Law1283 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1364, spectrum_eq_of_isDual dual_1283]
  exact sub_2336_2329

theorem sub_1369_1287 : Law1369.Subspectral Law1287 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1369, spectrum_eq_of_isDual dual_1287]
  exact sub_2324_2312

theorem sub_1371_2 : Law1371.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1371, spectrum_eq_of_isDual dual_2]
  exact sub_2344_2

theorem sub_1386_1277 : Law1386.Subspectral Law1277 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1386, spectrum_eq_of_isDual dual_1277]
  exact sub_2321_2292

theorem sub_1388_1412 : Law1388.Subspectral Law1412 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1388, spectrum_eq_of_isDual dual_1412]
  exact sub_2356_2354

theorem sub_1389_1329 : Law1389.Subspectral Law1329 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1389, spectrum_eq_of_isDual dual_1329]
  exact sub_2387_2386

theorem sub_1401_1333 : Law1401.Subspectral Law1333 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1401, spectrum_eq_of_isDual dual_1333]
  exact sub_2323_2315

theorem sub_1402_1385 : Law1402.Subspectral Law1385 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1402, spectrum_eq_of_isDual dual_1385]
  exact sub_2317_2305

theorem sub_1404_1298 : Law1404.Subspectral Law1298 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1404, spectrum_eq_of_isDual dual_1298]
  exact sub_2326_2313

theorem sub_1487_168 : Law1487.Subspectral Law168 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1487, spectrum_eq_of_isDual dual_168]
  exact sub_2164_168

theorem sub_1490_890 : Law1490.Subspectral Law890 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1490, spectrum_eq_of_isDual dual_890]
  exact sub_2109_2717

theorem sub_1493_2 : Law1493.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1493, spectrum_eq_of_isDual dual_2]
  exact sub_2197_2

theorem sub_1497_1493 : Law1497.Subspectral Law1493 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1497, spectrum_eq_of_isDual dual_1493]
  exact sub_2215_2197

theorem sub_1499_688 : Law1499.Subspectral Law688 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1499, spectrum_eq_of_isDual dual_688]
  exact sub_2108_2911

theorem sub_1501_1499 : Law1501.Subspectral Law1499 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1501, spectrum_eq_of_isDual dual_1499]
  exact sub_2110_2108

theorem sub_1508_2 : Law1508.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1508, spectrum_eq_of_isDual dual_2]
  exact sub_2136_2

theorem sub_1513_1503 : Law1513.Subspectral Law1503 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1513, spectrum_eq_of_isDual dual_1503]
  exact sub_2147_2145

theorem sub_1514_6 : Law1514.Subspectral Law6 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1514, spectrum_eq_of_isDual dual_6]
  exact sub_2216_6

theorem sub_1517_2 : Law1517.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1517, spectrum_eq_of_isDual dual_2]
  exact sub_2095_2

theorem sub_1524_1517 : Law1524.Subspectral Law1517 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1524, spectrum_eq_of_isDual dual_1517]
  exact sub_2176_2095

theorem sub_1536_2729 : Law1536.Subspectral Law2729 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1536, spectrum_eq_of_isDual dual_2729]
  exact sub_2112_995

theorem sub_1537_887 : Law1537.Subspectral Law887 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1537, spectrum_eq_of_isDual dual_887]
  exact sub_2105_2755

theorem sub_1542_1530 : Law1542.Subspectral Law1530 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1542, spectrum_eq_of_isDual dual_1530]
  exact sub_2224_2205

theorem sub_1546_1530 : Law1546.Subspectral Law1530 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1546, spectrum_eq_of_isDual dual_1530]
  exact sub_2210_2205

theorem sub_1548_1544 : Law1548.Subspectral Law1544 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1548, spectrum_eq_of_isDual dual_1544]
  exact sub_2218_2200

theorem sub_1549_1541 : Law1549.Subspectral Law1541 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1549, spectrum_eq_of_isDual dual_1541]
  exact sub_2193_2188

theorem sub_1550_1533 : Law1550.Subspectral Law1533 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1550, spectrum_eq_of_isDual dual_1533]
  exact sub_2159_2154

theorem sub_1553_2 : Law1553.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1553, spectrum_eq_of_isDual dual_2]
  exact sub_2094_2

theorem sub_1554_471 : Law1554.Subspectral Law471 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1554, spectrum_eq_of_isDual dual_471]
  exact sub_2092_3141

theorem sub_1557_2 : Law1557.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1557, spectrum_eq_of_isDual dual_2]
  exact sub_2131_2

theorem sub_1565_1522 : Law1565.Subspectral Law1522 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1565, spectrum_eq_of_isDual dual_1522]
  exact sub_2174_2166

theorem sub_1567_1557 : Law1567.Subspectral Law1557 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1567, spectrum_eq_of_isDual dual_1557]
  exact sub_2133_2131

theorem sub_1570_2 : Law1570.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1570, spectrum_eq_of_isDual dual_2]
  exact sub_2104_2

theorem sub_1571_2308 : Law1571.Subspectral Law2308 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1571, spectrum_eq_of_isDual dual_2308]
  exact sub_2113_1334

theorem sub_1572_1527 : Law1572.Subspectral Law1527 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1572, spectrum_eq_of_isDual dual_1527]
  exact sub_2121_2117

theorem sub_1574_1529 : Law1574.Subspectral Law1529 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1574, spectrum_eq_of_isDual dual_1529]
  exact sub_2141_2138

theorem sub_1575_1529 : Law1575.Subspectral Law1529 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1575, spectrum_eq_of_isDual dual_1529]
  exact sub_2201_2138

theorem sub_1576_1530 : Law1576.Subspectral Law1530 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1576, spectrum_eq_of_isDual dual_1530]
  exact sub_2209_2205

theorem sub_1579_1529 : Law1579.Subspectral Law1529 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1579, spectrum_eq_of_isDual dual_1529]
  exact sub_2150_2138

theorem sub_1580_1530 : Law1580.Subspectral Law1530 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1580, spectrum_eq_of_isDual dual_1530]
  exact sub_2225_2205

theorem sub_1582_1616 : Law1582.Subspectral Law1616 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1582, spectrum_eq_of_isDual dual_1616]
  exact sub_2191_2189

theorem sub_1584_1533 : Law1584.Subspectral Law1533 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1584, spectrum_eq_of_isDual dual_1533]
  exact sub_2158_2154

theorem sub_1589_1527 : Law1589.Subspectral Law1527 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1589, spectrum_eq_of_isDual dual_1527]
  exact sub_2118_2117

theorem sub_1591_1529 : Law1591.Subspectral Law1529 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1591, spectrum_eq_of_isDual dual_1529]
  exact sub_2153_2138

theorem sub_1592_1529 : Law1592.Subspectral Law1529 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1592, spectrum_eq_of_isDual dual_1529]
  exact sub_2184_2138

theorem sub_1593_1530 : Law1593.Subspectral Law1530 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1593, spectrum_eq_of_isDual dual_1530]
  exact sub_2229_2205

theorem sub_1597_1530 : Law1597.Subspectral Law1530 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1597, spectrum_eq_of_isDual dual_1530]
  exact sub_2206_2205

theorem sub_1599_1617 : Law1599.Subspectral Law1617 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1599, spectrum_eq_of_isDual dual_1617]
  exact sub_2228_2226

theorem sub_1600_1532 : Law1600.Subspectral Law1532 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1600, spectrum_eq_of_isDual dual_1532]
  exact sub_2185_2183

theorem sub_1601_1533 : Law1601.Subspectral Law1533 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1601, spectrum_eq_of_isDual dual_1533]
  exact sub_2155_2154

theorem sub_1602_1534 : Law1602.Subspectral Law1534 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1602, spectrum_eq_of_isDual dual_1534]
  exact sub_2231_2230

theorem sub_1605_1554 : Law1605.Subspectral Law1554 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1605, spectrum_eq_of_isDual dual_1554]
  exact sub_2114_2092

theorem sub_1607_1555 : Law1607.Subspectral Law1555 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1607, spectrum_eq_of_isDual dual_1555]
  exact sub_2123_2096

theorem sub_1609_1601 : Law1609.Subspectral Law1601 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1609, spectrum_eq_of_isDual dual_1601]
  exact sub_2157_2155

theorem sub_1611_1541 : Law1611.Subspectral Law1541 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1611, spectrum_eq_of_isDual dual_1541]
  exact sub_2192_2188

theorem sub_1615_1540 : Law1615.Subspectral Law1540 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1615, spectrum_eq_of_isDual dual_1540]
  exact sub_2151_2149

theorem sub_1616_1541 : Law1616.Subspectral Law1541 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1616, spectrum_eq_of_isDual dual_1541]
  exact sub_2189_2188

theorem sub_1617_1542 : Law1617.Subspectral Law1542 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1617, spectrum_eq_of_isDual dual_1542]
  exact sub_2226_2224

theorem sub_1619_1597 : Law1619.Subspectral Law1597 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1619, spectrum_eq_of_isDual dual_1597]
  exact sub_2208_2206

theorem sub_1620_1544 : Law1620.Subspectral Law1544 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1620, spectrum_eq_of_isDual dual_1544]
  exact sub_2202_2200

theorem sub_1621_1545 : Law1621.Subspectral Law1545 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1621, spectrum_eq_of_isDual dual_1545]
  exact sub_2143_2142

theorem sub_1625_1548 : Law1625.Subspectral Law1548 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1625, spectrum_eq_of_isDual dual_1548]
  exact sub_2221_2218

theorem sub_1626_1600 : Law1626.Subspectral Law1600 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1626, spectrum_eq_of_isDual dual_1600]
  exact sub_2194_2185

theorem sub_1683_1499 : Law1683.Subspectral Law1499 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1683, spectrum_eq_of_isDual dual_1499]
  exact sub_1886_2108

theorem sub_1686_2 : Law1686.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1686, spectrum_eq_of_isDual dual_2]
  exact sub_1960_2

theorem sub_1690_1686 : Law1690.Subspectral Law1686 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1690, spectrum_eq_of_isDual dual_1686]
  exact sub_1961_1960

theorem sub_1693_2 : Law1693.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1693, spectrum_eq_of_isDual dual_2]
  exact sub_1906_2

theorem sub_1696_689 : Law1696.Subspectral Law689 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1696, spectrum_eq_of_isDual dual_689]
  exact sub_1994_2922

theorem sub_1704_1693 : Law1704.Subspectral Law1693 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1704, spectrum_eq_of_isDual dual_1693]
  exact sub_1907_1906

theorem sub_1708_1696 : Law1708.Subspectral Law1696 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1708, spectrum_eq_of_isDual dual_1696]
  exact sub_2011_1994

theorem sub_1716_1711 : Law1716.Subspectral Law1711 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1716, spectrum_eq_of_isDual dual_1711]
  exact sub_1944_1933

theorem sub_1717_1690 : Law1717.Subspectral Law1690 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1717, spectrum_eq_of_isDual dual_1690]
  exact sub_2013_1961

theorem sub_1723_2 : Law1723.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1723, spectrum_eq_of_isDual dual_2]
  exact sub_1968_2

theorem sub_1730_2 : Law1730.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1730, spectrum_eq_of_isDual dual_2]
  exact sub_1914_2

theorem sub_1739_2 : Law1739.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1739, spectrum_eq_of_isDual dual_2]
  exact sub_1909_2

theorem sub_1741_1730 : Law1741.Subspectral Law1730 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1741, spectrum_eq_of_isDual dual_1730]
  exact sub_1919_1914

theorem sub_1743_2 : Law1743.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1743, spectrum_eq_of_isDual dual_2]
  exact sub_1946_2

theorem sub_1758_1720 : Law1758.Subspectral Law1720 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1758, spectrum_eq_of_isDual dual_1720]
  exact sub_1893_1892

theorem sub_1760_681 : Law1760.Subspectral Law681 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1760, spectrum_eq_of_isDual dual_681]
  exact sub_1928_3009

theorem sub_1762_1686 : Law1762.Subspectral Law1686 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1762, spectrum_eq_of_isDual dual_1686]
  exact sub_1972_1960

theorem sub_1764_1098 : Law1764.Subspectral Law1098 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1764, spectrum_eq_of_isDual dual_1098]
  exact sub_1967_2586

theorem sub_1765_187 : Law1765.Subspectral Law187 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1765, spectrum_eq_of_isDual dual_187]
  exact sub_1926_173

theorem sub_1766_1723 : Law1766.Subspectral Law1723 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1766, spectrum_eq_of_isDual dual_1723]
  exact sub_1969_1968

theorem sub_1769_1725 : Law1769.Subspectral Law1725 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1769, spectrum_eq_of_isDual dual_1725]
  exact sub_1965_1963

theorem sub_1777_2 : Law1777.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1777, spectrum_eq_of_isDual dual_2]
  exact sub_1938_2

theorem sub_1779_1778 : Law1779.Subspectral Law1778 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1779, spectrum_eq_of_isDual dual_1778]
  exact sub_2006_1998

theorem sub_1782_2 : Law1782.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1782, spectrum_eq_of_isDual dual_2]
  exact sub_1947_2

theorem sub_1786_1778 : Law1786.Subspectral Law1778 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1786, spectrum_eq_of_isDual dual_1778]
  exact sub_2017_1998

theorem sub_1790_949 : Law1790.Subspectral Law949 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1790, spectrum_eq_of_isDual dual_949]
  exact sub_1913_2776

theorem sub_1792_1730 : Law1792.Subspectral Law1730 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1792, spectrum_eq_of_isDual dual_1730]
  exact sub_1915_1914

theorem sub_1795_1735 : Law1795.Subspectral Law1735 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1795, spectrum_eq_of_isDual dual_1735]
  exact sub_1981_1980

theorem sub_1798_193 : Law1798.Subspectral Law193 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1798, spectrum_eq_of_isDual dual_193]
  exact sub_2001_200

theorem sub_1799_2 : Law1799.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1799, spectrum_eq_of_isDual dual_2]
  exact sub_1936_2

theorem sub_1800_1733 : Law1800.Subspectral Law1733 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1800, spectrum_eq_of_isDual dual_1733]
  exact sub_2003_2002

theorem sub_1803_1795 : Law1803.Subspectral Law1795 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1803, spectrum_eq_of_isDual dual_1795]
  exact sub_1982_1981

theorem sub_1804_1736 : Law1804.Subspectral Law1736 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1804, spectrum_eq_of_isDual dual_1736]
  exact sub_1952_1951

theorem sub_1805_1737 : Law1805.Subspectral Law1737 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1805, spectrum_eq_of_isDual dual_1737]
  exact sub_2028_2027

theorem sub_1807_1739 : Law1807.Subspectral Law1739 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1807, spectrum_eq_of_isDual dual_1739]
  exact sub_1917_1909

theorem sub_1808_1739 : Law1808.Subspectral Law1739 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1808, spectrum_eq_of_isDual dual_1739]
  exact sub_1911_1909

theorem sub_1810_1775 : Law1810.Subspectral Law1775 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1810, spectrum_eq_of_isDual dual_1775]
  exact sub_1920_1918

theorem sub_1813_1778 : Law1813.Subspectral Law1778 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1813, spectrum_eq_of_isDual dual_1778]
  exact sub_2016_1998

theorem sub_1814_1785 : Law1814.Subspectral Law1785 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1814, spectrum_eq_of_isDual dual_1785]
  exact sub_1989_1988

theorem sub_1818_1743 : Law1818.Subspectral Law1743 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1818, spectrum_eq_of_isDual dual_1743]
  exact sub_1948_1946

theorem sub_1824_1748 : Law1824.Subspectral Law1748 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1824, spectrum_eq_of_isDual dual_1748]
  exact sub_1940_1939

theorem sub_1828_1751 : Law1828.Subspectral Law1751 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1828, spectrum_eq_of_isDual dual_1751]
  exact sub_2018_2015

theorem sub_1829_1752 : Law1829.Subspectral Law1752 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1829, spectrum_eq_of_isDual dual_1752]
  exact sub_1991_1990

theorem sub_1830_1753 : Law1830.Subspectral Law1753 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1830, spectrum_eq_of_isDual dual_1753]
  exact sub_1957_1956

theorem sub_1831_1754 : Law1831.Subspectral Law1754 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1831, spectrum_eq_of_isDual dual_1754]
  exact sub_2034_2033

theorem sub_1889_2 : Law1889.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1889, spectrum_eq_of_isDual dual_2]
  exact sub_1757_2

theorem sub_1891_2 : Law1891.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1891, spectrum_eq_of_isDual dual_2]
  exact sub_1756_2

theorem sub_1892_2 : Law1892.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1892, spectrum_eq_of_isDual dual_2]
  exact sub_1720_2

theorem sub_1896_2918 : Law1896.Subspectral Law2918 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1896, spectrum_eq_of_isDual dual_2918]
  exact sub_1703_794

theorem sub_1901_2 : Law1901.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1901, spectrum_eq_of_isDual dual_2]
  exact sub_1773_2

theorem sub_1903_1901 : Law1903.Subspectral Law1901 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1903, spectrum_eq_of_isDual dual_1901]
  exact sub_1809_1773

theorem sub_1911_1889 : Law1911.Subspectral Law1889 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1911, spectrum_eq_of_isDual dual_1889]
  exact sub_1808_1757

theorem sub_1917_1891 : Law1917.Subspectral Law1891 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1917, spectrum_eq_of_isDual dual_1891]
  exact sub_1807_1756

theorem sub_1918_1906 : Law1918.Subspectral Law1906 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1918, spectrum_eq_of_isDual dual_1906]
  exact sub_1775_1693

theorem sub_1923_2 : Law1923.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1923, spectrum_eq_of_isDual dual_2]
  exact sub_1689_2

theorem sub_1930_1923 : Law1930.Subspectral Law1923 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1930, spectrum_eq_of_isDual dual_1923]
  exact sub_1770_1689

theorem sub_1933_2 : Law1933.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1933, spectrum_eq_of_isDual dual_2]
  exact sub_1711_2

theorem sub_1935_2 : Law1935.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1935, spectrum_eq_of_isDual dual_2]
  exact sub_1732_2

theorem sub_1939_2 : Law1939.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1939, spectrum_eq_of_isDual dual_2]
  exact sub_1748_2

theorem sub_1942_2717 : Law1942.Subspectral Law2717 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1942, spectrum_eq_of_isDual dual_2717]
  exact sub_1706_890

theorem sub_1951_2 : Law1951.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1951, spectrum_eq_of_isDual dual_2]
  exact sub_1736_2

theorem sub_1954_1928 : Law1954.Subspectral Law1928 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1954, spectrum_eq_of_isDual dual_1928]
  exact sub_1812_1760

theorem sub_1955_1947 : Law1955.Subspectral Law1947 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1955, spectrum_eq_of_isDual dual_1947]
  exact sub_1787_1782

theorem sub_1956_2 : Law1956.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1956, spectrum_eq_of_isDual dual_2]
  exact sub_1753_2

theorem sub_1959_884 : Law1959.Subspectral Law884 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1959, spectrum_eq_of_isDual dual_884]
  exact sub_1688_2806

theorem sub_1963_2 : Law1963.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1963, spectrum_eq_of_isDual dual_2]
  exact sub_1725_2

theorem sub_1965_1889 : Law1965.Subspectral Law1889 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1965, spectrum_eq_of_isDual dual_1889]
  exact sub_1769_1757

theorem sub_1967_546 : Law1967.Subspectral Law546 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1967, spectrum_eq_of_isDual dual_546]
  exact sub_1764_3185

theorem sub_1971_1891 : Law1971.Subspectral Law1891 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1971, spectrum_eq_of_isDual dual_1891]
  exact sub_1768_1756

theorem sub_1973_1892 : Law1973.Subspectral Law1892 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1973, spectrum_eq_of_isDual dual_1892]
  exact sub_1727_1720

theorem sub_1976_3119 : Law1976.Subspectral Law3119 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1976, spectrum_eq_of_isDual dual_3119]
  exact sub_1698_555

theorem sub_1978_1933 : Law1978.Subspectral Law1933 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1978, spectrum_eq_of_isDual dual_1933]
  exact sub_1715_1711

theorem sub_1980_1935 : Law1980.Subspectral Law1935 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1980, spectrum_eq_of_isDual dual_1935]
  exact sub_1735_1732

theorem sub_1984_2006 : Law1984.Subspectral Law2006 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1984, spectrum_eq_of_isDual dual_2006]
  exact sub_1781_1779

theorem sub_1985_2 : Law1985.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1985, spectrum_eq_of_isDual dual_2]
  exact sub_1744_2

theorem sub_1986_1948 : Law1986.Subspectral Law1948 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1986, spectrum_eq_of_isDual dual_1948]
  exact sub_1819_1818

theorem sub_1988_1901 : Law1988.Subspectral Law1901 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1988, spectrum_eq_of_isDual dual_1901]
  exact sub_1785_1773

theorem sub_1990_2 : Law1990.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1990, spectrum_eq_of_isDual dual_2]
  exact sub_1752_2

theorem sub_1995_1933 : Law1995.Subspectral Law1933 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1995, spectrum_eq_of_isDual dual_1933]
  exact sub_1712_1711

theorem sub_1997_2021 : Law1997.Subspectral Law2021 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1997, spectrum_eq_of_isDual dual_2021]
  exact sub_1747_1745

theorem sub_1998_2 : Law1998.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1998, spectrum_eq_of_isDual dual_2]
  exact sub_1778_2

theorem sub_1999_1889 : Law1999.Subspectral Law1889 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_1999, spectrum_eq_of_isDual dual_1889]
  exact sub_1823_1757

theorem sub_2002_2 : Law2002.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2002, spectrum_eq_of_isDual dual_2]
  exact sub_1733_2

theorem sub_2003_1936 : Law2003.Subspectral Law1936 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2003, spectrum_eq_of_isDual dual_1936]
  exact sub_1800_1799

theorem sub_2005_2023 : Law2005.Subspectral Law2023 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2005, spectrum_eq_of_isDual dual_2023]
  exact sub_1822_1820

theorem sub_2007_1939 : Law2007.Subspectral Law1939 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2007, spectrum_eq_of_isDual dual_1939]
  exact sub_1749_1748

theorem sub_2008_1999 : Law2008.Subspectral Law1999 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2008, spectrum_eq_of_isDual dual_1999]
  exact sub_1825_1823

theorem sub_2012_1994 : Law2012.Subspectral Law1994 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2012, spectrum_eq_of_isDual dual_1994]
  exact sub_1700_1696

theorem sub_2015_1909 : Law2015.Subspectral Law1909 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2015, spectrum_eq_of_isDual dual_1909]
  exact sub_1751_1739

theorem sub_2017_1947 : Law2017.Subspectral Law1947 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2017, spectrum_eq_of_isDual dual_1947]
  exact sub_1786_1782

theorem sub_2020_2031 : Law2020.Subspectral Law2031 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2020, spectrum_eq_of_isDual dual_2031]
  exact sub_1817_1815

theorem sub_2021_1985 : Law2021.Subspectral Law1985 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2021, spectrum_eq_of_isDual dual_1985]
  exact sub_1745_1744

theorem sub_2022_1906 : Law2022.Subspectral Law1906 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2022, spectrum_eq_of_isDual dual_1906]
  exact sub_1783_1693

theorem sub_2023_1907 : Law2023.Subspectral Law1907 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2023, spectrum_eq_of_isDual dual_1907]
  exact sub_1820_1704

theorem sub_2025_2003 : Law2025.Subspectral Law2003 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2025, spectrum_eq_of_isDual dual_2003]
  exact sub_1802_1800

theorem sub_2026_1981 : Law2026.Subspectral Law1981 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2026, spectrum_eq_of_isDual dual_1981]
  exact sub_1796_1795

theorem sub_2027_1914 : Law2027.Subspectral Law1914 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2027, spectrum_eq_of_isDual dual_1914]
  exact sub_1737_1730

theorem sub_2028_1915 : Law2028.Subspectral Law1915 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2028, spectrum_eq_of_isDual dual_1915]
  exact sub_1805_1792

theorem sub_2030_2008 : Law2030.Subspectral Law2008 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2030, spectrum_eq_of_isDual dual_2008]
  exact sub_1827_1825

theorem sub_2031_2016 : Law2031.Subspectral Law2016 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2031, spectrum_eq_of_isDual dual_2016]
  exact sub_1815_1813

theorem sub_2032_1918 : Law2032.Subspectral Law1918 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2032, spectrum_eq_of_isDual dual_1918]
  exact sub_1788_1775

theorem sub_2033_1956 : Law2033.Subspectral Law1956 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2033, spectrum_eq_of_isDual dual_1956]
  exact sub_1754_1753

theorem sub_2096_2094 : Law2096.Subspectral Law2094 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2096, spectrum_eq_of_isDual dual_2094]
  exact sub_1555_1553

theorem sub_2099_3162 : Law2099.Subspectral Law3162 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2099, spectrum_eq_of_isDual dual_3162]
  exact sub_1500_498

theorem sub_2102_2 : Law2102.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2102, spectrum_eq_of_isDual dual_2]
  exact sub_1588_2

theorem sub_2106_1732 : Law2106.Subspectral Law1732 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2106, spectrum_eq_of_isDual dual_1732]
  exact sub_1606_1935

theorem sub_2109_2772 : Law2109.Subspectral Law2772 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2109, spectrum_eq_of_isDual dual_2772]
  exact sub_1490_874

theorem sub_2113_2308 : Law2113.Subspectral Law2308 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2113, spectrum_eq_of_isDual dual_2308]
  exact sub_1571_1334

theorem sub_2116_898 : Law2116.Subspectral Law898 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2116, spectrum_eq_of_isDual dual_898]
  exact sub_1587_2805

theorem sub_2117_2 : Law2117.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2117, spectrum_eq_of_isDual dual_2]
  exact sub_1527_2

theorem sub_2120_2094 : Law2120.Subspectral Law2094 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2120, spectrum_eq_of_isDual dual_2094]
  exact sub_1604_1553

theorem sub_2122_2112 : Law2122.Subspectral Law2112 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2122, spectrum_eq_of_isDual dual_2112]
  exact sub_1538_1536

theorem sub_2129_2 : Law2129.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2129, spectrum_eq_of_isDual dual_2]
  exact sub_1562_2

theorem sub_2133_2129 : Law2133.Subspectral Law2129 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2133, spectrum_eq_of_isDual dual_2129]
  exact sub_1567_1562

theorem sub_2138_254 : Law2138.Subspectral Law254 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2138, spectrum_eq_of_isDual dual_254]
  exact sub_1529_150

theorem sub_2139_2138 : Law2139.Subspectral Law2138 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2139, spectrum_eq_of_isDual dual_2138]
  exact sub_1596_1529

theorem sub_2142_2 : Law2142.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2142, spectrum_eq_of_isDual dual_2]
  exact sub_1545_2

theorem sub_2145_2 : Law2145.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2145, spectrum_eq_of_isDual dual_2]
  exact sub_1503_2

theorem sub_2147_2136 : Law2147.Subspectral Law2136 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2147, spectrum_eq_of_isDual dual_2136]
  exact sub_1513_1508

theorem sub_2149_2 : Law2149.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2149, spectrum_eq_of_isDual dual_2]
  exact sub_1540_2

theorem sub_2154_2 : Law2154.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2154, spectrum_eq_of_isDual dual_2]
  exact sub_1533_2

theorem sub_2168_2092 : Law2168.Subspectral Law2092 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2168, spectrum_eq_of_isDual dual_2092]
  exact sub_1566_1554

theorem sub_2171_2 : Law2171.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2171, spectrum_eq_of_isDual dual_2]
  exact sub_1520_2

theorem sub_2172_2129 : Law2172.Subspectral Law2129 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2172, spectrum_eq_of_isDual dual_2129]
  exact sub_1563_1562

theorem sub_2175_2131 : Law2175.Subspectral Law2131 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2175, spectrum_eq_of_isDual dual_2131]
  exact sub_1559_1557

theorem sub_2177_2133 : Law2177.Subspectral Law2133 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2177, spectrum_eq_of_isDual dual_2133]
  exact sub_1568_1567

theorem sub_2179_2 : Law2179.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2179, spectrum_eq_of_isDual dual_2]
  exact sub_1495_2

theorem sub_2181_2099 : Law2181.Subspectral Law2099 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2181, spectrum_eq_of_isDual dual_2099]
  exact sub_1512_1500

theorem sub_2183_2 : Law2183.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2183, spectrum_eq_of_isDual dual_2]
  exact sub_1532_2

theorem sub_2187_2209 : Law2187.Subspectral Law2209 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2187, spectrum_eq_of_isDual dual_2209]
  exact sub_1578_1576

theorem sub_2188_2 : Law2188.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2188, spectrum_eq_of_isDual dual_2]
  exact sub_1541_2

theorem sub_2198_2136 : Law2198.Subspectral Law2136 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2198, spectrum_eq_of_isDual dual_2136]
  exact sub_1509_1508

theorem sub_2200_2 : Law2200.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2200, spectrum_eq_of_isDual dual_2]
  exact sub_1544_2

theorem sub_2204_2229 : Law2204.Subspectral Law2229 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2204, spectrum_eq_of_isDual dual_2229]
  exact sub_1595_1593

theorem sub_2205_2 : Law2205.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2205, spectrum_eq_of_isDual dual_2]
  exact sub_1530_2

theorem sub_2210_2142 : Law2210.Subspectral Law2142 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2210, spectrum_eq_of_isDual dual_2142]
  exact sub_1546_1545

theorem sub_2211_2198 : Law2211.Subspectral Law2198 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2211, spectrum_eq_of_isDual dual_2198]
  exact sub_1622_1509

theorem sub_2213_2108 : Law2213.Subspectral Law2108 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2213, spectrum_eq_of_isDual dual_2108]
  exact sub_1511_1499

theorem sub_2214_2145 : Law2214.Subspectral Law2145 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2214, spectrum_eq_of_isDual dual_2145]
  exact sub_1505_1503

theorem sub_2215_2179 : Law2215.Subspectral Law2179 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2215, spectrum_eq_of_isDual dual_2179]
  exact sub_1497_1495

theorem sub_2219_2157 : Law2219.Subspectral Law2157 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2219, spectrum_eq_of_isDual dual_2157]
  exact sub_1610_1609

theorem sub_2220_2191 : Law2220.Subspectral Law2191 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2220, spectrum_eq_of_isDual dual_2191]
  exact sub_1583_1582

theorem sub_2223_2234 : Law2223.Subspectral Law2234 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2223, spectrum_eq_of_isDual dual_2234]
  exact sub_1614_1612

theorem sub_2224_2149 : Law2224.Subspectral Law2149 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2224, spectrum_eq_of_isDual dual_2149]
  exact sub_1542_1540

theorem sub_2226_2151 : Law2226.Subspectral Law2151 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2226, spectrum_eq_of_isDual dual_2151]
  exact sub_1617_1615

theorem sub_2230_2117 : Law2230.Subspectral Law2117 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2230, spectrum_eq_of_isDual dual_2117]
  exact sub_1534_1527

theorem sub_2231_2118 : Law2231.Subspectral Law2118 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2231, spectrum_eq_of_isDual dual_2118]
  exact sub_1602_1589

theorem sub_2233_2120 : Law2233.Subspectral Law2120 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2233, spectrum_eq_of_isDual dual_2120]
  exact sub_1624_1604

theorem sub_2234_2214 : Law2234.Subspectral Law2214 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2234, spectrum_eq_of_isDual dual_2214]
  exact sub_1612_1505

theorem sub_2235_2121 : Law2235.Subspectral Law2121 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2235, spectrum_eq_of_isDual dual_2121]
  exact sub_1585_1572

theorem sub_2236_2176 : Law2236.Subspectral Law2176 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2236, spectrum_eq_of_isDual dual_2176]
  exact sub_1551_1524

theorem sub_2237_2123 : Law2237.Subspectral Law2123 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2237, spectrum_eq_of_isDual dual_2123]
  exact sub_1628_1607

theorem sub_2292_2 : Law2292.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2292, spectrum_eq_of_isDual dual_2]
  exact sub_1277_2

theorem sub_2297_538 : Law2297.Subspectral Law538 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2297, spectrum_eq_of_isDual dual_538]
  exact sub_1350_3109

theorem sub_2298_2 : Law2298.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2298, spectrum_eq_of_isDual dual_2]
  exact sub_1314_2

theorem sub_2305_2 : Law2305.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2305, spectrum_eq_of_isDual dual_2]
  exact sub_1385_2

theorem sub_2307_2921 : Law2307.Subspectral Law2921 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2307, spectrum_eq_of_isDual dual_2921]
  exact sub_1367_678

theorem sub_2308_895 : Law2308.Subspectral Law895 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2308, spectrum_eq_of_isDual dual_895]
  exact sub_1334_2789

theorem sub_2311_668 : Law2311.Subspectral Law668 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2311, spectrum_eq_of_isDual dual_668]
  exact sub_1296_2901

theorem sub_2313_2292 : Law2313.Subspectral Law2292 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2313, spectrum_eq_of_isDual dual_2292]
  exact sub_1298_1277

theorem sub_2316_2116 : Law2316.Subspectral Law2116 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2316, spectrum_eq_of_isDual dual_2116]
  exact sub_1368_1587

theorem sub_2319_887 : Law2319.Subspectral Law887 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2319, spectrum_eq_of_isDual dual_887]
  exact sub_1384_2755

theorem sub_2325_2298 : Law2325.Subspectral Law2298 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2325, spectrum_eq_of_isDual dual_2298]
  exact sub_1335_1314

theorem sub_2326_2299 : Law2326.Subspectral Law2299 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2326, spectrum_eq_of_isDual dual_2299]
  exact sub_1404_1352

theorem sub_2329_2 : Law2329.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2329, spectrum_eq_of_isDual dual_2]
  exact sub_1283_2

theorem sub_2332_2 : Law2332.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2332, spectrum_eq_of_isDual dual_2]
  exact sub_1359_2

theorem sub_2339_2 : Law2339.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2339, spectrum_eq_of_isDual dual_2]
  exact sub_1305_2

theorem sub_2342_2 : Law2342.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2342, spectrum_eq_of_isDual dual_2]
  exact sub_1393_2

theorem sub_2345_2 : Law2345.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2345, spectrum_eq_of_isDual dual_2]
  exact sub_1342_2

theorem sub_2346_2 : Law2346.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2346, spectrum_eq_of_isDual dual_2]
  exact sub_1418_2

theorem sub_2350_2339 : Law2350.Subspectral Law2339 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2350, spectrum_eq_of_isDual dual_2339]
  exact sub_1310_1305

theorem sub_2352_2 : Law2352.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2352, spectrum_eq_of_isDual dual_2]
  exact sub_1337_2

theorem sub_2353_2 : Law2353.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2353, spectrum_eq_of_isDual dual_2]
  exact sub_1376_2

theorem sub_2354_2 : Law2354.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2354, spectrum_eq_of_isDual dual_2]
  exact sub_1412_2

theorem sub_2357_2 : Law2357.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2357, spectrum_eq_of_isDual dual_2]
  exact sub_1330_2

theorem sub_2358_2 : Law2358.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2358, spectrum_eq_of_isDual dual_2]
  exact sub_1398_2

theorem sub_2360_2 : Law2360.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2360, spectrum_eq_of_isDual dual_2]
  exact sub_1406_2

theorem sub_2361_2 : Law2361.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2361, spectrum_eq_of_isDual dual_2]
  exact sub_1381_2

theorem sub_2362_2 : Law2362.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2362, spectrum_eq_of_isDual dual_2]
  exact sub_1347_2

theorem sub_2363_2 : Law2363.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2363, spectrum_eq_of_isDual dual_2]
  exact sub_1424_2

theorem sub_2365_3127 : Law2365.Subspectral Law3127 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2365, spectrum_eq_of_isDual dual_3127]
  exact sub_1282_521

theorem sub_2367_2329 : Law2367.Subspectral Law2329 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2367, spectrum_eq_of_isDual dual_2329]
  exact sub_1284_1283

theorem sub_2371_2332 : Law2371.Subspectral Law2332 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2371, spectrum_eq_of_isDual dual_2332]
  exact sub_1363_1359

theorem sub_2375_2332 : Law2375.Subspectral Law2332 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2375, spectrum_eq_of_isDual dual_2332]
  exact sub_1360_1359

theorem sub_2377_2334 : Law2377.Subspectral Law2334 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2377, spectrum_eq_of_isDual dual_2334]
  exact sub_1362_1354

theorem sub_2378_2334 : Law2378.Subspectral Law2334 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2378, spectrum_eq_of_isDual dual_2334]
  exact sub_1356_1354

theorem sub_2379_2369 : Law2379.Subspectral Law2369 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2379, spectrum_eq_of_isDual dual_2369]
  exact sub_1321_1319

theorem sub_2380_2336 : Law2380.Subspectral Law2336 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2380, spectrum_eq_of_isDual dual_2336]
  exact sub_1365_1364

theorem sub_2382_1886 : Law2382.Subspectral Law1886 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2382, spectrum_eq_of_isDual dual_1886]
  exact sub_1292_1683

theorem sub_2383_1131 : Law2383.Subspectral Law1131 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2383, spectrum_eq_of_isDual dual_1131]
  exact sub_1301_2511

theorem sub_2384_2339 : Law2384.Subspectral Law2339 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2384, spectrum_eq_of_isDual dual_2339]
  exact sub_1309_1305

theorem sub_2388_2 : Law2388.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2388, spectrum_eq_of_isDual dual_2]
  exact sub_1397_2

theorem sub_2390_2 : Law2390.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2390, spectrum_eq_of_isDual dual_2]
  exact sub_1375_2

theorem sub_2391_2 : Law2391.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2391, spectrum_eq_of_isDual dual_2]
  exact sub_1338_2

theorem sub_2392_2 : Law2392.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2392, spectrum_eq_of_isDual dual_2]
  exact sub_1413_2

theorem sub_2394_2 : Law2394.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2394, spectrum_eq_of_isDual dual_2]
  exact sub_1379_2

theorem sub_2395_2 : Law2395.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2395, spectrum_eq_of_isDual dual_2]
  exact sub_1408_2

theorem sub_2396_2 : Law2396.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2396, spectrum_eq_of_isDual dual_2]
  exact sub_1346_2

theorem sub_2397_2 : Law2397.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2397, spectrum_eq_of_isDual dual_2]
  exact sub_1423_2

theorem sub_2401_2339 : Law2401.Subspectral Law2339 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2401, spectrum_eq_of_isDual dual_2339]
  exact sub_1306_1305

theorem sub_2403_2 : Law2403.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2403, spectrum_eq_of_isDual dual_2]
  exact sub_1341_2

theorem sub_2404_2 : Law2404.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2404, spectrum_eq_of_isDual dual_2]
  exact sub_1372_2

theorem sub_2405_2 : Law2405.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2405, spectrum_eq_of_isDual dual_2]
  exact sub_1417_2

theorem sub_2407_2 : Law2407.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2407, spectrum_eq_of_isDual dual_2]
  exact sub_1392_2

theorem sub_2408_2341 : Law2408.Subspectral Law2341 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2408, spectrum_eq_of_isDual dual_2341]
  exact sub_1327_1326

theorem sub_2409_2342 : Law2409.Subspectral Law2342 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2409, spectrum_eq_of_isDual dual_2342]
  exact sub_1394_1393

theorem sub_2411_2 : Law2411.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2411, spectrum_eq_of_isDual dual_2]
  exact sub_1416_2

theorem sub_2412_2344 : Law2412.Subspectral Law2344 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2412, spectrum_eq_of_isDual dual_2344]
  exact sub_1373_1371

theorem sub_2413_2345 : Law2413.Subspectral Law2345 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2413, spectrum_eq_of_isDual dual_2345]
  exact sub_1343_1342

theorem sub_2414_2346 : Law2414.Subspectral Law2346 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2414, spectrum_eq_of_isDual dual_2346]
  exact sub_1419_1418

theorem sub_2416_2348 : Law2416.Subspectral Law2348 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2416, spectrum_eq_of_isDual dual_2348]
  exact sub_1308_1300

theorem sub_2417_2348 : Law2417.Subspectral Law2348 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2417, spectrum_eq_of_isDual dual_2348]
  exact sub_1302_1300

theorem sub_2418_2312 : Law2418.Subspectral Law2312 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2418, spectrum_eq_of_isDual dual_2312]
  exact sub_1294_1287

theorem sub_2419_2350 : Law2419.Subspectral Law2350 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2419, spectrum_eq_of_isDual dual_2350]
  exact sub_1311_1310

theorem sub_2421_2 : Law2421.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2421, spectrum_eq_of_isDual dual_2]
  exact sub_1345_2

theorem sub_2422_2 : Law2422.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2422, spectrum_eq_of_isDual dual_2]
  exact sub_1407_2

theorem sub_2423_2 : Law2423.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2423, spectrum_eq_of_isDual dual_2]
  exact sub_1380_2

theorem sub_2424_2 : Law2424.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2424, spectrum_eq_of_isDual dual_2]
  exact sub_1422_2

theorem sub_2426_2 : Law2426.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2426, spectrum_eq_of_isDual dual_2]
  exact sub_1411_2

theorem sub_2427_2352 : Law2427.Subspectral Law2352 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2427, spectrum_eq_of_isDual dual_2352]
  exact sub_1339_1337

theorem sub_2428_2353 : Law2428.Subspectral Law2353 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2428, spectrum_eq_of_isDual dual_2353]
  exact sub_1377_1376

theorem sub_2429_2354 : Law2429.Subspectral Law2354 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2429, spectrum_eq_of_isDual dual_2354]
  exact sub_1414_1412

theorem sub_2431_2 : Law2431.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2431, spectrum_eq_of_isDual dual_2]
  exact sub_1396_2

theorem sub_2432_2 : Law2432.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2432, spectrum_eq_of_isDual dual_2]
  exact sub_1390_2

theorem sub_2433_2357 : Law2433.Subspectral Law2357 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2433, spectrum_eq_of_isDual dual_2357]
  exact sub_1331_1330

theorem sub_2434_2358 : Law2434.Subspectral Law2358 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2434, spectrum_eq_of_isDual dual_2358]
  exact sub_1399_1398

theorem sub_2436_2 : Law2436.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2436, spectrum_eq_of_isDual dual_2]
  exact sub_1421_2

theorem sub_2437_2360 : Law2437.Subspectral Law2360 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2437, spectrum_eq_of_isDual dual_2360]
  exact sub_1409_1406

theorem sub_2438_2361 : Law2438.Subspectral Law2361 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2438, spectrum_eq_of_isDual dual_2361]
  exact sub_1382_1381

theorem sub_2439_2362 : Law2439.Subspectral Law2362 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2439, spectrum_eq_of_isDual dual_2362]
  exact sub_1348_1347

theorem sub_2440_2363 : Law2440.Subspectral Law2363 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2440, spectrum_eq_of_isDual dual_2363]
  exact sub_1425_1424

theorem sub_2495_2 : Law2495.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2495, spectrum_eq_of_isDual dual_2]
  exact sub_1074_2

theorem sub_2501_2 : Law2501.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2501, spectrum_eq_of_isDual dual_2]
  exact sub_1111_2

theorem sub_2505_2 : Law2505.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2505, spectrum_eq_of_isDual dual_2]
  exact sub_1094_2

theorem sub_2508_2 : Law2508.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2508, spectrum_eq_of_isDual dual_2]
  exact sub_1182_2

theorem sub_2514_2 : Law2514.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2514, spectrum_eq_of_isDual dual_2]
  exact sub_1093_2

theorem sub_2515_2 : Law2515.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2515, spectrum_eq_of_isDual dual_2]
  exact sub_1084_2

theorem sub_2516_2495 : Law2516.Subspectral Law2495 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2516, spectrum_eq_of_isDual dual_2495]
  exact sub_1095_1074

theorem sub_2518_2 : Law2518.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2518, spectrum_eq_of_isDual dual_2]
  exact sub_1130_2

theorem sub_2523_2 : Law2523.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2523, spectrum_eq_of_isDual dual_2]
  exact sub_1121_2

theorem sub_2526_2500 : Law2526.Subspectral Law2500 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2526, spectrum_eq_of_isDual dual_2500]
  exact sub_1198_1147

theorem sub_2527_2510 : Law2527.Subspectral Law2510 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2527, spectrum_eq_of_isDual dual_2510]
  exact sub_1166_1164

theorem sub_2528_2501 : Law2528.Subspectral Law2501 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2528, spectrum_eq_of_isDual dual_2501]
  exact sub_1132_1111

theorem sub_2529_2502 : Law2529.Subspectral Law2502 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2529, spectrum_eq_of_isDual dual_2502]
  exact sub_1201_1149

theorem sub_2532_2 : Law2532.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2532, spectrum_eq_of_isDual dual_2]
  exact sub_1080_2

theorem sub_2537_2922 : Law2537.Subspectral Law2922 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2537, spectrum_eq_of_isDual dual_2922]
  exact sub_1151_689

theorem sub_2544_2 : Law2544.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2544, spectrum_eq_of_isDual dual_2]
  exact sub_1123_2

theorem sub_2547_2 : Law2547.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2547, spectrum_eq_of_isDual dual_2]
  exact sub_1168_2

theorem sub_2548_2 : Law2548.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2548, spectrum_eq_of_isDual dual_2]
  exact sub_1139_2

theorem sub_2551_2 : Law2551.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2551, spectrum_eq_of_isDual dual_2]
  exact sub_1097_2

theorem sub_2555_2 : Law2555.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2555, spectrum_eq_of_isDual dual_2]
  exact sub_1134_2

theorem sub_2560_2 : Law2560.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2560, spectrum_eq_of_isDual dual_2]
  exact sub_1127_2

theorem sub_2565_2 : Law2565.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2565, spectrum_eq_of_isDual dual_2]
  exact sub_1144_2

theorem sub_2568_2 : Law2568.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2568, spectrum_eq_of_isDual dual_2]
  exact sub_1079_2

theorem sub_2570_2532 : Law2570.Subspectral Law2532 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2570, spectrum_eq_of_isDual dual_2532]
  exact sub_1081_1080

theorem sub_2572_2 : Law2572.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2572, spectrum_eq_of_isDual dual_2]
  exact sub_1116_2

theorem sub_2574_2535 : Law2574.Subspectral Law2535 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2574, spectrum_eq_of_isDual dual_2535]
  exact sub_1160_1156

theorem sub_2577_2 : Law2577.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2577, spectrum_eq_of_isDual dual_2]
  exact sub_1114_2

theorem sub_2578_2535 : Law2578.Subspectral Law2535 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2578, spectrum_eq_of_isDual dual_2535]
  exact sub_1157_1156

theorem sub_2580_2537 : Law2580.Subspectral Law2537 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2580, spectrum_eq_of_isDual dual_2537]
  exact sub_1159_1151

theorem sub_2581_2537 : Law2581.Subspectral Law2537 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2581, spectrum_eq_of_isDual dual_2537]
  exact sub_1153_1151

theorem sub_2583_2539 : Law2583.Subspectral Law2539 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2583, spectrum_eq_of_isDual dual_2539]
  exact sub_1162_1161

theorem sub_2585_2 : Law2585.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2585, spectrum_eq_of_isDual dual_2]
  exact sub_1089_2

theorem sub_2587_2542 : Law2587.Subspectral Law2542 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2587, spectrum_eq_of_isDual dual_2542]
  exact sub_1106_1102

theorem sub_2589_2 : Law2589.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2589, spectrum_eq_of_isDual dual_2]
  exact sub_1126_2

theorem sub_2594_2 : Law2594.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2594, spectrum_eq_of_isDual dual_2]
  exact sub_1135_2

theorem sub_2597_2593 : Law2597.Subspectral Law2593 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2597, spectrum_eq_of_isDual dual_2593]
  exact sub_1176_1172

theorem sub_2599_2 : Law2599.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2599, spectrum_eq_of_isDual dual_2]
  exact sub_1143_2

theorem sub_2606_2 : Law2606.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2606, spectrum_eq_of_isDual dual_2]
  exact sub_1138_2

theorem sub_2607_2 : Law2607.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2607, spectrum_eq_of_isDual dual_2]
  exact sub_1169_2

theorem sub_2611_2 : Law2611.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2611, spectrum_eq_of_isDual dual_2]
  exact sub_1124_2

theorem sub_2615_2547 : Law2615.Subspectral Law2547 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2615, spectrum_eq_of_isDual dual_2547]
  exact sub_1170_1168

theorem sub_2616_2548 : Law2616.Subspectral Law2548 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2616, spectrum_eq_of_isDual dual_2548]
  exact sub_1140_1139

theorem sub_2617_2549 : Law2617.Subspectral Law2549 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2617, spectrum_eq_of_isDual dual_2549]
  exact sub_1216_1215

theorem sub_2619_2551 : Law2619.Subspectral Law2551 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2619, spectrum_eq_of_isDual dual_2551]
  exact sub_1105_1097

theorem sub_2620_2551 : Law2620.Subspectral Law2551 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2620, spectrum_eq_of_isDual dual_2551]
  exact sub_1099_1097

theorem sub_2624_2 : Law2624.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2624, spectrum_eq_of_isDual dual_2]
  exact sub_1142_2

theorem sub_2630_2555 : Law2630.Subspectral Law2555 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2630, spectrum_eq_of_isDual dual_2555]
  exact sub_1136_1134

theorem sub_2632_2557 : Law2632.Subspectral Law2557 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2632, spectrum_eq_of_isDual dual_2557]
  exact sub_1211_1209

theorem sub_2634_2559 : Law2634.Subspectral Law2559 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2634, spectrum_eq_of_isDual dual_2559]
  exact sub_1193_1185

theorem sub_2636_2560 : Law2636.Subspectral Law2560 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2636, spectrum_eq_of_isDual dual_2560]
  exact sub_1128_1127

theorem sub_2637_2561 : Law2637.Subspectral Law2561 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2637, spectrum_eq_of_isDual dual_2561]
  exact sub_1196_1195

theorem sub_2640_2598 : Law2640.Subspectral Law2598 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2640, spectrum_eq_of_isDual dual_2598]
  exact sub_1206_1205

theorem sub_2641_2615 : Law2641.Subspectral Law2615 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2641, spectrum_eq_of_isDual dual_2615]
  exact sub_1179_1170

theorem sub_2642_2565 : Law2642.Subspectral Law2565 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2642, spectrum_eq_of_isDual dual_2565]
  exact sub_1145_1144

theorem sub_2713_693 : Law2713.Subspectral Law693 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2713, spectrum_eq_of_isDual dual_693]
  exact sub_961_3026

theorem sub_2715_2708 : Law2715.Subspectral Law2708 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2715, spectrum_eq_of_isDual dual_2708]
  exact sub_997_891

theorem sub_2719_2708 : Law2719.Subspectral Law2708 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2719, spectrum_eq_of_isDual dual_2708]
  exact sub_892_891

theorem sub_2721_2906 : Law2721.Subspectral Law2906 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2721, spectrum_eq_of_isDual dual_2906]
  exact sub_927_741

theorem sub_2723_2711 : Law2723.Subspectral Law2711 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2723, spectrum_eq_of_isDual dual_2711]
  exact sub_996_979

theorem sub_2726_2 : Law2726.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2726, spectrum_eq_of_isDual dual_2]
  exact sub_918_2

theorem sub_2729_2717 : Law2729.Subspectral Law2717 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2729, spectrum_eq_of_isDual dual_2717]
  exact sub_995_890

theorem sub_2732_2705 : Law2732.Subspectral Law2705 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2732, spectrum_eq_of_isDual dual_2705]
  exact sub_998_946

theorem sub_2735_2 : Law2735.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2735, spectrum_eq_of_isDual dual_2]
  exact sub_877_2

theorem sub_2738_2 : Law2738.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2738, spectrum_eq_of_isDual dual_2]
  exact sub_953_2

theorem sub_2745_30 : Law2745.Subspectral Law30 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2745, spectrum_eq_of_isDual dual_30]
  exact sub_899_15

theorem sub_2747_285 : Law2747.Subspectral Law285 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2747, spectrum_eq_of_isDual dual_285]
  exact sub_920_92

theorem sub_2748_2 : Law2748.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2748, spectrum_eq_of_isDual dual_2]
  exact sub_987_2

theorem sub_2750_297 : Law2750.Subspectral Law297 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2750, spectrum_eq_of_isDual dual_297]
  exact sub_965_96

theorem sub_2751_2 : Law2751.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2751, spectrum_eq_of_isDual dual_2]
  exact sub_936_2

theorem sub_2754_2 : Law2754.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2754, spectrum_eq_of_isDual dual_2]
  exact sub_894_2

theorem sub_2759_289 : Law2759.Subspectral Law289 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2759, spectrum_eq_of_isDual dual_289]
  exact sub_970_97

theorem sub_2760_2738 : Law2760.Subspectral Law2738 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2760, spectrum_eq_of_isDual dual_2738]
  exact sub_1006_953

theorem sub_2763_2 : Law2763.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2763, spectrum_eq_of_isDual dual_2]
  exact sub_924_2

theorem sub_2764_2762 : Law2764.Subspectral Law2762 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2764, spectrum_eq_of_isDual dual_2762]
  exact sub_992_982

theorem sub_2766_2754 : Law2766.Subspectral Law2754 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2766, spectrum_eq_of_isDual dual_2754]
  exact sub_1000_894

theorem sub_2768_2 : Law2768.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2768, spectrum_eq_of_isDual dual_2]
  exact sub_941_2

theorem sub_2771_751 : Law2771.Subspectral Law751 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2771, spectrum_eq_of_isDual dual_751]
  exact sub_876_2984

theorem sub_2772_485 : Law2772.Subspectral Law485 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2772, spectrum_eq_of_isDual dual_485]
  exact sub_874_3114

theorem sub_2773_2698 : Law2773.Subspectral Law2698 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2773, spectrum_eq_of_isDual dual_2698]
  exact sub_878_871

theorem sub_2777_2738 : Law2777.Subspectral Law2738 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2777, spectrum_eq_of_isDual dual_2738]
  exact sub_957_953

theorem sub_2781_2698 : Law2781.Subspectral Law2698 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2781, spectrum_eq_of_isDual dual_2698]
  exact sub_954_871

theorem sub_2783_2740 : Law2783.Subspectral Law2740 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2783, spectrum_eq_of_isDual dual_2740]
  exact sub_956_948

theorem sub_2784_2740 : Law2784.Subspectral Law2740 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2784, spectrum_eq_of_isDual dual_2740]
  exact sub_950_948

theorem sub_2786_2773 : Law2786.Subspectral Law2773 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2786, spectrum_eq_of_isDual dual_2773]
  exact sub_959_878

theorem sub_2790_2708 : Law2790.Subspectral Law2708 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2790, spectrum_eq_of_isDual dual_2708]
  exact sub_903_891

theorem sub_2792_2 : Law2792.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2792, spectrum_eq_of_isDual dual_2]
  exact sub_923_2

theorem sub_2793_2 : Law2793.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2793, spectrum_eq_of_isDual dual_2]
  exact sub_983_2

theorem sub_2796_2818 : Law2796.Subspectral Law2818 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2796, spectrum_eq_of_isDual dual_2818]
  exact sub_969_967

theorem sub_2797_2 : Law2797.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2797, spectrum_eq_of_isDual dual_2]
  exact sub_932_2

theorem sub_2798_2708 : Law2798.Subspectral Law2708 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2798, spectrum_eq_of_isDual dual_2708]
  exact sub_1007_891

theorem sub_2800_2 : Law2800.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2800, spectrum_eq_of_isDual dual_2]
  exact sub_973_2

theorem sub_2802_2 : Law2802.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2802, spectrum_eq_of_isDual dual_2]
  exact sub_940_2

theorem sub_2807_2806 : Law2807.Subspectral Law2806 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2807, spectrum_eq_of_isDual dual_2806]
  exact sub_900_884

theorem sub_2809_2 : Law2809.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2809, spectrum_eq_of_isDual dual_2]
  exact sub_935_2

theorem sub_2810_2 : Law2810.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2810, spectrum_eq_of_isDual dual_2]
  exact sub_966_2

theorem sub_2813_2838 : Law2813.Subspectral Law2838 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2813, spectrum_eq_of_isDual dual_2838]
  exact sub_986_984

theorem sub_2815_2 : Law2815.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2815, spectrum_eq_of_isDual dual_2]
  exact sub_988_2

theorem sub_2817_2835 : Law2817.Subspectral Law2835 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2817, spectrum_eq_of_isDual dual_2835]
  exact sub_1010_1008

theorem sub_2819_2751 : Law2819.Subspectral Law2751 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2819, spectrum_eq_of_isDual dual_2751]
  exact sub_937_936

theorem sub_2822_2754 : Law2822.Subspectral Law2754 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2822, spectrum_eq_of_isDual dual_2754]
  exact sub_902_894

theorem sub_2823_2754 : Law2823.Subspectral Law2754 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2823, spectrum_eq_of_isDual dual_2754]
  exact sub_896_894

theorem sub_2824_2718 : Law2824.Subspectral Law2718 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2824, spectrum_eq_of_isDual dual_2718]
  exact sub_888_881

theorem sub_2827_2 : Law2827.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2827, spectrum_eq_of_isDual dual_2]
  exact sub_939_2

theorem sub_2829_2 : Law2829.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2829, spectrum_eq_of_isDual dual_2]
  exact sub_974_2

theorem sub_2832_2 : Law2832.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2832, spectrum_eq_of_isDual dual_2]
  exact sub_1005_2

theorem sub_2833_2797 : Law2833.Subspectral Law2797 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2833, spectrum_eq_of_isDual dual_2797]
  exact sub_933_932

theorem sub_2834_2 : Law2834.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2834, spectrum_eq_of_isDual dual_2]
  exact sub_971_2

theorem sub_2837_2 : Law2837.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2837, spectrum_eq_of_isDual dual_2]
  exact sub_990_2

theorem sub_2838_2793 : Law2838.Subspectral Law2793 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2838, spectrum_eq_of_isDual dual_2793]
  exact sub_984_983

theorem sub_2839_2726 : Law2839.Subspectral Law2726 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2839, spectrum_eq_of_isDual dual_2726]
  exact sub_925_918

theorem sub_2843_2766 : Law2843.Subspectral Law2766 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2843, spectrum_eq_of_isDual dual_2766]
  exact sub_1003_1000

theorem sub_2844_2800 : Law2844.Subspectral Law2800 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2844, spectrum_eq_of_isDual dual_2800]
  exact sub_976_973

theorem sub_2845_2768 : Law2845.Subspectral Law2768 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2845, spectrum_eq_of_isDual dual_2768]
  exact sub_942_941

theorem sub_2846_2769 : Law2846.Subspectral Law2769 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2846, spectrum_eq_of_isDual dual_2769]
  exact sub_1019_1018

theorem sub_2907_668 : Law2907.Subspectral Law668 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2907, spectrum_eq_of_isDual dual_668]
  exact sub_705_2901

theorem sub_2911_2 : Law2911.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2911, spectrum_eq_of_isDual dual_2]
  exact sub_688_2

theorem sub_2914_2932 : Law2914.Subspectral Law2932 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2914, spectrum_eq_of_isDual dual_2932]
  exact sub_776_792

theorem sub_2922_2911 : Law2922.Subspectral Law2911 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2922, spectrum_eq_of_isDual dual_2911]
  exact sub_689_688

theorem sub_2926_2904 : Law2926.Subspectral Law2904 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2926, spectrum_eq_of_isDual dual_2904]
  exact sub_793_742

theorem sub_2932_1689 : Law2932.Subspectral Law1689 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2932, spectrum_eq_of_isDual dual_1689]
  exact sub_792_1923

theorem sub_2934_2924 : Law2934.Subspectral Law2924 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2934, spectrum_eq_of_isDual dual_2924]
  exact sub_726_724

theorem sub_2941_2984 : Law2941.Subspectral Law2984 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2941, spectrum_eq_of_isDual dual_2984]
  exact sub_750_751

theorem sub_2943_908 : Law2943.Subspectral Law908 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2943, spectrum_eq_of_isDual dual_908]
  exact sub_745_2704

theorem sub_2948_2 : Law2948.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2948, spectrum_eq_of_isDual dual_2]
  exact sub_696_2

theorem sub_2950_7 : Law2950.Subspectral Law7 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2950, spectrum_eq_of_isDual dual_7]
  exact sub_717_7

theorem sub_2954_2950 : Law2954.Subspectral Law2950 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2954, spectrum_eq_of_isDual dual_2950]
  exact sub_733_717

theorem sub_2957_1698 : Law2957.Subspectral Law1698 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2957, spectrum_eq_of_isDual dual_1698]
  exact sub_691_1976

theorem sub_2961_2 : Law2961.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2961, spectrum_eq_of_isDual dual_2]
  exact sub_728_2

theorem sub_2966_2995 : Law2966.Subspectral Law2995 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2966, spectrum_eq_of_isDual dual_2995]
  exact sub_721_720

theorem sub_2970_3032 : Law2970.Subspectral Law3032 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2970, spectrum_eq_of_isDual dual_3032]
  exact sub_772_771

theorem sub_2971_2954 : Law2971.Subspectral Law2954 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2971, spectrum_eq_of_isDual dual_2954]
  exact sub_738_733

theorem sub_2975_2974 : Law2975.Subspectral Law2974 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2975, spectrum_eq_of_isDual dual_2974]
  exact sub_671_673

theorem sub_2976_2901 : Law2976.Subspectral Law2901 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2976, spectrum_eq_of_isDual dual_2901]
  exact sub_675_668

theorem sub_2978_2 : Law2978.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2978, spectrum_eq_of_isDual dual_2]
  exact sub_710_2

theorem sub_2984_792 : Law2984.Subspectral Law792 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2984, spectrum_eq_of_isDual dual_792]
  exact sub_751_2932

theorem sub_2986_2943 : Law2986.Subspectral Law2943 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2986, spectrum_eq_of_isDual dual_2943]
  exact sub_753_745

theorem sub_2988_2978 : Law2988.Subspectral Law2978 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2988, spectrum_eq_of_isDual dual_2978]
  exact sub_712_710

theorem sub_2995_2 : Law2995.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2995, spectrum_eq_of_isDual dual_2]
  exact sub_720_2

theorem sub_3000_2 : Law3000.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3000, spectrum_eq_of_isDual dual_2]
  exact sub_729_2

theorem sub_3010_2948 : Law3010.Subspectral Law2948 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3010, spectrum_eq_of_isDual dual_2948]
  exact sub_697_696

theorem sub_3012_3036 : Law3012.Subspectral Law3036 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3012, spectrum_eq_of_isDual dual_3036]
  exact sub_732_730

theorem sub_3013_2953 : Law3013.Subspectral Law2953 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3013, spectrum_eq_of_isDual dual_2953]
  exact sub_763_762

theorem sub_3016_3041 : Law3016.Subspectral Law3041 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3016, spectrum_eq_of_isDual dual_3041]
  exact sub_783_781

theorem sub_3017_2 : Law3017.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3017, spectrum_eq_of_isDual dual_2]
  exact sub_718_2

theorem sub_3020_3038 : Law3020.Subspectral Law3038 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3020, spectrum_eq_of_isDual dual_3038]
  exact sub_807_805

theorem sub_3021_2953 : Law3021.Subspectral Law2953 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3021, spectrum_eq_of_isDual dual_2953]
  exact sub_764_762

theorem sub_3022_2954 : Law3022.Subspectral Law2954 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3022, spectrum_eq_of_isDual dual_2954]
  exact sub_734_733

theorem sub_3023_2955 : Law3023.Subspectral Law2955 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3023, spectrum_eq_of_isDual dual_2955]
  exact sub_810_809

theorem sub_3026_3009 : Law3026.Subspectral Law3009 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3026, spectrum_eq_of_isDual dual_3009]
  exact sub_693_681

theorem sub_3032_3003 : Law3032.Subspectral Law3003 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3032, spectrum_eq_of_isDual dual_3003]
  exact sub_771_770

theorem sub_3033_2980 : Law3033.Subspectral Law2980 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3033, spectrum_eq_of_isDual dual_2980]
  exact sub_813_754

theorem sub_3035_3046 : Law3035.Subspectral Law3046 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3035, spectrum_eq_of_isDual dual_3046]
  exact sub_802_800

theorem sub_3036_2961 : Law3036.Subspectral Law2961 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3036, spectrum_eq_of_isDual dual_2961]
  exact sub_730_728

theorem sub_3038_2963 : Law3038.Subspectral Law2963 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3038, spectrum_eq_of_isDual dual_2963]
  exact sub_805_803

theorem sub_3042_2929 : Law3042.Subspectral Law2929 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3042, spectrum_eq_of_isDual dual_2929]
  exact sub_722_715

theorem sub_3043_3040 : Law3043.Subspectral Law3040 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3043, spectrum_eq_of_isDual dual_3040]
  exact sub_790_787

theorem sub_3046_3036 : Law3046.Subspectral Law3036 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3046, spectrum_eq_of_isDual dual_3036]
  exact sub_800_730

theorem sub_3047_3003 : Law3047.Subspectral Law3003 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3047, spectrum_eq_of_isDual dual_3003]
  exact sub_773_770

theorem sub_3048_3042 : Law3048.Subspectral Law3042 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3048, spectrum_eq_of_isDual dual_3042]
  exact sub_739_722

theorem sub_3107_2 : Law3107.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3107, spectrum_eq_of_isDual dual_2]
  exact sub_539_2

theorem sub_3109_874 : Law3109.Subspectral Law874 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3109, spectrum_eq_of_isDual dual_874]
  exact sub_538_2772

theorem sub_3110_2 : Law3110.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3110, spectrum_eq_of_isDual dual_2]
  exact sub_502_2

theorem sub_3111_3104 : Law3111.Subspectral Law3104 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3111, spectrum_eq_of_isDual dual_3104]
  exact sub_540_465

theorem sub_3114_2 : Law3114.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3114, spectrum_eq_of_isDual dual_2]
  exact sub_485_2

theorem sub_3119_2772 : Law3119.Subspectral Law2772 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3119, spectrum_eq_of_isDual dual_2772]
  exact sub_555_874

theorem sub_3121_3114 : Law3121.Subspectral Law3114 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3121, spectrum_eq_of_isDual dual_3114]
  exact sub_591_485

theorem sub_3127_794 : Law3127.Subspectral Law794 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3127, spectrum_eq_of_isDual dual_794]
  exact sub_521_2918

theorem sub_3132_2 : Law3132.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3132, spectrum_eq_of_isDual dual_2]
  exact sub_512_2

theorem sub_3133_3104 : Law3133.Subspectral Law3104 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3133, spectrum_eq_of_isDual dual_3104]
  exact sub_574_465

theorem sub_3135_3127 : Law3135.Subspectral Law3127 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3135, spectrum_eq_of_isDual dual_3127]
  exact sub_589_521

theorem sub_3137_3110 : Law3137.Subspectral Law3110 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3137, spectrum_eq_of_isDual dual_3110]
  exact sub_523_502

theorem sub_3138_3111 : Law3138.Subspectral Law3111 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3138, spectrum_eq_of_isDual dual_3111]
  exact sub_592_540

theorem sub_3141_3179 : Law3141.Subspectral Law3179 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3141, spectrum_eq_of_isDual dual_3179]
  exact sub_471_472

theorem sub_3146_2 : Law3146.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3146, spectrum_eq_of_isDual dual_2]
  exact sub_542_2

theorem sub_3151_683 : Law3151.Subspectral Law683 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3151, spectrum_eq_of_isDual dual_683]
  exact sub_493_2991

theorem sub_3153_22 : Law3153.Subspectral Law22 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3153, spectrum_eq_of_isDual dual_22]
  exact sub_514_37

theorem sub_3157_2 : Law3157.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3157, spectrum_eq_of_isDual dual_2]
  exact sub_530_2

theorem sub_3158_3154 : Law3158.Subspectral Law3154 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3158, spectrum_eq_of_isDual dual_3154]
  exact sub_606_581

theorem sub_3160_886 : Law3160.Subspectral Law886 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3160, spectrum_eq_of_isDual dual_886]
  exact sub_488_2788

theorem sub_3166_3154 : Law3166.Subspectral Law3154 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3166, spectrum_eq_of_isDual dual_3154]
  exact sub_600_581

theorem sub_3169_2 : Law3169.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3169, spectrum_eq_of_isDual dual_2]
  exact sub_518_2

theorem sub_3170_3154 : Law3170.Subspectral Law3154 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3170, spectrum_eq_of_isDual dual_3154]
  exact sub_586_581

theorem sub_3172_3246 : Law3172.Subspectral Law3246 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3172, spectrum_eq_of_isDual dual_3246]
  exact sub_594_587

theorem sub_3173_3235 : Law3173.Subspectral Law3235 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3173, spectrum_eq_of_isDual dual_3235]
  exact sub_569_568

theorem sub_3174_3208 : Law3174.Subspectral Law3208 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3174, spectrum_eq_of_isDual dual_3208]
  exact sub_535_534

theorem sub_3175_2 : Law3175.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3175, spectrum_eq_of_isDual dual_2]
  exact sub_612_2

theorem sub_3179_3104 : Law3179.Subspectral Law3104 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3179, spectrum_eq_of_isDual dual_3104]
  exact sub_472_465

theorem sub_3181_2717 : Law3181.Subspectral Law2717 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3181, spectrum_eq_of_isDual dual_2717]
  exact sub_507_890

theorem sub_3183_3144 : Law3183.Subspectral Law3144 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3183, spectrum_eq_of_isDual dual_3144]
  exact sub_551_547

theorem sub_3186_2 : Law3186.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3186, spectrum_eq_of_isDual dual_2]
  exact sub_505_2

theorem sub_3190_3146 : Law3190.Subspectral Law3146 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3190, spectrum_eq_of_isDual dual_3146]
  exact sub_544_542

theorem sub_3191_3110 : Law3191.Subspectral Law3110 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3191, spectrum_eq_of_isDual dual_3110]
  exact sub_509_502

theorem sub_3192_3187 : Law3192.Subspectral Law3187 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3192, spectrum_eq_of_isDual dual_3187]
  exact sub_553_548

theorem sub_3198_2 : Law3198.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3198, spectrum_eq_of_isDual dual_2]
  exact sub_517_2

theorem sub_3202_3224 : Law3202.Subspectral Law3224 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3202, spectrum_eq_of_isDual dual_3224]
  exact sub_563_561

theorem sub_3203_2 : Law3203.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3203, spectrum_eq_of_isDual dual_2]
  exact sub_526_2

theorem sub_3204_3154 : Law3204.Subspectral Law3154 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3204, spectrum_eq_of_isDual dual_3154]
  exact sub_601_581

theorem sub_3209_3158 : Law3209.Subspectral Law3158 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3209, spectrum_eq_of_isDual dual_3158]
  exact sub_611_606

theorem sub_3215_2 : Law3215.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3215, spectrum_eq_of_isDual dual_2]
  exact sub_529_2

theorem sub_3216_3156 : Law3216.Subspectral Law3156 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3216, spectrum_eq_of_isDual dual_3156]
  exact sub_560_559

theorem sub_3217_3154 : Law3217.Subspectral Law3154 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3217, spectrum_eq_of_isDual dual_3154]
  exact sub_605_581

theorem sub_3220_2 : Law3220.Subspectral Law2 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3220, spectrum_eq_of_isDual dual_2]
  exact sub_515_2

theorem sub_3221_3154 : Law3221.Subspectral Law3154 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3221, spectrum_eq_of_isDual dual_3154]
  exact sub_582_581

theorem sub_3224_3156 : Law3224.Subspectral Law3156 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3224, spectrum_eq_of_isDual dual_3156]
  exact sub_561_559

theorem sub_3225_3157 : Law3225.Subspectral Law3157 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3225, spectrum_eq_of_isDual dual_3157]
  exact sub_531_530

theorem sub_3228_961 : Law3228.Subspectral Law961 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3228, spectrum_eq_of_isDual dual_961]
  exact sub_496_2713

theorem sub_3229_3135 : Law3229.Subspectral Law3135 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3229, spectrum_eq_of_isDual dual_3135]
  exact sub_490_589

theorem sub_3230_3124 : Law3230.Subspectral Law3124 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3230, spectrum_eq_of_isDual dual_3124]
  exact sub_482_475

theorem sub_3231_3125 : Law3231.Subspectral Law3125 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3231, spectrum_eq_of_isDual dual_3125]
  exact sub_499_486

theorem sub_3233_3127 : Law3233.Subspectral Law3127 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3233, spectrum_eq_of_isDual dual_3127]
  exact sub_533_521

theorem sub_3240_3124 : Law3240.Subspectral Law3124 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3240, spectrum_eq_of_isDual dual_3124]
  exact sub_565_475

theorem sub_3241_3166 : Law3241.Subspectral Law3166 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3241, spectrum_eq_of_isDual dual_3166]
  exact sub_602_600

theorem sub_3243_3168 : Law3243.Subspectral Law3168 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3243, spectrum_eq_of_isDual dual_3168]
  exact sub_584_576

theorem sub_3244_3199 : Law3244.Subspectral Law3199 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3244, spectrum_eq_of_isDual dual_3199]
  exact sub_578_577

theorem sub_3245_3169 : Law3245.Subspectral Law3169 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3245, spectrum_eq_of_isDual dual_3169]
  exact sub_519_518

theorem sub_3246_3170 : Law3246.Subspectral Law3170 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3246, spectrum_eq_of_isDual dual_3170]
  exact sub_587_586

theorem sub_3248_3226 : Law3248.Subspectral Law3226 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3248, spectrum_eq_of_isDual dual_3226]
  exact sub_609_607

theorem sub_3249_3190 : Law3249.Subspectral Law3190 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3249, spectrum_eq_of_isDual dual_3190]
  exact sub_597_544

theorem sub_3250_3240 : Law3250.Subspectral Law3240 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3250, spectrum_eq_of_isDual dual_3240]
  exact sub_570_565

theorem sub_3251_3191 : Law3251.Subspectral Law3191 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3251, spectrum_eq_of_isDual dual_3191]
  exact sub_536_509

theorem sub_3252_3175 : Law3252.Subspectral Law3175 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_3252, spectrum_eq_of_isDual dual_3175]
  exact sub_613_612

theorem path_125_73 : Law125.Subspectral Law73 :=
  sub_125_73

theorem path_880_115 : Law880.Subspectral Law115 :=
  (sub_880_219).trans sub_219_115

theorem path_1496_481 : Law1496.Subspectral Law481 :=
  sub_1496_481

theorem path_887_695 : Law887.Subspectral Law695 :=
  (sub_887_1537).trans sub_1537_695

theorem path_895_898 : Law895.Subspectral Law898 :=
  (sub_895_2789).trans sub_2789_898

theorem path_115_873 : Law115.Subspectral Law873 :=
  (sub_115_219).trans sub_219_873

theorem singleton_2 : Law2.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (Subspectral.refl _) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_6 : Law6.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_7 : Law7.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_15 : Law15.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_15_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_17 : Law17.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_17_577).trans sub_577_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_18 : Law18.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_18_1799).trans sub_1799_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_20 : Law20.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_20_17).trans sub_17_577).trans sub_577_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_21 : Law21.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_21_613).trans sub_613_612).trans sub_612_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_22 : Law22.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_22_18).trans sub_18_1799).trans sub_1799_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_30 : Law30.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_30_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_32 : Law32.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_32_3199).trans sub_3199_3198).trans sub_3198_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_33 : Law33.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_33_3252).trans sub_3252_3175).trans sub_3175_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_35 : Law35.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_35_33).trans sub_33_3252).trans sub_3252_3175).trans sub_3175_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_36 : Law36.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_36_1936).trans sub_1936_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_37 : Law37.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_37_36).trans sub_36_1936).trans sub_1936_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_63_eq_63 : Law63.spectrum = Law63.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_64 : Law64.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_64_472).trans sub_472_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_66_eq_66 : Law66.spectrum = Law66.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_67 : Law67.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_67_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_69 : Law69.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_69_292).trans sub_292_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_70 : Law70.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_70_1567).trans sub_1567_1557).trans sub_1557_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_71 : Law71.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_73_eq_73 : Law73.spectrum = Law73.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_74 : Law74.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_74_1005).trans sub_1005_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_76 : Law76.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_76_925).trans sub_925_918).trans sub_918_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_77 : Law77.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_77_766).trans sub_766_717).trans sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_79 : Law79.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_79_789).trans sub_789_721).trans sub_721_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_80 : Law80.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_80_799).trans sub_799_770).trans sub_770_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_81 : Law81.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_81_74).trans sub_74_1005).trans sub_1005_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_83 : Law83.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_83_995).trans sub_995_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_84 : Law84.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_84_1606).trans sub_1606_1570).trans sub_1570_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_85 : Law85.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_85_74).trans sub_74_1005).trans sub_1005_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_87 : Law87.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_87_92).trans sub_92_91).trans sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_88 : Law88.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_88_809).trans sub_809_696).trans sub_696_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_89 : Law89.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_91 : Law91.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_92 : Law92.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_92_91).trans sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_93 : Law93.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_93_925).trans sub_925_918).trans sub_918_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_95 : Law95.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_95_91).trans sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_96 : Law96.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_96_92).trans sub_92_91).trans sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_97 : Law97.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_97_92).trans sub_92_91).trans sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_98 : Law98.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_98_976).trans sub_976_973).trans sub_973_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_115_eq_115 : Law115.spectrum = Law115.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_116 : Law116.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_116_878).trans sub_878_871).trans sub_871_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_118_eq_118 : Law118.spectrum = Law118.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_119 : Law119.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_119_888).trans sub_888_881).trans sub_881_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_121 : Law121.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_121_1105).trans sub_1105_1079).trans sub_1079_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_122 : Law122.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_122_1770).trans sub_1770_1689).trans sub_1689_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_123 : Law123.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_123_119).trans sub_119_888).trans sub_888_881).trans sub_881_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_125_eq_125 : Law125.spectrum = Law125.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_126 : Law126.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_126_915).trans sub_915_911).trans sub_911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_128 : Law128.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_128_1222).trans sub_1222_1145).trans sub_1145_1142).trans sub_1142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_129 : Law129.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_129_128).trans sub_128_1222).trans sub_1222_1145).trans sub_1145_1142).trans sub_1142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_131 : Law131.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_131_1414).trans sub_1414_1411).trans sub_1411_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_132 : Law132.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_132_1398).trans sub_1398_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_133 : Law133.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_133_1329).trans sub_1329_149).trans sub_149_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_135 : Law135.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_135_1401).trans sub_1401_1333).trans sub_1333_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_136 : Law136.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_136_1809).trans sub_1809_1773).trans sub_1773_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_137 : Law137.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_137_959).trans sub_959_878).trans sub_878_871).trans sub_871_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_139 : Law139.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_139_1418).trans sub_1418_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_140 : Law140.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_140_1348).trans sub_1348_1345).trans sub_1345_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_141 : Law141.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_141_1409).trans sub_1409_1406).trans sub_1406_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_143 : Law143.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_143_1425).trans sub_1425_1421).trans sub_1421_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_144 : Law144.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_144_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_145 : Law145.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_145_144).trans sub_144_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_147 : Law147.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_147_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_148 : Law148.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_148_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_149 : Law149.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_149_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_150 : Law150.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_150_147).trans sub_147_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_167_eq_167 : Law167.spectrum = Law167.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem spectrum_168_eq_168 : Law168.spectrum = Law168.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem spectrum_170_eq_66 : Law170.spectrum = Law66.spectrum :=
  Set.Subset.antisymm (sub_170_66) (sub_66_170)

theorem singleton_171 : Law171.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_171_1497).trans sub_1497_1493).trans sub_1493_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_173 : Law173.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_173_3230).trans sub_3230_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_174 : Law174.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_174_2176).trans sub_2176_2095).trans sub_2095_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_175 : Law175.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_175_1514).trans sub_1514_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_177_eq_66 : Law177.spectrum = Law66.spectrum :=
  Set.Subset.antisymm ((sub_177_170).trans sub_170_66) ((sub_66_170).trans sub_170_177)

theorem singleton_178 : Law178.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_178_1524).trans sub_1524_1517).trans sub_1517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_180 : Law180.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_180_18).trans sub_18_1799).trans sub_1799_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_181 : Law181.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_181_1830).trans sub_1830_1753).trans sub_1753_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_183 : Law183.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_183_1829).trans sub_1829_1752).trans sub_1752_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_184 : Law184.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_184_1831).trans sub_1831_1754).trans sub_1754_1752).trans sub_1752_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_185 : Law185.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_185_178).trans sub_178_1524).trans sub_1524_1517).trans sub_1517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_187 : Law187.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_187_482).trans sub_482_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_188 : Law188.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_188_2215).trans sub_2215_2179).trans sub_2179_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_189 : Law189.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_189_2216).trans sub_2216_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_191 : Law191.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_191_1991).trans sub_1991_1990).trans sub_1990_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_192 : Law192.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_192_183).trans sub_183_1829).trans sub_1829_1752).trans sub_1752_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_193 : Law193.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_193_171).trans sub_171_1497).trans sub_1497_1493).trans sub_1493_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_195 : Law195.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_195_1818).trans sub_1818_1743).trans sub_1743_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_196 : Law196.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_196_1957).trans sub_1957_1956).trans sub_1956_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_197 : Law197.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_197_181).trans sub_181_1830).trans sub_1830_1753).trans sub_1753_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_199 : Law199.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_199_183).trans sub_183_1829).trans sub_1829_1752).trans sub_1752_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_200 : Law200.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_200_183).trans sub_183_1829).trans sub_1829_1752).trans sub_1752_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_201 : Law201.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_201_2008).trans sub_2008_1999).trans sub_1999_1889).trans sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_202 : Law202.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_202_193).trans sub_193_171).trans sub_171_1497).trans sub_1497_1493).trans sub_1493_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_219_eq_115 : Law219.spectrum = Law115.spectrum :=
  Set.Subset.antisymm (sub_219_115) (sub_115_219)

theorem singleton_220 : Law220.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_220_1893).trans sub_1893_1891).trans sub_1891_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_222_eq_125 : Law222.spectrum = Law125.spectrum :=
  Set.Subset.antisymm (sub_222_125) (sub_125_222)

theorem singleton_223 : Law223.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_223_1903).trans sub_1903_1901).trans sub_1901_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_225 : Law225.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_225_2323).trans sub_2323_2315).trans sub_2315_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_226 : Law226.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_226_2785).trans sub_2785_2780).trans sub_2780_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_227 : Law227.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_227_1920).trans sub_1920_1911).trans sub_1911_1889).trans sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_229_eq_118 : Law229.spectrum = Law118.spectrum :=
  Set.Subset.antisymm (sub_229_118) (sub_118_229)

theorem singleton_230 : Law230.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_230_1930).trans sub_1930_1923).trans sub_1923_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_232 : Law232.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_232_2643).trans sub_2643_2566).trans sub_2566_2565).trans sub_2565_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_233 : Law233.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_233_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_235 : Law235.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_235_2346).trans sub_2346_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_236 : Law236.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_236_2358).trans sub_2358_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_237 : Law237.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_239 : Law239.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_239_2619).trans sub_2619_2551).trans sub_2551_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_240 : Law240.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_240_2824).trans sub_2824_2718).trans sub_2718_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_241 : Law241.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_241_1974).trans sub_1974_1965).trans sub_1965_1889).trans sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_243 : Law243.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_243_2429).trans sub_2429_2354).trans sub_2354_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_244 : Law244.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_244_2434).trans sub_2434_2358).trans sub_2358_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_245 : Law245.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_245_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_247 : Law247.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_247_2440).trans sub_2440_2363).trans sub_2363_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_248 : Law248.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_248_232).trans sub_232_2643).trans sub_2643_2566).trans sub_2566_2565).trans sub_2565_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_249 : Law249.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_249_233).trans sub_233_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_251 : Law251.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_251_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_252 : Law252.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_252_235).trans sub_235_2346).trans sub_2346_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_253 : Law253.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_253_2386).trans sub_2386_237).trans sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_254 : Law254.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_254_237).trans sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_271_eq_63 : Law271.spectrum = Law63.spectrum :=
  Set.Subset.antisymm (sub_271_63) (sub_63_271)

theorem singleton_272 : Law272.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_272_2096).trans sub_2096_2094).trans sub_2094_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_274_eq_73 : Law274.spectrum = Law73.spectrum :=
  Set.Subset.antisymm (sub_274_73) (sub_73_274)

theorem singleton_275 : Law275.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_275_2106).trans sub_2106_1732).trans sub_1732_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_277 : Law277.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_277_2729).trans sub_2729_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_278 : Law278.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_278_2832).trans sub_2832_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_279 : Law279.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_279_278).trans sub_278_2832).trans sub_2832_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_281_eq_66 : Law281.spectrum = Law66.spectrum :=
  Set.Subset.antisymm (sub_281_66) (sub_66_281)

theorem singleton_282 : Law282.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_282_2133).trans sub_2133_2129).trans sub_2129_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_284 : Law284.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_284_2839).trans sub_2839_2726).trans sub_2726_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_285 : Law285.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_285_299).trans sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_287 : Law287.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_287_285).trans sub_285_299).trans sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_288 : Law288.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_288_284).trans sub_284_2839).trans sub_2839_2726).trans sub_2726_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_289 : Law289.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_289_285).trans sub_285_299).trans sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_291 : Law291.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_291_67).trans sub_67_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_292 : Law292.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_292_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_293 : Law293.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_295 : Law295.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_295_2967).trans sub_2967_2966).trans sub_2966_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_296 : Law296.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_296_2955).trans sub_2955_2948).trans sub_2948_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_297 : Law297.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_297_285).trans sub_285_299).trans sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_299 : Law299.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_300 : Law300.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_300_2999).trans sub_2999_2950).trans sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_301 : Law301.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_301_2839).trans sub_2839_2726).trans sub_2726_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_303 : Law303.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_303_299).trans sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_304 : Law304.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_305 : Law305.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_305_278).trans sub_278_2832).trans sub_2832_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_306 : Law306.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_306_2844).trans sub_2844_2800).trans sub_2800_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_465 : Law465.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_467_eq_467 : Law467.spectrum = Law467.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_468 : Law468.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_470 : Law470.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_470_1926).trans sub_1926_173).trans sub_173_3230).trans sub_3230_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_471 : Law471.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_471_472).trans sub_472_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_472 : Law472.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_472_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_474_eq_474 : Law474.spectrum = Law474.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_475 : Law475.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_478 : Law478.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_478_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_480 : Law480.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_480_2806).trans sub_2806_1351).trans sub_1351_1182).trans sub_1182_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_481_eq_481 : Law481.spectrum = Law481.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_482 : Law482.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_482_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_484 : Law484.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_484_3181).trans sub_3181_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_485 : Law485.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_486 : Law486.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_486_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_488 : Law488.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_488_2788).trans sub_2788_538).trans sub_538_2772).trans sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_490 : Law490.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_490_589).trans sub_589_521).trans sub_521_2918).trans sub_2918_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_493 : Law493.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_493_2704).trans sub_2704_69).trans sub_69_292).trans sub_292_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_494 : Law494.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_494_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_496 : Law496.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_496_484).trans sub_484_3181).trans sub_3181_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_497 : Law497.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_497_480).trans sub_480_2806).trans sub_2806_1351).trans sub_1351_1182).trans sub_1182_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_498 : Law498.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_498_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_499 : Law499.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_499_486).trans sub_486_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_501_eq_501 : Law501.spectrum = Law501.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_502 : Law502.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_502_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_505 : Law505.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_505_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_507 : Law507.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_507_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_509 : Law509.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_509_502).trans sub_502_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_512 : Law512.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_512_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_514 : Law514.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_514_98).trans sub_98_976).trans sub_976_973).trans sub_973_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_515 : Law515.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_515_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_517 : Law517.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_518 : Law518.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_518_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_519 : Law519.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_519_515).trans sub_515_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_521 : Law521.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_521_2918).trans sub_2918_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_523 : Law523.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_523_502).trans sub_502_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_525 : Law525.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_525_519).trans sub_519_515).trans sub_515_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_526 : Law526.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_526_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_527 : Law527.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_527_505).trans sub_505_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_529 : Law529.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_529_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_530 : Law530.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_531 : Law531.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_531_529).trans sub_529_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_533 : Law533.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_533_607).trans sub_607_494).trans sub_494_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_534 : Law534.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_534_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_535 : Law535.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_535_534).trans sub_534_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_536 : Law536.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_536_509).trans sub_509_502).trans sub_502_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_538 : Law538.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_538_2772).trans sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_539 : Law539.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_539_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_540 : Law540.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_540_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_542 : Law542.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_542_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_544 : Law544.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_544_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_546_eq_546 : Law546.spectrum = Law546.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_547 : Law547.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_547_2109).trans sub_2109_2772).trans sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_548 : Law548.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_548_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_550 : Law550.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_550_542).trans sub_542_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_551 : Law551.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_551_547).trans sub_547_2109).trans sub_2109_2772).trans sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_552 : Law552.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_552_542).trans sub_542_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_553 : Law553.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_553_548).trans sub_548_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_555 : Law555.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_555_874).trans sub_874_3114).trans sub_3114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_556_eq_556 : Law556.spectrum = Law556.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_557 : Law557.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_557_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_559 : Law559.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_559_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_560 : Law560.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_560_559).trans sub_559_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_561 : Law561.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_561_559).trans sub_559_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_563 : Law563.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_563_585).trans sub_585_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_564 : Law564.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_564_525).trans sub_525_519).trans sub_519_515).trans sub_515_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_565 : Law565.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_565_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_567 : Law567.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_567_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_568 : Law568.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_568_567).trans sub_567_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_569 : Law569.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_569_568).trans sub_568_567).trans sub_567_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_570 : Law570.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_570_565).trans sub_565_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_573 : Law573.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_573_1683).trans sub_1683_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_574 : Law574.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_574_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_576 : Law576.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_576_600).trans sub_600_581).trans sub_581_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_577 : Law577.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_577_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_578 : Law578.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_578_577).trans sub_577_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_580 : Law580.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_580_605).trans sub_605_529).trans sub_529_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_581 : Law581.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_581_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_582 : Law582.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_582_581).trans sub_581_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_584 : Law584.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_584_602).trans sub_602_601).trans sub_601_526).trans sub_526_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_585 : Law585.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_585_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_586 : Law586.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_586_518).trans sub_518_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_587 : Law587.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_587_585).trans sub_585_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_589 : Law589.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_589_521).trans sub_521_2918).trans sub_2918_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_590 : Law590.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_590_539).trans sub_539_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_591 : Law591.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_591_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_592 : Law592.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_592_486).trans sub_486_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_594 : Law594.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_594_587).trans sub_587_585).trans sub_585_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_595 : Law595.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_595_533).trans sub_533_607).trans sub_607_494).trans sub_494_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_596 : Law596.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_596_567).trans sub_567_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_597 : Law597.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_597_544).trans sub_544_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_599 : Law599.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_599_597).trans sub_597_544).trans sub_544_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_600 : Law600.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_600_581).trans sub_581_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_601 : Law601.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_601_526).trans sub_526_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_602 : Law602.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_602_601).trans sub_601_526).trans sub_526_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_604 : Law604.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_604_529).trans sub_529_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_605 : Law605.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_605_529).trans sub_529_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_606 : Law606.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_606_530).trans sub_530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_607 : Law607.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_607_494).trans sub_494_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_609 : Law609.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_609_607).trans sub_607_494).trans sub_494_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_610 : Law610.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_610_590).trans sub_590_539).trans sub_539_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_611 : Law611.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_611_534).trans sub_534_517).trans sub_517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_612 : Law612.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_612_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_613 : Law613.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_613_612).trans sub_612_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_667_eq_667 : Law667.spectrum = Law667.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_668 : Law668.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_668_2108).trans sub_2108_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_670_eq_670 : Law670.spectrum = Law670.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_671 : Law671.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_671_673).trans sub_673_1294).trans sub_1294_1287).trans sub_1287_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_673 : Law673.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_673_1294).trans sub_1294_1287).trans sub_1287_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_674 : Law674.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_674_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_675 : Law675.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_675_674).trans sub_674_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_677_eq_677 : Law677.spectrum = Law677.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_678 : Law678.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_678_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_681 : Law681.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_681_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_683 : Law683.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_683_1942).trans sub_1942_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_685 : Law685.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_685_555).trans sub_555_874).trans sub_874_3114).trans sub_3114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_687 : Law687.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_687_995).trans sub_995_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_688 : Law688.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_689 : Law689.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_691 : Law691.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_691_1976).trans sub_1976_3119).trans sub_3119_2772).trans sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_693 : Law693.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_693_681).trans sub_681_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_695_eq_695 : Law695.spectrum = Law695.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_696 : Law696.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_696_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_697 : Law697.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_697_696).trans sub_696_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_699 : Law699.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_699_673).trans sub_673_1294).trans sub_1294_1287).trans sub_1287_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_700 : Law700.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_700_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_701 : Law701.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_701_674).trans sub_674_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_702 : Law702.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_702_700).trans sub_700_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_704_eq_704 : Law704.spectrum = Law704.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_705 : Law705.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_705_2901).trans sub_2901_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_708 : Law708.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_708_2418).trans sub_2418_2312).trans sub_2312_2523).trans sub_2523_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_710 : Law710.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_710_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_712 : Law712.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_712_710).trans sub_710_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_715 : Law715.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_715_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_717 : Law717.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_718 : Law718.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_718_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_720 : Law720.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_721 : Law721.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_721_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_722 : Law722.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_722_715).trans sub_715_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_724 : Law724.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_724_2365).trans sub_2365_3127).trans sub_3127_794).trans sub_794_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_726 : Law726.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((((sub_726_724).trans sub_724_2365).trans sub_2365_3127).trans sub_3127_794).trans sub_794_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_728 : Law728.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_728_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_729 : Law729.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_729_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_730 : Law730.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_730_728).trans sub_728_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_732 : Law732.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_732_730).trans sub_730_728).trans sub_728_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_733 : Law733.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_733_717).trans sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_734 : Law734.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_734_733).trans sub_733_717).trans sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_736 : Law736.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_736_95).trans sub_95_91).trans sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_737 : Law737.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_737_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_738 : Law738.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_738_733).trans sub_733_717).trans sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_739 : Law739.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_739_712).trans sub_712_710).trans sub_710_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_741 : Law741.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_741_3213).trans sub_3213_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_742 : Law742.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_742_15).trans sub_15_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_743 : Law743.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_743_552).trans sub_552_542).trans sub_542_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_745 : Law745.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_745_484).trans sub_484_3181).trans sub_3181_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_747 : Law747.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_747_544).trans sub_544_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_749_eq_556 : Law749.spectrum = Law556.spectrum :=
  Set.Subset.antisymm (sub_749_556) ((sub_556_2982).trans sub_2982_749)

theorem singleton_750 : Law750.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_750_751).trans sub_751_2932).trans sub_2932_1689).trans sub_1689_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_751 : Law751.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_751_2932).trans sub_2932_1689).trans sub_1689_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_753 : Law753.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((((sub_753_745).trans sub_745_484).trans sub_484_3181).trans sub_3181_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_754 : Law754.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_754_710).trans sub_710_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_755 : Law755.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_755_674).trans sub_674_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_756 : Law756.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_756_712).trans sub_712_710).trans sub_710_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_758 : Law758.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_758_1714).trans sub_1714_2906).trans sub_2906_494).trans sub_494_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_760 : Law760.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_760_557).trans sub_557_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_762 : Law762.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_762_717).trans sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_763 : Law763.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_763_762).trans sub_762_717).trans sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_764 : Law764.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_764_762).trans sub_762_717).trans sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_766 : Law766.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_766_717).trans sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_767 : Law767.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_767_717).trans sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_768 : Law768.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_768_730).trans sub_730_728).trans sub_728_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_770 : Law770.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_770_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_771 : Law771.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_771_770).trans sub_770_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_772 : Law772.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_772_771).trans sub_771_770).trans sub_770_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_773 : Law773.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_773_770).trans sub_770_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_775_eq_556 : Law775.spectrum = Law556.spectrum :=
  Set.Subset.antisymm (((sub_775_2928).trans sub_2928_749).trans sub_749_556) (sub_556_775)

theorem singleton_776 : Law776.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_776_792).trans sub_792_1923).trans sub_1923_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_777 : Law777.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_777_715).trans sub_715_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_779 : Law779.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_779_717).trans sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_780 : Law780.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_780_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_781 : Law781.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_781_718).trans sub_718_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_783 : Law783.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_783_781).trans sub_781_718).trans sub_718_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_784 : Law784.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_784_717).trans sub_717_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_785 : Law785.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_785_718).trans sub_718_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_787 : Law787.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_787_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_788 : Law788.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_788_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_789 : Law789.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_789_721).trans sub_721_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_790 : Law790.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_790_787).trans sub_787_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_792 : Law792.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_792_1923).trans sub_1923_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_793 : Law793.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_793_742).trans sub_742_15).trans sub_15_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_794 : Law794.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_794_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_795 : Law795.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_795_777).trans sub_777_715).trans sub_715_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_797 : Law797.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_797_789).trans sub_789_721).trans sub_721_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_798 : Law798.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_798_736).trans sub_736_95).trans sub_95_91).trans sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_799 : Law799.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_799_770).trans sub_770_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_800 : Law800.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_800_730).trans sub_730_728).trans sub_728_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_802 : Law802.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_802_813).trans sub_813_754).trans sub_754_710).trans sub_710_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_803 : Law803.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_803_728).trans sub_728_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_804 : Law804.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_804_729).trans sub_729_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_805 : Law805.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_805_730).trans sub_730_728).trans sub_728_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_807 : Law807.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_807_732).trans sub_732_730).trans sub_730_728).trans sub_728_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_808 : Law808.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_808_732).trans sub_732_730).trans sub_730_728).trans sub_728_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_809 : Law809.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_809_696).trans sub_696_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_810 : Law810.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_810_809).trans sub_809_696).trans sub_696_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_812 : Law812.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_812_787).trans sub_787_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_813 : Law813.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_813_754).trans sub_754_710).trans sub_710_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_814 : Law814.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_814_737).trans sub_737_720).trans sub_720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_815 : Law815.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_815_809).trans sub_809_696).trans sub_696_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_816 : Law816.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_816_790).trans sub_790_787).trans sub_787_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_871 : Law871.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_871_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_873_eq_873 : Law873.spectrum = Law873.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_874 : Law874.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_874_3114).trans sub_3114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_876 : Law876.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_876_2984).trans sub_2984_792).trans sub_792_1923).trans sub_1923_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_877 : Law877.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_877_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_878 : Law878.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_878_871).trans sub_871_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_880_eq_880 : Law880.spectrum = Law880.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_881 : Law881.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_881_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_883_eq_883 : Law883.spectrum = Law883.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_884 : Law884.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_884_2295).trans sub_2295_2508).trans sub_2508_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_886 : Law886.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_886_3109).trans sub_3109_874).trans sub_874_3114).trans sub_3114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_887_eq_887 : Law887.spectrum = Law887.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_888 : Law888.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_888_881).trans sub_881_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_890 : Law890.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_891 : Law891.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_891_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_892 : Law892.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_892_881).trans sub_881_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_894 : Law894.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_894_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_895_eq_895 : Law895.spectrum = Law895.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_896 : Law896.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_896_894).trans sub_894_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_898_eq_898 : Law898.spectrum = Law898.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_899 : Law899.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_899_15).trans sub_15_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_900 : Law900.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_900_884).trans sub_884_2295).trans sub_2295_2508).trans sub_2508_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_902 : Law902.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_902_894).trans sub_894_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_903 : Law903.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_903_891).trans sub_891_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_904 : Law904.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_904_894).trans sub_894_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_905 : Law905.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_905_903).trans sub_903_891).trans sub_891_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_907_eq_907 : Law907.spectrum = Law907.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_908 : Law908.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_908_291).trans sub_291_67).trans sub_67_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_911 : Law911.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_913 : Law913.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_913_1292).trans sub_1292_1683).trans sub_1683_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_915 : Law915.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_915_911).trans sub_911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_918 : Law918.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_918_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_920 : Law920.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_920_92).trans sub_92_91).trans sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_921 : Law921.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_921_986).trans sub_986_1011).trans sub_1011_935).trans sub_935_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_923 : Law923.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_923_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_924 : Law924.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_924_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_925 : Law925.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_925_918).trans sub_918_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_927 : Law927.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_927_741).trans sub_741_3213).trans sub_3213_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_929 : Law929.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_929_918).trans sub_918_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_931 : Law931.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_931_1012).trans sub_1012_936).trans sub_936_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_932 : Law932.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_932_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_933 : Law933.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_933_932).trans sub_932_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_935 : Law935.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_935_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_936 : Law936.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_936_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_937 : Law937.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_937_935).trans sub_935_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_939 : Law939.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_939_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_940 : Law940.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_940_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_941 : Law941.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_941_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_942 : Law942.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_942_939).trans sub_939_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_944 : Law944.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_944_173).trans sub_173_3230).trans sub_3230_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_945 : Law945.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_945_2976).trans sub_2976_2901).trans sub_2901_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_946 : Law946.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_946_871).trans sub_871_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_948 : Law948.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_948_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_949_eq_546 : Law949.spectrum = Law546.spectrum :=
  Set.Subset.antisymm (sub_949_546) (((sub_546_962).trans sub_962_1790).trans sub_1790_949)

theorem singleton_950 : Law950.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_950_948).trans sub_948_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_953 : Law953.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_953_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_954 : Law954.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_954_871).trans sub_871_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_956 : Law956.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_956_948).trans sub_948_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_957 : Law957.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_957_953).trans sub_953_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_958 : Law958.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_958_948).trans sub_948_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_959 : Law959.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_959_878).trans sub_878_871).trans sub_871_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_961 : Law961.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_961_3026).trans sub_3026_3009).trans sub_3009_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_962_eq_546 : Law962.spectrum = Law546.spectrum :=
  Set.Subset.antisymm (sub_962_546) (sub_546_962)

theorem singleton_963 : Law963.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_963_918).trans sub_918_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_965 : Law965.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_965_96).trans sub_96_92).trans sub_92_91).trans sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_966 : Law966.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_966_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_967 : Law967.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_967_966).trans sub_966_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_969 : Law969.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_969_967).trans sub_967_966).trans sub_966_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_970 : Law970.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_970_97).trans sub_97_92).trans sub_92_91).trans sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_971 : Law971.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_971_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_973 : Law973.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_973_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_974 : Law974.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_974_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_975 : Law975.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((((sub_975_970).trans sub_970_97).trans sub_97_92).trans sub_92_91).trans sub_91_89).trans sub_89_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_976 : Law976.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_976_973).trans sub_973_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_979 : Law979.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_979_15).trans sub_15_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_980 : Law980.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_980_918).trans sub_918_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_982 : Law982.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_982_1006).trans sub_1006_953).trans sub_953_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_983 : Law983.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_983_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_984 : Law984.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_984_983).trans sub_983_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_986 : Law986.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_986_1011).trans sub_1011_935).trans sub_935_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_987 : Law987.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_987_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_988 : Law988.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_988_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_990 : Law990.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_990_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_991 : Law991.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_991_983).trans sub_983_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_992 : Law992.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_992_982).trans sub_982_1006).trans sub_1006_953).trans sub_953_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_993 : Law993.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_993_990).trans sub_990_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_995 : Law995.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_995_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_996 : Law996.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_996_979).trans sub_979_15).trans sub_15_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_997 : Law997.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_997_891).trans sub_891_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_998 : Law998.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_998_946).trans sub_946_871).trans sub_871_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1000 : Law1000.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1000_894).trans sub_894_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1001 : Law1001.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1001_966).trans sub_966_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1002 : Law1002.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1002_932).trans sub_932_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1003 : Law1003.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1003_896).trans sub_896_894).trans sub_894_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1005 : Law1005.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1005_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1006 : Law1006.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1006_953).trans sub_953_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1007 : Law1007.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1007_891).trans sub_891_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1008 : Law1008.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1008_971).trans sub_971_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1010 : Law1010.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1010_1008).trans sub_1008_971).trans sub_971_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1011 : Law1011.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1011_935).trans sub_935_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1012 : Law1012.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1012_936).trans sub_936_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1013 : Law1013.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1013_937).trans sub_937_935).trans sub_935_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1015 : Law1015.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1015_1005).trans sub_1005_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1016 : Law1016.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1016_939).trans sub_939_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1017 : Law1017.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1017_940).trans sub_940_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1018 : Law1018.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1018_941).trans sub_941_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1019 : Law1019.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1019_942).trans sub_942_939).trans sub_939_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1074 : Law1074.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1074_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1076_eq_1076 : Law1076.spectrum = Law1076.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1077 : Law1077.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1077_119).trans sub_119_888).trans sub_888_881).trans sub_881_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1079 : Law1079.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1079_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1080 : Law1080.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1080_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1081 : Law1081.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1081_1079).trans sub_1079_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1083_eq_1083 : Law1083.spectrum = Law1083.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1084 : Law1084.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1084_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1087 : Law1087.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1087_1114).trans sub_1114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1089 : Law1089.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1089_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1091 : Law1091.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1091_1084).trans sub_1084_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1093 : Law1093.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1093_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1094 : Law1094.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1094_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1095 : Law1095.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1095_1074).trans sub_1074_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1097 : Law1097.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1097_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1098_eq_546 : Law1098.spectrum = Law546.spectrum :=
  Set.Subset.antisymm ((((sub_1098_1913).trans sub_1913_1790).trans sub_1790_949).trans sub_949_546) (((sub_546_1967).trans sub_1967_1764).trans sub_1764_1098)

theorem singleton_1099 : Law1099.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1099_1097).trans sub_1097_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1102 : Law1102.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1102_15).trans sub_15_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1103 : Law1103.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1103_1087).trans sub_1087_1114).trans sub_1114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1105 : Law1105.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1105_1079).trans sub_1079_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1106 : Law1106.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_1106_1102).trans sub_1102_15).trans sub_15_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1107 : Law1107.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1107_1097).trans sub_1097_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1108 : Law1108.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1108_1081).trans sub_1081_1079).trans sub_1079_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1110_eq_1110 : Law1110.spectrum = Law1110.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1111 : Law1111.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1111_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1114 : Law1114.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1116 : Law1116.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1116_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1118 : Law1118.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1118_1111).trans sub_1111_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1121 : Law1121.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1121_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1123 : Law1123.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1124 : Law1124.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1126 : Law1126.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1126_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1127 : Law1127.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1127_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1128 : Law1128.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1128_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1130 : Law1130.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1130_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1131_eq_556 : Law1131.spectrum = Law556.spectrum :=
  Set.Subset.antisymm (sub_1131_556) (sub_556_1131)

theorem singleton_1132 : Law1132.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1132_1111).trans sub_1111_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1134 : Law1134.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1134_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1135 : Law1135.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1135_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1136 : Law1136.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1136_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1138 : Law1138.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1138_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1139 : Law1139.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1139_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1140 : Law1140.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1140_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1142 : Law1142.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1143 : Law1143.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1143_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1144 : Law1144.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1144_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1145 : Law1145.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1145_1142).trans sub_1142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1147 : Law1147.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1147_69).trans sub_69_292).trans sub_292_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1148 : Law1148.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1148_1385).trans sub_1385_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1149 : Law1149.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1149_1074).trans sub_1074_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1151 : Law1151.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1151_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1153 : Law1153.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1153_1151).trans sub_1151_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1156 : Law1156.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1156_15).trans sub_15_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1157 : Law1157.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_1157_1156).trans sub_1156_15).trans sub_15_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1159 : Law1159.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1159_1151).trans sub_1151_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1160 : Law1160.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_1160_1156).trans sub_1156_15).trans sub_15_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1161 : Law1161.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1161_1080).trans sub_1080_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1162 : Law1162.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1162_1161).trans sub_1161_1080).trans sub_1080_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1164 : Law1164.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1164_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1166 : Law1166.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1166_1084).trans sub_1084_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1168 : Law1168.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1168_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1169 : Law1169.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1169_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1170 : Law1170.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1170_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1172 : Law1172.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1172_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1173 : Law1173.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1173_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1174 : Law1174.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1174_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1176 : Law1176.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1176_1172).trans sub_1172_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1177 : Law1177.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1177_1204).trans sub_1204_1142).trans sub_1142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1178 : Law1178.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1178_1127).trans sub_1127_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1179 : Law1179.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1179_1128).trans sub_1128_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1182 : Law1182.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1182_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1183 : Law1183.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1183_1074).trans sub_1074_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1185 : Law1185.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1185_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1186 : Law1186.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1186_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1187 : Law1187.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1187_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1189 : Law1189.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1189_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1190 : Law1190.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1190_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1191 : Law1191.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1191_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1193 : Law1193.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1193_1185).trans sub_1185_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1194 : Law1194.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1194_1126).trans sub_1126_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1195 : Law1195.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1195_1127).trans sub_1127_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1196 : Law1196.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1196_1128).trans sub_1128_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1198 : Law1198.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_1198_1147).trans sub_1147_69).trans sub_69_292).trans sub_292_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1199 : Law1199.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1199_1130).trans sub_1130_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1200 : Law1200.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1200_1094).trans sub_1094_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1201 : Law1201.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1201_1095).trans sub_1095_1074).trans sub_1074_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1203 : Law1203.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1203_1195).trans sub_1195_1127).trans sub_1127_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1204 : Law1204.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1204_1142).trans sub_1142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1205 : Law1205.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1205_1135).trans sub_1135_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1206 : Law1206.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1206_1205).trans sub_1205_1135).trans sub_1135_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1208 : Law1208.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1208_1219).trans sub_1219_1142).trans sub_1142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1209 : Law1209.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1209_1134).trans sub_1134_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1210 : Law1210.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1210_1135).trans sub_1135_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1211 : Law1211.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1211_1136).trans sub_1136_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1213 : Law1213.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1213_1191).trans sub_1191_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1214 : Law1214.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1214_1138).trans sub_1138_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1215 : Law1215.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1215_1139).trans sub_1139_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1216 : Law1216.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1216_1140).trans sub_1140_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1218 : Law1218.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1218_1196).trans sub_1196_1128).trans sub_1128_1124).trans sub_1124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1219 : Law1219.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1219_1142).trans sub_1142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1220 : Law1220.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1220_1143).trans sub_1143_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1221 : Law1221.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1221_1144).trans sub_1144_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1222 : Law1222.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1222_1145).trans sub_1145_1142).trans sub_1142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1277 : Law1277.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1277_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1279_eq_1279 : Law1279.spectrum = Law1279.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1280 : Law1280.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1280_1087).trans sub_1087_1114).trans sub_1114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1282 : Law1282.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1282_521).trans sub_521_2918).trans sub_2918_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1283 : Law1283.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1283_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1284 : Law1284.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1284_1283).trans sub_1283_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1286_eq_1286 : Law1286.spectrum = Law1286.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1287 : Law1287.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1287_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1290 : Law1290.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1290_1087).trans sub_1087_1114).trans sub_1114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1292 : Law1292.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1292_1683).trans sub_1683_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1294 : Law1294.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1294_1287).trans sub_1287_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1296 : Law1296.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1296_2901).trans sub_2901_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1297 : Law1297.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1297_136).trans sub_136_1809).trans sub_1809_1773).trans sub_1773_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1298 : Law1298.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1298_1277).trans sub_1277_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1300 : Law1300.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1300_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1301_eq_556 : Law1301.spectrum = Law556.spectrum :=
  Set.Subset.antisymm (sub_1301_556) ((sub_556_2383).trans sub_2383_1301)

theorem singleton_1302 : Law1302.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1302_1300).trans sub_1300_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1305 : Law1305.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1305_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1306 : Law1306.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1306_1305).trans sub_1305_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1308 : Law1308.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1308_1300).trans sub_1300_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1309 : Law1309.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1309_1305).trans sub_1305_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1310 : Law1310.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1310_1300).trans sub_1300_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1311 : Law1311.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1311_1308).trans sub_1308_1300).trans sub_1300_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1313_eq_1313 : Law1313.spectrum = Law1313.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1314 : Law1314.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1314_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1317 : Law1317.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1317_1087).trans sub_1087_1114).trans sub_1114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1319 : Law1319.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1319_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1321 : Law1321.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1321_1319).trans sub_1319_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1323_eq_1323 : Law1323.spectrum = Law1323.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1324 : Law1324.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1324_1121).trans sub_1121_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1326 : Law1326.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1326_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1327 : Law1327.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1327_1326).trans sub_1326_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1329 : Law1329.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1329_149).trans sub_149_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1330 : Law1330.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1330_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1331 : Law1331.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1331_1330).trans sub_1330_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1333 : Law1333.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1333_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1334_eq_895 : Law1334.spectrum = Law895.spectrum :=
  Set.Subset.antisymm ((sub_1334_2308).trans sub_2308_895) ((sub_895_1571).trans sub_1571_1334)

theorem singleton_1335 : Law1335.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1335_1314).trans sub_1314_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1337 : Law1337.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1337_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1338 : Law1338.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1338_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1339 : Law1339.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1339_1337).trans sub_1337_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1341 : Law1341.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1341_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1342 : Law1342.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1342_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1343 : Law1343.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1343_1341).trans sub_1341_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1345 : Law1345.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1345_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1346 : Law1346.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1346_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1347 : Law1347.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1347_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1348 : Law1348.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1348_1345).trans sub_1345_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1350 : Law1350.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1350_3109).trans sub_3109_874).trans sub_874_3114).trans sub_3114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1351 : Law1351.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1351_1182).trans sub_1182_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1352 : Law1352.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1352_1277).trans sub_1277_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1354 : Law1354.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1354_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1355_eq_556 : Law1355.spectrum = Law556.spectrum :=
  Set.Subset.antisymm (sub_1355_556) (sub_556_1355)

theorem singleton_1356 : Law1356.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1356_1354).trans sub_1354_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1359 : Law1359.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1359_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1360 : Law1360.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1360_1359).trans sub_1359_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1362 : Law1362.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1362_1354).trans sub_1354_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1363 : Law1363.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1363_1319).trans sub_1319_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1364 : Law1364.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1364_1283).trans sub_1283_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1365 : Law1365.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1365_1364).trans sub_1364_1283).trans sub_1283_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1367 : Law1367.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1367_678).trans sub_678_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1368_eq_898 : Law1368.spectrum = Law898.spectrum :=
  Set.Subset.antisymm (((sub_1368_1587).trans sub_1587_2116).trans sub_2116_898) ((sub_898_2316).trans sub_2316_1368)

theorem singleton_1369 : Law1369.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1369_1287).trans sub_1287_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1371 : Law1371.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1371_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1372 : Law1372.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1372_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1373 : Law1373.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1373_1371).trans sub_1371_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1375 : Law1375.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1375_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1376 : Law1376.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1376_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1377 : Law1377.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1377_1375).trans sub_1375_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1379 : Law1379.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1379_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1380 : Law1380.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1380_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1381 : Law1381.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1381_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1382 : Law1382.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1382_1379).trans sub_1379_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1384_eq_887 : Law1384.spectrum = Law887.spectrum :=
  Set.Subset.antisymm ((sub_1384_2319).trans sub_2319_887) (sub_887_1384)

theorem singleton_1385 : Law1385.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1385_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1386 : Law1386.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1386_1277).trans sub_1277_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1388 : Law1388.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1388_1412).trans sub_1412_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1389 : Law1389.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1389_1329).trans sub_1329_149).trans sub_149_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1390 : Law1390.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1390_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1392 : Law1392.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1392_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1393 : Law1393.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1393_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1394 : Law1394.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1394_1392).trans sub_1392_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1396 : Law1396.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1396_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1397 : Law1397.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1397_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1398 : Law1398.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1398_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1399 : Law1399.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1399_1390).trans sub_1390_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1401 : Law1401.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1401_1333).trans sub_1333_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1402 : Law1402.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1402_1385).trans sub_1385_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1403 : Law1403.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_1403_1367).trans sub_1367_678).trans sub_678_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1404 : Law1404.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1404_1298).trans sub_1298_1277).trans sub_1277_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1406 : Law1406.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1406_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1407 : Law1407.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1407_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1408 : Law1408.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1408_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1409 : Law1409.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1409_1406).trans sub_1406_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1411 : Law1411.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1411_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1412 : Law1412.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1412_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1413 : Law1413.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1413_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1414 : Law1414.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1414_1411).trans sub_1411_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1416 : Law1416.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1416_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1417 : Law1417.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1417_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1418 : Law1418.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1418_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1419 : Law1419.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1419_1416).trans sub_1416_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1421 : Law1421.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1421_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1422 : Law1422.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1422_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1423 : Law1423.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1423_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1424 : Law1424.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1424_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1425 : Law1425.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1425_1421).trans sub_1421_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1480_eq_1480 : Law1480.spectrum = Law1480.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem spectrum_1483_eq_1483 : Law1483.spectrum = Law1483.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem spectrum_1485_eq_1485 : Law1485.spectrum = Law1485.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem spectrum_1486_eq_1486 : Law1486.spectrum = Law1486.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem spectrum_1487_eq_168 : Law1487.spectrum = Law168.spectrum :=
  Set.Subset.antisymm (sub_1487_168) (sub_168_1487)

theorem spectrum_1489_eq_1489 : Law1489.spectrum = Law1489.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1490 : Law1490.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1490_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1493 : Law1493.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1493_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1495 : Law1495.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1495_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1496_eq_1496 : Law1496.spectrum = Law1496.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1497 : Law1497.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1497_1493).trans sub_1493_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1499 : Law1499.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1500 : Law1500.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1500_498).trans sub_498_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1501 : Law1501.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1501_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1503 : Law1503.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1503_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1505 : Law1505.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1505_1503).trans sub_1503_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1508 : Law1508.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1508_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1509 : Law1509.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1509_1508).trans sub_1508_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1511 : Law1511.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1511_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1512 : Law1512.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_1512_1500).trans sub_1500_498).trans sub_498_71).trans sub_71_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1513 : Law1513.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1513_1503).trans sub_1503_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1514 : Law1514.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1514_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1516_eq_1516 : Law1516.spectrum = Law1516.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1517 : Law1517.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1520 : Law1520.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1520_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1522 : Law1522.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_1522_2920).trans sub_2920_1151).trans sub_1151_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1524 : Law1524.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1524_1517).trans sub_1517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1526_eq_1526 : Law1526.spectrum = Law1526.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1527 : Law1527.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1527_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1529 : Law1529.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1529_150).trans sub_150_147).trans sub_147_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1530 : Law1530.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1532 : Law1532.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1532_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1533 : Law1533.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1533_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1534 : Law1534.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1534_1527).trans sub_1527_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1536 : Law1536.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1536_2729).trans sub_2729_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1537_eq_887 : Law1537.spectrum = Law887.spectrum :=
  Set.Subset.antisymm (sub_1537_887) (sub_887_1537)

theorem singleton_1538 : Law1538.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_1538_1536).trans sub_1536_2729).trans sub_2729_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1540 : Law1540.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1540_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1541 : Law1541.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1541_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1542 : Law1542.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1542_1530).trans sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1544 : Law1544.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1545 : Law1545.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1545_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1546 : Law1546.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1546_1530).trans sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1548 : Law1548.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1548_1544).trans sub_1544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1549 : Law1549.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1549_1541).trans sub_1541_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1550 : Law1550.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1550_1533).trans sub_1533_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1551 : Law1551.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1551_1524).trans sub_1524_1517).trans sub_1517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1553 : Law1553.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1553_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1554 : Law1554.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1554_471).trans sub_471_472).trans sub_472_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1555 : Law1555.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1555_1517).trans sub_1517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1557 : Law1557.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1557_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1559 : Law1559.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1559_1557).trans sub_1557_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1562 : Law1562.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1562_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1563 : Law1563.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1563_1562).trans sub_1562_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1565 : Law1565.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((((sub_1565_1522).trans sub_1522_2920).trans sub_2920_1151).trans sub_1151_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1566 : Law1566.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_1566_1554).trans sub_1554_471).trans sub_471_472).trans sub_472_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1567 : Law1567.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1567_1557).trans sub_1557_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1568 : Law1568.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1568_1559).trans sub_1559_1557).trans sub_1557_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1570 : Law1570.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1570_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1571_eq_895 : Law1571.spectrum = Law895.spectrum :=
  Set.Subset.antisymm ((sub_1571_2308).trans sub_2308_895) (sub_895_1571)

theorem singleton_1572 : Law1572.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1572_1527).trans sub_1527_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1574 : Law1574.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1574_1529).trans sub_1529_150).trans sub_150_147).trans sub_147_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1575 : Law1575.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1575_1529).trans sub_1529_150).trans sub_150_147).trans sub_147_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1576 : Law1576.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1576_1530).trans sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1578 : Law1578.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1578_1576).trans sub_1576_1530).trans sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1579 : Law1579.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1579_1529).trans sub_1529_150).trans sub_150_147).trans sub_147_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1580 : Law1580.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1580_1530).trans sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1582 : Law1582.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1582_1616).trans sub_1616_1541).trans sub_1541_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1583 : Law1583.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1583_1582).trans sub_1582_1616).trans sub_1616_1541).trans sub_1541_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1584 : Law1584.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1584_1533).trans sub_1533_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1585 : Law1585.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1585_1497).trans sub_1497_1493).trans sub_1493_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1587_eq_898 : Law1587.spectrum = Law898.spectrum :=
  Set.Subset.antisymm ((sub_1587_2116).trans sub_2116_898) (((sub_898_2316).trans sub_2316_1368).trans sub_1368_1587)

theorem singleton_1588 : Law1588.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1588_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1589 : Law1589.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1589_1527).trans sub_1527_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1591 : Law1591.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1591_1529).trans sub_1529_150).trans sub_150_147).trans sub_147_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1592 : Law1592.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1592_1529).trans sub_1529_150).trans sub_150_147).trans sub_147_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1593 : Law1593.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1593_1530).trans sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1595 : Law1595.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1595_1593).trans sub_1593_1530).trans sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1596 : Law1596.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1596_1529).trans sub_1529_150).trans sub_150_147).trans sub_147_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1597 : Law1597.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1597_1530).trans sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1599 : Law1599.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1599_1617).trans sub_1617_1542).trans sub_1542_1530).trans sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1600 : Law1600.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1600_1532).trans sub_1532_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1601 : Law1601.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1601_1533).trans sub_1533_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1602 : Law1602.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1602_1534).trans sub_1534_1527).trans sub_1527_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1604 : Law1604.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1604_1553).trans sub_1553_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1605 : Law1605.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_1605_1554).trans sub_1554_471).trans sub_471_472).trans sub_472_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1606 : Law1606.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1606_1570).trans sub_1570_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1607 : Law1607.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1607_1555).trans sub_1555_1517).trans sub_1517_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1609 : Law1609.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1609_1601).trans sub_1601_1533).trans sub_1533_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1610 : Law1610.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1610_1609).trans sub_1609_1601).trans sub_1601_1533).trans sub_1533_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1611 : Law1611.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1611_1541).trans sub_1541_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1612 : Law1612.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1612_1505).trans sub_1505_1503).trans sub_1503_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1614 : Law1614.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1614_1612).trans sub_1612_1505).trans sub_1505_1503).trans sub_1503_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1615 : Law1615.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1615_1540).trans sub_1540_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1616 : Law1616.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1616_1541).trans sub_1541_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1617 : Law1617.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1617_1542).trans sub_1542_1530).trans sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1619 : Law1619.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1619_1597).trans sub_1597_1530).trans sub_1530_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1620 : Law1620.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1620_1544).trans sub_1544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1621 : Law1621.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1621_1545).trans sub_1545_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1622 : Law1622.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1622_1509).trans sub_1509_1508).trans sub_1508_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1624 : Law1624.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1624_1604).trans sub_1604_1553).trans sub_1553_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1625 : Law1625.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1625_1548).trans sub_1548_1544).trans sub_1544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1626 : Law1626.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1626_1600).trans sub_1600_1532).trans sub_1532_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1627 : Law1627.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1627_1513).trans sub_1513_1503).trans sub_1503_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1628 : Law1628.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1628_1585).trans sub_1585_1497).trans sub_1497_1493).trans sub_1493_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1683 : Law1683.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1683_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1685_eq_1685 : Law1685.spectrum = Law1685.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1686 : Law1686.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1686_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1688 : Law1688.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1688_2806).trans sub_2806_1351).trans sub_1351_1182).trans sub_1182_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1689 : Law1689.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1689_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1690 : Law1690.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1690_1686).trans sub_1686_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1692_eq_1692 : Law1692.spectrum = Law1692.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1693 : Law1693.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1693_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1696 : Law1696.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1696_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1698 : Law1698.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1698_555).trans sub_555_874).trans sub_874_3114).trans sub_3114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1700 : Law1700.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1700_1696).trans sub_1696_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1702 : Law1702.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1702_747).trans sub_747_544).trans sub_544_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1703 : Law1703.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1703_794).trans sub_794_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1704 : Law1704.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1704_1693).trans sub_1693_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1706 : Law1706.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1706_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1708 : Law1708.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1708_1696).trans sub_1696_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1710_eq_695 : Law1710.spectrum = Law695.spectrum :=
  Set.Subset.antisymm (sub_1710_695) ((sub_695_1993).trans sub_1993_1710)

theorem singleton_1711 : Law1711.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1711_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1712 : Law1712.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1712_1711).trans sub_1711_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1714 : Law1714.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1714_2906).trans sub_2906_494).trans sub_494_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1715 : Law1715.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1715_1711).trans sub_1711_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1716 : Law1716.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1716_1711).trans sub_1711_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1717 : Law1717.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1717_1690).trans sub_1690_1686).trans sub_1686_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1719_eq_1719 : Law1719.spectrum = Law1719.spectrum :=
  Set.Subset.antisymm (Subspectral.refl _) (Subspectral.refl _)

theorem singleton_1720 : Law1720.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1723 : Law1723.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1723_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1725 : Law1725.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1725_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1727 : Law1727.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1727_1720).trans sub_1720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1730 : Law1730.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1730_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1732 : Law1732.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1732_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1733 : Law1733.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1733_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1735 : Law1735.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1735_1732).trans sub_1732_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1736 : Law1736.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1736_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1737 : Law1737.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1737_1730).trans sub_1730_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1739 : Law1739.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1739_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1741 : Law1741.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1741_1730).trans sub_1730_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1743 : Law1743.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1743_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1744 : Law1744.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1744_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1745 : Law1745.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1745_1744).trans sub_1744_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1747 : Law1747.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1747_1745).trans sub_1745_1744).trans sub_1744_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1748 : Law1748.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1748_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1749 : Law1749.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1749_1748).trans sub_1748_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1751 : Law1751.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1751_1739).trans sub_1739_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1752 : Law1752.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1752_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1753 : Law1753.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1753_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1754 : Law1754.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1754_1752).trans sub_1752_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1756 : Law1756.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1756_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1757 : Law1757.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1757_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1758 : Law1758.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1758_1720).trans sub_1720_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1760 : Law1760.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1760_681).trans sub_681_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1762 : Law1762.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1762_1686).trans sub_1686_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1764_eq_546 : Law1764.spectrum = Law546.spectrum :=
  Set.Subset.antisymm ((sub_1764_1967).trans sub_1967_546) ((sub_546_1967).trans sub_1967_1764)

theorem singleton_1765 : Law1765.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1765_187).trans sub_187_482).trans sub_482_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1766 : Law1766.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1766_1723).trans sub_1723_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1768 : Law1768.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1768_1756).trans sub_1756_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1769 : Law1769.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1769_1725).trans sub_1725_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1770 : Law1770.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1770_1689).trans sub_1689_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1771 : Law1771.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1771_1690).trans sub_1690_1686).trans sub_1686_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1773 : Law1773.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1773_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1775 : Law1775.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1775_1693).trans sub_1693_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1777 : Law1777.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1777_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1778 : Law1778.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1778_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1779 : Law1779.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1779_1778).trans sub_1778_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1781 : Law1781.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1781_1779).trans sub_1779_1778).trans sub_1778_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1782 : Law1782.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1782_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1783 : Law1783.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1783_1693).trans sub_1693_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1785 : Law1785.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1785_1773).trans sub_1773_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1786 : Law1786.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1786_1778).trans sub_1778_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1787 : Law1787.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1787_1782).trans sub_1782_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1788 : Law1788.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1788_1775).trans sub_1775_1693).trans sub_1693_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1790_eq_546 : Law1790.spectrum = Law546.spectrum :=
  Set.Subset.antisymm ((sub_1790_949).trans sub_949_546) ((sub_546_962).trans sub_962_1790)

theorem singleton_1791 : Law1791.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1791_1588).trans sub_1588_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1792 : Law1792.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1792_1730).trans sub_1730_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1794 : Law1794.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1794_1788).trans sub_1788_1775).trans sub_1775_1693).trans sub_1693_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1795 : Law1795.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1795_1735).trans sub_1735_1732).trans sub_1732_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1796 : Law1796.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1796_1795).trans sub_1795_1735).trans sub_1735_1732).trans sub_1732_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1798 : Law1798.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_1798_193).trans sub_193_171).trans sub_171_1497).trans sub_1497_1493).trans sub_1493_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1799 : Law1799.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1799_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1800 : Law1800.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1800_1733).trans sub_1733_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1802 : Law1802.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1802_1800).trans sub_1800_1733).trans sub_1733_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1803 : Law1803.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1803_1795).trans sub_1795_1735).trans sub_1735_1732).trans sub_1732_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1804 : Law1804.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1804_1736).trans sub_1736_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1805 : Law1805.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1805_1737).trans sub_1737_1730).trans sub_1730_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1807 : Law1807.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1807_1739).trans sub_1739_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1808 : Law1808.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1808_1739).trans sub_1739_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1809 : Law1809.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1809_1773).trans sub_1773_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1810 : Law1810.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1810_1775).trans sub_1775_1693).trans sub_1693_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1812 : Law1812.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1812_1760).trans sub_1760_681).trans sub_681_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1813 : Law1813.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1813_1778).trans sub_1778_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1814 : Law1814.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1814_1785).trans sub_1785_1773).trans sub_1773_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1815 : Law1815.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1815_1813).trans sub_1813_1778).trans sub_1778_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1817 : Law1817.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1817_1815).trans sub_1815_1813).trans sub_1813_1778).trans sub_1778_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1818 : Law1818.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1818_1743).trans sub_1743_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1819 : Law1819.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1819_1818).trans sub_1818_1743).trans sub_1743_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1820 : Law1820.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1820_1704).trans sub_1704_1693).trans sub_1693_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1822 : Law1822.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1822_1820).trans sub_1820_1704).trans sub_1704_1693).trans sub_1693_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1823 : Law1823.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1823_1757).trans sub_1757_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1824 : Law1824.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1824_1748).trans sub_1748_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1825 : Law1825.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1825_1712).trans sub_1712_1711).trans sub_1711_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1827 : Law1827.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1827_1825).trans sub_1825_1712).trans sub_1712_1711).trans sub_1711_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1828 : Law1828.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1828_1751).trans sub_1751_1739).trans sub_1739_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1829 : Law1829.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1829_1752).trans sub_1752_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1830 : Law1830.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1830_1753).trans sub_1753_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1831 : Law1831.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1831_1754).trans sub_1754_1752).trans sub_1752_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1886 : Law1886.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1886_2108).trans sub_2108_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1888_eq_1719 : Law1888.spectrum = Law1719.spectrum :=
  Set.Subset.antisymm (sub_1888_1719) (sub_1719_1888)

theorem singleton_1889 : Law1889.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1891 : Law1891.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1891_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1892 : Law1892.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1892_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1893 : Law1893.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1893_1891).trans sub_1891_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1895_eq_1692 : Law1895.spectrum = Law1692.spectrum :=
  Set.Subset.antisymm (sub_1895_1692) (sub_1692_1895)

theorem singleton_1896 : Law1896.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1896_2918).trans sub_2918_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1899 : Law1899.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1899_1889).trans sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1901 : Law1901.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1901_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1903 : Law1903.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1903_1901).trans sub_1901_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1905 : Law1905.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1905_471).trans sub_471_472).trans sub_472_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1906 : Law1906.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1906_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1907 : Law1907.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1907_1906).trans sub_1906_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1909 : Law1909.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1909_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1911 : Law1911.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1911_1889).trans sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1913_eq_546 : Law1913.spectrum = Law546.spectrum :=
  Set.Subset.antisymm (((sub_1913_1790).trans sub_1790_949).trans sub_949_546) (((sub_546_962).trans sub_962_1790).trans sub_1790_1913)

theorem singleton_1914 : Law1914.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1914_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1915 : Law1915.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1915_1914).trans sub_1914_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1917 : Law1917.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1917_1891).trans sub_1891_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1918 : Law1918.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1918_1906).trans sub_1906_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1919 : Law1919.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1919_1914).trans sub_1914_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1920 : Law1920.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1920_1911).trans sub_1911_1889).trans sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1922_eq_1685 : Law1922.spectrum = Law1685.spectrum :=
  Set.Subset.antisymm (sub_1922_1685) (sub_1685_1922)

theorem singleton_1923 : Law1923.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1923_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1926 : Law1926.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1926_173).trans sub_173_3230).trans sub_3230_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1928 : Law1928.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1928_3009).trans sub_3009_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1930 : Law1930.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1930_1923).trans sub_1923_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1933 : Law1933.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1933_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1935 : Law1935.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1935_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1936 : Law1936.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1936_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1938 : Law1938.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1938_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1939 : Law1939.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1939_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1940 : Law1940.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1940_1936).trans sub_1936_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1942 : Law1942.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1942_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1944 : Law1944.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1944_1933).trans sub_1933_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1946 : Law1946.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1946_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1947 : Law1947.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1947_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1948 : Law1948.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1948_1946).trans sub_1946_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1950 : Law1950.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1950_195).trans sub_195_1818).trans sub_1818_1743).trans sub_1743_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1951 : Law1951.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1951_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1952 : Law1952.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1952_1951).trans sub_1951_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1954 : Law1954.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1954_1928).trans sub_1928_3009).trans sub_3009_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1955 : Law1955.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1955_1947).trans sub_1947_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1956 : Law1956.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1956_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1957 : Law1957.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1957_1956).trans sub_1956_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1959 : Law1959.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1959_884).trans sub_884_2295).trans sub_2295_2508).trans sub_2508_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1960 : Law1960.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1960_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1961 : Law1961.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1961_1960).trans sub_1960_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1963 : Law1963.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1963_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1965 : Law1965.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1965_1889).trans sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1967_eq_546 : Law1967.spectrum = Law546.spectrum :=
  Set.Subset.antisymm (sub_1967_546) (sub_546_1967)

theorem singleton_1968 : Law1968.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1968_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1969 : Law1969.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1969_1968).trans sub_1968_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1971 : Law1971.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1971_1891).trans sub_1891_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1972 : Law1972.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1972_1960).trans sub_1960_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1973 : Law1973.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1973_1892).trans sub_1892_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1974 : Law1974.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1974_1965).trans sub_1965_1889).trans sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1976 : Law1976.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1976_3119).trans sub_3119_2772).trans sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1978 : Law1978.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1978_1933).trans sub_1933_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1980 : Law1980.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1980_1935).trans sub_1935_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1981 : Law1981.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1981_1980).trans sub_1980_1935).trans sub_1935_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1982 : Law1982.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_1982_1981).trans sub_1981_1980).trans sub_1980_1935).trans sub_1935_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1984 : Law1984.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1984_2006).trans sub_2006_1998).trans sub_1998_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1985 : Law1985.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1985_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1986 : Law1986.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1986_1948).trans sub_1948_1946).trans sub_1946_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1988 : Law1988.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1988_1901).trans sub_1901_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1989 : Law1989.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1989_1988).trans sub_1988_1901).trans sub_1901_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1990 : Law1990.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1990_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1991 : Law1991.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1991_1990).trans sub_1990_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_1993_eq_695 : Law1993.spectrum = Law695.spectrum :=
  Set.Subset.antisymm ((sub_1993_1710).trans sub_1710_695) (sub_695_1993)

theorem singleton_1994 : Law1994.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1994_2922).trans sub_2922_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1995 : Law1995.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1995_1933).trans sub_1933_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1997 : Law1997.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_1997_2021).trans sub_2021_1985).trans sub_1985_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1998 : Law1998.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_1998_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_1999 : Law1999.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_1999_1889).trans sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2001 : Law2001.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2001_200).trans sub_200_183).trans sub_183_1829).trans sub_1829_1752).trans sub_1752_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2002 : Law2002.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2002_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2003 : Law2003.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2003_1936).trans sub_1936_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2005 : Law2005.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2005_2023).trans sub_2023_1907).trans sub_1907_1906).trans sub_1906_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2006 : Law2006.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2006_1998).trans sub_1998_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2007 : Law2007.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2007_1939).trans sub_1939_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2008 : Law2008.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2008_1999).trans sub_1999_1889).trans sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2010 : Law2010.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2010_1942).trans sub_1942_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2011 : Law2011.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2011_1994).trans sub_1994_2922).trans sub_2922_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2012 : Law2012.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2012_1994).trans sub_1994_2922).trans sub_2922_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2013 : Law2013.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2013_1907).trans sub_1907_1906).trans sub_1906_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2015 : Law2015.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2015_1909).trans sub_1909_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2016 : Law2016.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2016_1998).trans sub_1998_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2017 : Law2017.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2017_1947).trans sub_1947_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2018 : Law2018.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2018_2015).trans sub_2015_1909).trans sub_1909_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2020 : Law2020.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2020_2031).trans sub_2031_2016).trans sub_2016_1998).trans sub_1998_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2021 : Law2021.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2021_1985).trans sub_1985_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2022 : Law2022.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2022_1906).trans sub_1906_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2023 : Law2023.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2023_1907).trans sub_1907_1906).trans sub_1906_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2025 : Law2025.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2025_2003).trans sub_2003_1936).trans sub_1936_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2026 : Law2026.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2026_1981).trans sub_1981_1980).trans sub_1980_1935).trans sub_1935_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2027 : Law2027.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2027_1914).trans sub_1914_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2028 : Law2028.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2028_1915).trans sub_1915_1914).trans sub_1914_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2030 : Law2030.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2030_2008).trans sub_2008_1999).trans sub_1999_1889).trans sub_1889_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2031 : Law2031.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2031_2016).trans sub_2016_1998).trans sub_1998_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2032 : Law2032.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2032_1918).trans sub_1918_1906).trans sub_1906_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2033 : Law2033.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2033_1956).trans sub_1956_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2034 : Law2034.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2034_1957).trans sub_1957_1956).trans sub_1956_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2089_eq_1480 : Law2089.spectrum = Law1480.spectrum :=
  Set.Subset.antisymm (sub_2089_1480) (sub_1480_2089)

theorem spectrum_2091_eq_1516 : Law2091.spectrum = Law1516.spectrum :=
  Set.Subset.antisymm (sub_2091_1516) (sub_1516_2091)

theorem singleton_2092 : Law2092.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2092_3141).trans sub_3141_3179).trans sub_3179_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2094 : Law2094.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2094_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2095 : Law2095.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2095_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2096 : Law2096.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2096_2094).trans sub_2094_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2098_eq_1489 : Law2098.spectrum = Law1489.spectrum :=
  Set.Subset.antisymm (sub_2098_1489) (sub_1489_2098)

theorem singleton_2099 : Law2099.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2099_3162).trans sub_3162_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2101_eq_1526 : Law2101.spectrum = Law1526.spectrum :=
  Set.Subset.antisymm (sub_2101_1526) (sub_1526_2101)

theorem singleton_2102 : Law2102.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2102_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2104 : Law2104.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2105_eq_887 : Law2105.spectrum = Law887.spectrum :=
  Set.Subset.antisymm ((sub_2105_1537).trans sub_1537_887) (sub_887_2105)

theorem singleton_2106 : Law2106.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2106_1732).trans sub_1732_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2108 : Law2108.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2108_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2109 : Law2109.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2109_2772).trans sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2110 : Law2110.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2110_2108).trans sub_2108_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2112 : Law2112.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2112_995).trans sub_995_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2113_eq_895 : Law2113.spectrum = Law895.spectrum :=
  Set.Subset.antisymm ((sub_2113_2308).trans sub_2308_895) ((sub_895_1571).trans sub_1571_2113)

theorem singleton_2114 : Law2114.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2114_2112).trans sub_2112_995).trans sub_995_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2116_eq_898 : Law2116.spectrum = Law898.spectrum :=
  Set.Subset.antisymm (sub_2116_898) ((sub_898_2316).trans sub_2316_2116)

theorem singleton_2117 : Law2117.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2117_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2118 : Law2118.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2118_2117).trans sub_2117_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2120 : Law2120.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2120_2094).trans sub_2094_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2121 : Law2121.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2121_2117).trans sub_2117_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2122 : Law2122.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2122_2112).trans sub_2112_995).trans sub_995_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2123 : Law2123.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2123_2106).trans sub_2106_1732).trans sub_1732_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2126_eq_1486 : Law2126.spectrum = Law1486.spectrum :=
  Set.Subset.antisymm (sub_2126_1486) (sub_1486_2126)

theorem singleton_2129 : Law2129.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2129_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2131 : Law2131.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2131_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2133 : Law2133.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2133_2129).trans sub_2129_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2136 : Law2136.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2136_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2138 : Law2138.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2138_254).trans sub_254_237).trans sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2139 : Law2139.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2139_2138).trans sub_2138_254).trans sub_254_237).trans sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2141 : Law2141.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2141_2138).trans sub_2138_254).trans sub_254_237).trans sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2142 : Law2142.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2143 : Law2143.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2143_2142).trans sub_2142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2145 : Law2145.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2145_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2146_eq_1496 : Law2146.spectrum = Law1496.spectrum :=
  Set.Subset.antisymm (sub_2146_1496) (sub_1496_2146)

theorem singleton_2147 : Law2147.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2147_2136).trans sub_2136_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2149 : Law2149.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2149_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2150 : Law2150.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2150_2138).trans sub_2138_254).trans sub_254_237).trans sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2151 : Law2151.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2151_2149).trans sub_2149_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2153 : Law2153.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2153_2138).trans sub_2138_254).trans sub_254_237).trans sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2154 : Law2154.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2155 : Law2155.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2155_2154).trans sub_2154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2157 : Law2157.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2157_2155).trans sub_2155_2154).trans sub_2154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2158 : Law2158.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2158_2154).trans sub_2154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2159 : Law2159.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2159_2154).trans sub_2154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2160 : Law2160.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2160_2133).trans sub_2133_2129).trans sub_2129_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2162_eq_1485 : Law2162.spectrum = Law1485.spectrum :=
  Set.Subset.antisymm (sub_2162_1485) (sub_1485_2162)

theorem spectrum_2163_eq_1483 : Law2163.spectrum = Law1483.spectrum :=
  Set.Subset.antisymm (sub_2163_1483) (sub_1483_2163)

theorem spectrum_2164_eq_168 : Law2164.spectrum = Law168.spectrum :=
  Set.Subset.antisymm (sub_2164_168) (sub_168_2164)

theorem singleton_2166 : Law2166.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2166_876).trans sub_876_2984).trans sub_2984_792).trans sub_792_1923).trans sub_1923_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2168 : Law2168.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2168_2092).trans sub_2092_3141).trans sub_3141_3179).trans sub_3179_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2171 : Law2171.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2171_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2172 : Law2172.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2172_2129).trans sub_2129_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2174 : Law2174.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((((sub_2174_2166).trans sub_2166_876).trans sub_876_2984).trans sub_2984_792).trans sub_792_1923).trans sub_1923_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2175 : Law2175.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2175_2131).trans sub_2131_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2176 : Law2176.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2176_2095).trans sub_2095_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2177 : Law2177.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2177_2133).trans sub_2133_2129).trans sub_2129_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2179 : Law2179.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2179_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2181 : Law2181.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2181_2099).trans sub_2099_3162).trans sub_3162_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2183 : Law2183.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2183_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2184 : Law2184.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2184_2138).trans sub_2138_254).trans sub_254_237).trans sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2185 : Law2185.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2185_2183).trans sub_2183_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2187 : Law2187.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2187_2209).trans sub_2209_2205).trans sub_2205_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2188 : Law2188.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2188_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2189 : Law2189.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2189_2188).trans sub_2188_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2191 : Law2191.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2191_2189).trans sub_2189_2188).trans sub_2188_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2192 : Law2192.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2192_2188).trans sub_2188_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2193 : Law2193.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2193_2188).trans sub_2188_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2194 : Law2194.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2194_2185).trans sub_2185_2183).trans sub_2183_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2197 : Law2197.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2197_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2198 : Law2198.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2198_2136).trans sub_2136_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2200 : Law2200.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2200_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2201 : Law2201.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2201_2138).trans sub_2138_254).trans sub_254_237).trans sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2202 : Law2202.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2202_2200).trans sub_2200_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2204 : Law2204.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2204_2229).trans sub_2229_2205).trans sub_2205_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2205 : Law2205.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2205_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2206 : Law2206.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2206_2205).trans sub_2205_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2208 : Law2208.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2208_2206).trans sub_2206_2205).trans sub_2205_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2209 : Law2209.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2209_2205).trans sub_2205_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2210 : Law2210.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2210_2142).trans sub_2142_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2211 : Law2211.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2211_2198).trans sub_2198_2136).trans sub_2136_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2213 : Law2213.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2213_2108).trans sub_2108_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2214 : Law2214.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2214_2145).trans sub_2145_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2215 : Law2215.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2215_2179).trans sub_2179_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2216 : Law2216.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2216_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2218 : Law2218.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2218_2200).trans sub_2200_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2219 : Law2219.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2219_2157).trans sub_2157_2155).trans sub_2155_2154).trans sub_2154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2220 : Law2220.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2220_2191).trans sub_2191_2189).trans sub_2189_2188).trans sub_2188_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2221 : Law2221.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2221_2218).trans sub_2218_2200).trans sub_2200_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2223 : Law2223.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2223_2234).trans sub_2234_2214).trans sub_2214_2145).trans sub_2145_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2224 : Law2224.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2224_2149).trans sub_2149_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2225 : Law2225.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2225_2205).trans sub_2205_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2226 : Law2226.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2226_2151).trans sub_2151_2149).trans sub_2149_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2228 : Law2228.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2228_2226).trans sub_2226_2151).trans sub_2151_2149).trans sub_2149_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2229 : Law2229.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2229_2205).trans sub_2205_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2230 : Law2230.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2230_2117).trans sub_2117_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2231 : Law2231.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2231_2118).trans sub_2118_2117).trans sub_2117_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2233 : Law2233.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2233_2120).trans sub_2120_2094).trans sub_2094_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2234 : Law2234.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2234_2214).trans sub_2214_2145).trans sub_2145_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2235 : Law2235.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2235_2121).trans sub_2121_2117).trans sub_2117_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2236 : Law2236.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2236_2176).trans sub_2176_2095).trans sub_2095_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2237 : Law2237.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2237_2123).trans sub_2123_2106).trans sub_2106_1732).trans sub_1732_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2292 : Law2292.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2292_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2294_eq_1313 : Law2294.spectrum = Law1313.spectrum :=
  Set.Subset.antisymm (sub_2294_1313) (sub_1313_2294)

theorem singleton_2295 : Law2295.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2295_2508).trans sub_2508_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2297 : Law2297.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2297_538).trans sub_538_2772).trans sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2298 : Law2298.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2298_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2299 : Law2299.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2299_2292).trans sub_2292_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2301_eq_1286 : Law2301.spectrum = Law1286.spectrum :=
  Set.Subset.antisymm (sub_2301_1286) (sub_1286_2301)

theorem singleton_2302 : Law2302.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2302_223).trans sub_223_1903).trans sub_1903_1901).trans sub_1901_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2304_eq_1323 : Law2304.spectrum = Law1323.spectrum :=
  Set.Subset.antisymm (sub_2304_1323) (sub_1323_2304)

theorem singleton_2305 : Law2305.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2305_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2307 : Law2307.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2307_2921).trans sub_2921_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2308_eq_895 : Law2308.spectrum = Law895.spectrum :=
  Set.Subset.antisymm (sub_2308_895) ((sub_895_1571).trans sub_1571_2308)

theorem singleton_2309 : Law2309.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2309_2302).trans sub_2302_223).trans sub_223_1903).trans sub_1903_1901).trans sub_1901_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2311 : Law2311.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2311_668).trans sub_668_2108).trans sub_2108_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2312 : Law2312.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2312_2523).trans sub_2523_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2313 : Law2313.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2313_2292).trans sub_2292_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2315 : Law2315.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2315_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2316_eq_898 : Law2316.spectrum = Law898.spectrum :=
  Set.Subset.antisymm ((sub_2316_2116).trans sub_2116_898) (sub_898_2316)

theorem singleton_2317 : Law2317.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2317_2305).trans sub_2305_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2319_eq_887 : Law2319.spectrum = Law887.spectrum :=
  Set.Subset.antisymm (sub_2319_887) ((sub_887_1384).trans sub_1384_2319)

theorem singleton_2320 : Law2320.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2320_2523).trans sub_2523_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2321 : Law2321.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2321_2292).trans sub_2292_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2323 : Law2323.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2323_2315).trans sub_2315_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2324 : Law2324.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2324_2527).trans sub_2527_2510).trans sub_2510_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2325 : Law2325.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2325_2298).trans sub_2298_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2326 : Law2326.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2326_2299).trans sub_2299_2292).trans sub_2292_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2328_eq_1279 : Law2328.spectrum = Law1279.spectrum :=
  Set.Subset.antisymm (sub_2328_1279) (sub_1279_2328)

theorem singleton_2329 : Law2329.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2329_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2332 : Law2332.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2332_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2334 : Law2334.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2334_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2336 : Law2336.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2336_2329).trans sub_2329_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2339 : Law2339.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2339_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2341 : Law2341.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2341_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2342 : Law2342.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2342_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2344 : Law2344.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2344_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2345 : Law2345.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2345_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2346 : Law2346.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2346_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2348 : Law2348.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2348_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2350 : Law2350.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2350_2339).trans sub_2339_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2352 : Law2352.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2352_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2353 : Law2353.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2353_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2354 : Law2354.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2354_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2356 : Law2356.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2356_2354).trans sub_2354_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2357 : Law2357.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2357_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2358 : Law2358.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2358_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2360 : Law2360.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2360_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2361 : Law2361.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2361_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2362 : Law2362.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2362_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2363 : Law2363.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2363_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2365 : Law2365.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2365_3127).trans sub_3127_794).trans sub_794_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2366 : Law2366.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2366_2603).trans sub_2603_2577).trans sub_2577_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2367 : Law2367.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2367_2329).trans sub_2329_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2369 : Law2369.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2369_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2370_eq_556 : Law2370.spectrum = Law556.spectrum :=
  Set.Subset.antisymm ((sub_2370_1355).trans sub_1355_556) ((sub_556_1355).trans sub_1355_2370)

theorem singleton_2371 : Law2371.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2371_2332).trans sub_2332_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2374 : Law2374.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2374_2603).trans sub_2603_2577).trans sub_2577_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2375 : Law2375.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2375_2332).trans sub_2332_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2377 : Law2377.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2377_2334).trans sub_2334_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2378 : Law2378.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2378_2334).trans sub_2334_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2379 : Law2379.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2379_2369).trans sub_2369_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2380 : Law2380.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2380_2336).trans sub_2336_2329).trans sub_2329_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2382 : Law2382.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2382_1886).trans sub_1886_2108).trans sub_2108_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2383_eq_556 : Law2383.spectrum = Law556.spectrum :=
  Set.Subset.antisymm ((sub_2383_1131).trans sub_1131_556) (sub_556_2383)

theorem singleton_2384 : Law2384.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2384_2339).trans sub_2339_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2386 : Law2386.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2386_237).trans sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2387 : Law2387.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2387_2386).trans sub_2386_237).trans sub_237_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2388 : Law2388.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2388_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2390 : Law2390.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2390_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2391 : Law2391.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2391_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2392 : Law2392.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2392_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2394 : Law2394.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2394_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2395 : Law2395.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2395_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2396 : Law2396.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2396_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2397 : Law2397.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2397_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2400 : Law2400.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2400_2603).trans sub_2603_2577).trans sub_2577_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2401 : Law2401.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2401_2339).trans sub_2339_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2403 : Law2403.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2403_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2404 : Law2404.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2404_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2405 : Law2405.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2405_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2407 : Law2407.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2407_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2408 : Law2408.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2408_2341).trans sub_2341_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2409 : Law2409.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2409_2342).trans sub_2342_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2411 : Law2411.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2411_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2412 : Law2412.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2412_2344).trans sub_2344_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2413 : Law2413.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2413_2345).trans sub_2345_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2414 : Law2414.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2414_2346).trans sub_2346_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2416 : Law2416.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2416_2348).trans sub_2348_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2417 : Law2417.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2417_2348).trans sub_2348_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2418 : Law2418.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2418_2312).trans sub_2312_2523).trans sub_2523_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2419 : Law2419.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2419_2350).trans sub_2350_2339).trans sub_2339_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2421 : Law2421.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2421_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2422 : Law2422.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2422_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2423 : Law2423.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2423_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2424 : Law2424.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2424_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2426 : Law2426.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2426_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2427 : Law2427.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2427_2352).trans sub_2352_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2428 : Law2428.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2428_2353).trans sub_2353_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2429 : Law2429.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2429_2354).trans sub_2354_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2431 : Law2431.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2431_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2432 : Law2432.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2432_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2433 : Law2433.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2433_2357).trans sub_2357_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2434 : Law2434.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2434_2358).trans sub_2358_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2436 : Law2436.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2436_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2437 : Law2437.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2437_2360).trans sub_2360_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2438 : Law2438.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2438_2361).trans sub_2361_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2439 : Law2439.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2439_2362).trans sub_2362_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2440 : Law2440.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2440_2363).trans sub_2363_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2495 : Law2495.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2495_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2497_eq_1110 : Law2497.spectrum = Law1110.spectrum :=
  Set.Subset.antisymm (sub_2497_1110) (sub_1110_2497)

theorem singleton_2498 : Law2498.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2498_2305).trans sub_2305_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2500 : Law2500.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2500_291).trans sub_291_67).trans sub_67_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2501 : Law2501.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2501_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2502 : Law2502.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2502_2495).trans sub_2495_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2504_eq_1083 : Law2504.spectrum = Law1083.spectrum :=
  Set.Subset.antisymm (sub_2504_1083) (sub_1083_2504)

theorem singleton_2505 : Law2505.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2505_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2508 : Law2508.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2508_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2510 : Law2510.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2510_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2511_eq_556 : Law2511.spectrum = Law556.spectrum :=
  Set.Subset.antisymm ((sub_2511_1131).trans sub_1131_556) ((sub_556_1131).trans sub_1131_2511)

theorem singleton_2512 : Law2512.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2512_2505).trans sub_2505_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2514 : Law2514.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2514_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2515 : Law2515.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2515_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2516 : Law2516.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2516_2495).trans sub_2495_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2518 : Law2518.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2518_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2520 : Law2520.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2520_2518).trans sub_2518_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2523 : Law2523.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2523_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2524 : Law2524.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2524_2495).trans sub_2495_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2526 : Law2526.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2526_2500).trans sub_2500_291).trans sub_291_67).trans sub_67_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2527 : Law2527.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2527_2510).trans sub_2510_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2528 : Law2528.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2528_2501).trans sub_2501_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2529 : Law2529.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2529_2502).trans sub_2502_2495).trans sub_2495_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2531_eq_1076 : Law2531.spectrum = Law1076.spectrum :=
  Set.Subset.antisymm (sub_2531_1076) (sub_1076_2531)

theorem singleton_2532 : Law2532.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2532_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2535 : Law2535.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2535_30).trans sub_30_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2537 : Law2537.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2537_2922).trans sub_2922_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2539 : Law2539.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2539_2532).trans sub_2532_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2542 : Law2542.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2542_30).trans sub_30_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2544 : Law2544.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2545 : Law2545.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2545_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2547 : Law2547.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2547_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2548 : Law2548.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2548_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2549 : Law2549.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2549_2547).trans sub_2547_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2551 : Law2551.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2551_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2553 : Law2553.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2553_2551).trans sub_2551_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2555 : Law2555.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2555_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2556 : Law2556.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2556_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2557 : Law2557.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2557_2555).trans sub_2555_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2559 : Law2559.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2559_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2560 : Law2560.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2560_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2561 : Law2561.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2561_2560).trans sub_2560_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2563 : Law2563.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2563_2561).trans sub_2561_2560).trans sub_2560_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2564 : Law2564.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2564_2560).trans sub_2560_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2565 : Law2565.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2565_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2566 : Law2566.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2566_2565).trans sub_2565_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2568 : Law2568.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2568_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2569 : Law2569.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2569_240).trans sub_240_2824).trans sub_2824_2718).trans sub_2718_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2570 : Law2570.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2570_2532).trans sub_2532_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2572 : Law2572.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2572_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2574 : Law2574.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2574_2535).trans sub_2535_30).trans sub_30_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2577 : Law2577.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2577_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2578 : Law2578.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2578_2535).trans sub_2535_30).trans sub_30_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2580 : Law2580.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2580_2537).trans sub_2537_2922).trans sub_2922_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2581 : Law2581.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2581_2537).trans sub_2537_2922).trans sub_2922_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2582 : Law2582.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2582_2501).trans sub_2501_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2583 : Law2583.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2583_2539).trans sub_2539_2532).trans sub_2532_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2585 : Law2585.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2585_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2586_eq_546 : Law2586.spectrum = Law546.spectrum :=
  Set.Subset.antisymm (((sub_2586_1790).trans sub_1790_949).trans sub_949_546) ((sub_546_1967).trans sub_1967_2586)

theorem singleton_2587 : Law2587.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2587_2542).trans sub_2542_30).trans sub_30_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2589 : Law2589.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2589_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2590 : Law2590.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2590_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2591 : Law2591.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2591_2589).trans sub_2589_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2593 : Law2593.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2593_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2594 : Law2594.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2594_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2595 : Law2595.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2595_2594).trans sub_2594_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2597 : Law2597.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2597_2593).trans sub_2593_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2598 : Law2598.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2598_2594).trans sub_2594_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2599 : Law2599.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2599_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2600 : Law2600.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2600_2599).trans sub_2599_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2603 : Law2603.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2603_2577).trans sub_2577_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2604 : Law2604.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2604_2603).trans sub_2603_2577).trans sub_2577_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2606 : Law2606.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2606_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2607 : Law2607.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2607_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2608 : Law2608.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2608_2606).trans sub_2606_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2610 : Law2610.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2610_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2611 : Law2611.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2611_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2612 : Law2612.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2612_2611).trans sub_2611_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2614 : Law2614.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2614_2612).trans sub_2612_2611).trans sub_2611_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2615 : Law2615.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2615_2547).trans sub_2547_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2616 : Law2616.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2616_2548).trans sub_2548_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2617 : Law2617.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2617_2549).trans sub_2549_2547).trans sub_2547_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2619 : Law2619.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2619_2551).trans sub_2551_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2620 : Law2620.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2620_2551).trans sub_2551_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2621 : Law2621.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2621_2515).trans sub_2515_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2622 : Law2622.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2622_2621).trans sub_2621_2515).trans sub_2515_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2624 : Law2624.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2624_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2625 : Law2625.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2625_2624).trans sub_2624_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2626 : Law2626.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2626_2625).trans sub_2625_2624).trans sub_2624_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2627 : Law2627.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2627_2624).trans sub_2624_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2629 : Law2629.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2629_2627).trans sub_2627_2624).trans sub_2624_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2630 : Law2630.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2630_2555).trans sub_2555_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2631 : Law2631.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2631_2611).trans sub_2611_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2632 : Law2632.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2632_2557).trans sub_2557_2555).trans sub_2555_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2634 : Law2634.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2634_2559).trans sub_2559_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2635 : Law2635.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2635_2611).trans sub_2611_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2636 : Law2636.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2636_2560).trans sub_2560_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2637 : Law2637.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2637_2561).trans sub_2561_2560).trans sub_2560_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2639 : Law2639.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2639_2637).trans sub_2637_2561).trans sub_2561_2560).trans sub_2560_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2640 : Law2640.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2640_2598).trans sub_2598_2594).trans sub_2594_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2641 : Law2641.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2641_2615).trans sub_2615_2547).trans sub_2547_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2642 : Law2642.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2642_2565).trans sub_2565_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2643 : Law2643.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2643_2566).trans sub_2566_2565).trans sub_2565_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2698 : Law2698.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2698_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2700_eq_907 : Law2700.spectrum = Law907.spectrum :=
  Set.Subset.antisymm (sub_2700_907) (sub_907_2700)

theorem singleton_2701 : Law2701.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2701_675).trans sub_675_674).trans sub_674_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2703 : Law2703.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2703_187).trans sub_187_482).trans sub_482_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2704 : Law2704.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2704_69).trans sub_69_292).trans sub_292_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2705 : Law2705.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2705_2698).trans sub_2698_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2707_eq_880 : Law2707.spectrum = Law880.spectrum :=
  Set.Subset.antisymm (sub_2707_880) (sub_880_2707)

theorem singleton_2708 : Law2708.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2708_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2711 : Law2711.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2711_30).trans sub_30_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2713 : Law2713.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2713_693).trans sub_693_681).trans sub_681_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2715 : Law2715.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2715_2708).trans sub_2708_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2717 : Law2717.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2718 : Law2718.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2718_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2719 : Law2719.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2719_2708).trans sub_2708_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2721 : Law2721.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2721_2906).trans sub_2906_494).trans sub_494_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2722_eq_546 : Law2722.spectrum = Law546.spectrum :=
  Set.Subset.antisymm ((sub_2722_962).trans sub_962_546) ((sub_546_962).trans sub_962_2722)

theorem singleton_2723 : Law2723.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2723_2711).trans sub_2711_30).trans sub_30_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2726 : Law2726.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2726_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2727 : Law2727.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2727_2726).trans sub_2726_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2729 : Law2729.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2729_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2730 : Law2730.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2730_2726).trans sub_2726_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2731 : Law2731.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2731_2726).trans sub_2726_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2732 : Law2732.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2732_2705).trans sub_2705_2698).trans sub_2698_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2734_eq_873 : Law2734.spectrum = Law873.spectrum :=
  Set.Subset.antisymm (sub_2734_873) (sub_873_2734)

theorem singleton_2735 : Law2735.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2735_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2738 : Law2738.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2738_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2740 : Law2740.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2740_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2742 : Law2742.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2742_2738).trans sub_2738_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2744_eq_883 : Law2744.spectrum = Law883.spectrum :=
  Set.Subset.antisymm (sub_2744_883) (sub_883_2744)

theorem singleton_2745 : Law2745.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2745_30).trans sub_30_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2747 : Law2747.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2747_285).trans sub_285_299).trans sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2748 : Law2748.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2748_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2750 : Law2750.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2750_297).trans sub_297_285).trans sub_285_299).trans sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2751 : Law2751.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2751_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2752 : Law2752.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2752_2751).trans sub_2751_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2754 : Law2754.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2754_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2755_eq_887 : Law2755.spectrum = Law887.spectrum :=
  Set.Subset.antisymm (sub_2755_887) (sub_887_2755)

theorem singleton_2756 : Law2756.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2756_2754).trans sub_2754_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2758 : Law2758.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2758_2752).trans sub_2752_2751).trans sub_2751_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2759 : Law2759.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2759_289).trans sub_289_285).trans sub_285_299).trans sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2760 : Law2760.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2760_2738).trans sub_2738_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2762 : Law2762.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2762_2760).trans sub_2760_2738).trans sub_2738_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2763 : Law2763.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2763_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2764 : Law2764.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2764_2762).trans sub_2762_2760).trans sub_2760_2738).trans sub_2738_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2766 : Law2766.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2766_2754).trans sub_2754_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2767 : Law2767.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((((sub_2767_2759).trans sub_2759_289).trans sub_289_285).trans sub_285_299).trans sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2768 : Law2768.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2768_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2769 : Law2769.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2769_2768).trans sub_2768_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2771 : Law2771.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2771_751).trans sub_751_2932).trans sub_2932_1689).trans sub_1689_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2772 : Law2772.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2773 : Law2773.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2773_2698).trans sub_2698_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2775 : Law2775.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2775_2382).trans sub_2382_1886).trans sub_1886_2108).trans sub_2108_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2776_eq_546 : Law2776.spectrum = Law546.spectrum :=
  Set.Subset.antisymm ((sub_2776_949).trans sub_949_546) ((((sub_546_962).trans sub_962_1790).trans sub_1790_949).trans sub_949_2776)

theorem singleton_2777 : Law2777.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2777_2738).trans sub_2738_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2780 : Law2780.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2780_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2781 : Law2781.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2781_2698).trans sub_2698_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2783 : Law2783.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2783_2740).trans sub_2740_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2784 : Law2784.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2784_2740).trans sub_2740_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2785 : Law2785.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2785_2780).trans sub_2780_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2786 : Law2786.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2786_2773).trans sub_2773_2698).trans sub_2698_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2788 : Law2788.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2788_538).trans sub_538_2772).trans sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2789_eq_895 : Law2789.spectrum = Law895.spectrum :=
  Set.Subset.antisymm (sub_2789_895) (sub_895_2789)

theorem singleton_2790 : Law2790.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2790_2708).trans sub_2708_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2792 : Law2792.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2792_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2793 : Law2793.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2793_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2794 : Law2794.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2794_2793).trans sub_2793_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2796 : Law2796.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2796_2818).trans sub_2818_2810).trans sub_2810_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2797 : Law2797.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2797_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2798 : Law2798.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2798_2708).trans sub_2708_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2800 : Law2800.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2800_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2801 : Law2801.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2801_2797).trans sub_2797_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2802 : Law2802.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2802_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2803 : Law2803.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2803_2800).trans sub_2800_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2805_eq_898 : Law2805.spectrum = Law898.spectrum :=
  Set.Subset.antisymm (sub_2805_898) (sub_898_2805)

theorem singleton_2806 : Law2806.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2806_1351).trans sub_1351_1182).trans sub_1182_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2807 : Law2807.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2807_2806).trans sub_2806_1351).trans sub_1351_1182).trans sub_1182_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2809 : Law2809.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2809_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2810 : Law2810.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2810_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2811 : Law2811.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2811_2809).trans sub_2809_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2813 : Law2813.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2813_2838).trans sub_2838_2793).trans sub_2793_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2814 : Law2814.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2814_2813).trans sub_2813_2838).trans sub_2838_2793).trans sub_2793_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2815 : Law2815.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2815_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2817 : Law2817.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2817_2835).trans sub_2835_2815).trans sub_2815_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2818 : Law2818.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2818_2810).trans sub_2810_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2819 : Law2819.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2819_2751).trans sub_2751_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2820 : Law2820.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2820_2819).trans sub_2819_2751).trans sub_2751_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2822 : Law2822.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2822_2754).trans sub_2754_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2823 : Law2823.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2823_2754).trans sub_2754_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2824 : Law2824.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2824_2718).trans sub_2718_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2825 : Law2825.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2825_2790).trans sub_2790_2708).trans sub_2708_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2827 : Law2827.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2827_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2828 : Law2828.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2828_2810).trans sub_2810_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2829 : Law2829.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2829_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2830 : Law2830.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2830_2827).trans sub_2827_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2832 : Law2832.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2832_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2833 : Law2833.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2833_2797).trans sub_2797_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2834 : Law2834.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2834_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2835 : Law2835.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2835_2815).trans sub_2815_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2837 : Law2837.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2837_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2838 : Law2838.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2838_2793).trans sub_2793_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2839 : Law2839.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2839_2726).trans sub_2726_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2840 : Law2840.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2840_2837).trans sub_2837_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2842 : Law2842.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2842_2832).trans sub_2832_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2843 : Law2843.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2843_2766).trans sub_2766_2754).trans sub_2754_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2844 : Law2844.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2844_2800).trans sub_2800_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2845 : Law2845.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2845_2768).trans sub_2768_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2846 : Law2846.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2846_2769).trans sub_2769_2768).trans sub_2768_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2900_eq_667 : Law2900.spectrum = Law667.spectrum :=
  Set.Subset.antisymm (sub_2900_667) (sub_667_2900)

theorem singleton_2901 : Law2901.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2901_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2903_eq_704 : Law2903.spectrum = Law704.spectrum :=
  Set.Subset.antisymm (sub_2903_704) (sub_704_2903)

theorem singleton_2904 : Law2904.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2904_30).trans sub_30_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2906 : Law2906.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2906_494).trans sub_494_465).trans sub_465_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2907 : Law2907.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2907_668).trans sub_668_2108).trans sub_2108_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2908 : Law2908.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2908_3148).trans sub_3148_3146).trans sub_3146_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2910_eq_677 : Law2910.spectrum = Law677.spectrum :=
  Set.Subset.antisymm (sub_2910_677) (sub_677_2910)

theorem singleton_2911 : Law2911.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2914 : Law2914.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2914_2932).trans sub_2932_1689).trans sub_1689_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2916 : Law2916.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2916_2010).trans sub_2010_1942).trans sub_1942_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2918 : Law2918.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2918_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2920 : Law2920.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2920_1151).trans sub_1151_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2921 : Law2921.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2921_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2922 : Law2922.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2922_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2924 : Law2924.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2924_1147).trans sub_1147_69).trans sub_69_292).trans sub_292_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2926 : Law2926.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2926_2904).trans sub_2904_30).trans sub_30_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2928_eq_556 : Law2928.spectrum = Law556.spectrum :=
  Set.Subset.antisymm ((sub_2928_749).trans sub_749_556) ((sub_556_775).trans sub_775_2928)

theorem singleton_2929 : Law2929.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2929_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2930 : Law2930.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2930_2929).trans sub_2929_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2932 : Law2932.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2932_1689).trans sub_1689_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2933 : Law2933.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2933_3136).trans sub_3136_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2934 : Law2934.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((((sub_2934_2924).trans sub_2924_1147).trans sub_1147_69).trans sub_69_292).trans sub_292_1123).trans sub_1123_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2935 : Law2935.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2935_2930).trans sub_2930_2929).trans sub_2929_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2937_eq_670 : Law2937.spectrum = Law670.spectrum :=
  Set.Subset.antisymm (sub_2937_670) (sub_670_2937)

theorem singleton_2938 : Law2938.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2938_2922).trans sub_2922_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2941 : Law2941.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2941_2984).trans sub_2984_792).trans sub_792_1923).trans sub_1923_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2943 : Law2943.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2943_908).trans sub_908_291).trans sub_291_67).trans sub_67_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2945 : Law2945.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2945_1317).trans sub_1317_1087).trans sub_1087_1114).trans sub_1114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2948 : Law2948.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2948_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2950 : Law2950.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2951 : Law2951.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2951_2950).trans sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2953 : Law2953.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2953_2950).trans sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2954 : Law2954.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2954_2950).trans sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2955 : Law2955.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2955_2948).trans sub_2948_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2957 : Law2957.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2957_1698).trans sub_1698_555).trans sub_555_874).trans sub_874_3114).trans sub_3114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2959 : Law2959.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2959_2938).trans sub_2938_2922).trans sub_2922_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2961 : Law2961.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2961_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2962 : Law2962.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2962_2950).trans sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2963 : Law2963.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2963_2961).trans sub_2961_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2965 : Law2965.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2965_2950).trans sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2966 : Law2966.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2966_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2967 : Law2967.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2967_2966).trans sub_2966_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2969 : Law2969.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2969_2967).trans sub_2967_2966).trans sub_2966_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2970 : Law2970.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2970_3032).trans sub_3032_3003).trans sub_3003_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2971 : Law2971.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2971_2954).trans sub_2954_2950).trans sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2972 : Law2972.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2972_2955).trans sub_2955_2948).trans sub_2948_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2974 : Law2974.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2974_1683).trans sub_1683_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2975 : Law2975.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_2975_2974).trans sub_2974_1683).trans sub_1683_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2976 : Law2976.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2976_2901).trans sub_2901_1499).trans sub_1499_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2978 : Law2978.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2978_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2980 : Law2980.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2980_2978).trans sub_2978_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_2982_eq_556 : Law2982.spectrum = Law556.spectrum :=
  Set.Subset.antisymm ((sub_2982_749).trans sub_749_556) (sub_556_2982)

theorem singleton_2983 : Law2983.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2983_1294).trans sub_1294_1287).trans sub_1287_468).trans sub_468_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2984 : Law2984.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2984_792).trans sub_792_1923).trans sub_1923_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2986 : Law2986.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((((sub_2986_2943).trans sub_2943_908).trans sub_908_291).trans sub_291_67).trans sub_67_2544).trans sub_2544_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2987 : Law2987.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2987_3190).trans sub_3190_3146).trans sub_3146_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2988 : Law2988.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2988_2978).trans sub_2978_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2989 : Law2989.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2989_2980).trans sub_2980_2978).trans sub_2978_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2991 : Law2991.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_2991_1706).trans sub_1706_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2993 : Law2993.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2993_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2995 : Law2995.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2996 : Law2996.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2996_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2997 : Law2997.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_2997_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_2999 : Law2999.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_2999_2950).trans sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3000 : Law3000.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3000_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3001 : Law3001.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3001_3000).trans sub_3000_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3003 : Law3003.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3003_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3004 : Law3004.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3004_3003).trans sub_3003_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3005 : Law3005.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3005_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3006 : Law3006.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3006_3003).trans sub_3003_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_3008_eq_695 : Law3008.spectrum = Law695.spectrum :=
  Set.Subset.antisymm (sub_3008_695) (sub_695_3008)

theorem singleton_3009 : Law3009.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3009_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3010 : Law3010.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3010_2948).trans sub_2948_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3012 : Law3012.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3012_3036).trans sub_3036_2961).trans sub_2961_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3013 : Law3013.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3013_2953).trans sub_2953_2950).trans sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3014 : Law3014.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3014_3012).trans sub_3012_3036).trans sub_3036_2961).trans sub_2961_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3016 : Law3016.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3016_3041).trans sub_3041_3017).trans sub_3017_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3017 : Law3017.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3017_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3018 : Law3018.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3018_3017).trans sub_3017_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3020 : Law3020.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3020_3038).trans sub_3038_2963).trans sub_2963_2961).trans sub_2961_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3021 : Law3021.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3021_2953).trans sub_2953_2950).trans sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3022 : Law3022.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3022_2954).trans sub_2954_2950).trans sub_2950_7).trans sub_7_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3023 : Law3023.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3023_2955).trans sub_2955_2948).trans sub_2948_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3025 : Law3025.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_3025_2920).trans sub_2920_1151).trans sub_1151_689).trans sub_689_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3026 : Law3026.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3026_3009).trans sub_3009_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3027 : Law3027.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3027_3119).trans sub_3119_2772).trans sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3028 : Law3028.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3028_2993).trans sub_2993_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3030 : Law3030.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3030_303).trans sub_303_299).trans sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3031 : Law3031.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_3031_3030).trans sub_3030_303).trans sub_303_299).trans sub_299_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3032 : Law3032.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3032_3003).trans sub_3003_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3033 : Law3033.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3033_2980).trans sub_2980_2978).trans sub_2978_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3035 : Law3035.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3035_3046).trans sub_3046_3036).trans sub_3036_2961).trans sub_2961_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3036 : Law3036.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3036_2961).trans sub_2961_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3037 : Law3037.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3037_3036).trans sub_3036_2961).trans sub_2961_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3038 : Law3038.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3038_2963).trans sub_2963_2961).trans sub_2961_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3040 : Law3040.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3040_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3041 : Law3041.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3041_3017).trans sub_3017_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3042 : Law3042.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3042_2929).trans sub_2929_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3043 : Law3043.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3043_3040).trans sub_3040_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3045 : Law3045.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3045_3040).trans sub_3040_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3046 : Law3046.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3046_3036).trans sub_3036_2961).trans sub_2961_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3047 : Law3047.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3047_3003).trans sub_3003_2995).trans sub_2995_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3048 : Law3048.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3048_3042).trans sub_3042_2929).trans sub_2929_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3049 : Law3049.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3049_3043).trans sub_3043_3040).trans sub_3040_304).trans sub_304_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3104 : Law3104.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_3106_eq_501 : Law3106.spectrum = Law501.spectrum :=
  Set.Subset.antisymm (sub_3106_501) (sub_501_3106)

theorem singleton_3107 : Law3107.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3107_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3109 : Law3109.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3109_874).trans sub_874_3114).trans sub_3114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3110 : Law3110.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3110_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3111 : Law3111.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3111_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_3113_eq_474 : Law3113.spectrum = Law474.spectrum :=
  Set.Subset.antisymm (sub_3113_474) (sub_474_3113)

theorem singleton_3114 : Law3114.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3117 : Law3117.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3117_1886).trans sub_1886_2108).trans sub_2108_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3119 : Law3119.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3119_2772).trans sub_2772_485).trans sub_485_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3121 : Law3121.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3121_3114).trans sub_3114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3123 : Law3123.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3123_507).trans sub_507_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3124 : Law3124.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3125 : Law3125.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3125_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3127 : Law3127.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3127_794).trans sub_794_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_3128_eq_556 : Law3128.spectrum = Law556.spectrum :=
  Set.Subset.antisymm (sub_3128_556) (sub_556_3128)

theorem singleton_3129 : Law3129.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3129_3107).trans sub_3107_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3132 : Law3132.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3132_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3133 : Law3133.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3133_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3135 : Law3135.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3135_3127).trans sub_3127_794).trans sub_794_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3136 : Law3136.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3136_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3137 : Law3137.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3137_3110).trans sub_3110_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3138 : Law3138.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3138_3111).trans sub_3111_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_3140_eq_467 : Law3140.spectrum = Law467.spectrum :=
  Set.Subset.antisymm (sub_3140_467) (sub_467_3140)

theorem singleton_3141 : Law3141.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3141_3179).trans sub_3179_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3144 : Law3144.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3144_1490).trans sub_1490_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3146 : Law3146.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3146_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3148 : Law3148.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3148_3146).trans sub_3146_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3151 : Law3151.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_3151_683).trans sub_683_1942).trans sub_1942_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3153 : Law3153.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3153_22).trans sub_22_18).trans sub_18_1799).trans sub_1799_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3154 : Law3154.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3156 : Law3156.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3156_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3157 : Law3157.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3157_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3158 : Law3158.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3158_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3160 : Law3160.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_3160_886).trans sub_886_3109).trans sub_3109_874).trans sub_874_3114).trans sub_3114_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_3161_eq_481 : Law3161.spectrum = Law481.spectrum :=
  Set.Subset.antisymm (sub_3161_481) (sub_481_3161)

theorem singleton_3162 : Law3162.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3162_293).trans sub_293_6).trans sub_6_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3164 : Law3164.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3164_3158).trans sub_3158_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3165 : Law3165.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3165_3164).trans sub_3164_3158).trans sub_3158_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3166 : Law3166.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3166_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3168 : Law3168.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3168_3166).trans sub_3166_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3169 : Law3169.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3169_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3170 : Law3170.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3170_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3172 : Law3172.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3172_3246).trans sub_3246_3170).trans sub_3170_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3173 : Law3173.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3173_3235).trans sub_3235_3216).trans sub_3216_3156).trans sub_3156_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3174 : Law3174.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3174_3208).trans sub_3208_3198).trans sub_3198_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3175 : Law3175.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3175_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3177 : Law3177.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_3177_1765).trans sub_1765_187).trans sub_187_482).trans sub_482_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3178 : Law3178.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3178_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3179 : Law3179.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3179_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3181 : Law3181.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3181_2717).trans sub_2717_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3183 : Law3183.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_3183_3144).trans sub_3144_1490).trans sub_1490_890).trans sub_890_2911).trans sub_2911_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem spectrum_3185_eq_546 : Law3185.spectrum = Law546.spectrum :=
  Set.Subset.antisymm (sub_3185_546) (sub_546_3185)

theorem singleton_3186 : Law3186.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3186_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3187 : Law3187.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3187_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3189 : Law3189.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3189_3146).trans sub_3146_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3190 : Law3190.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3190_3146).trans sub_3146_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3191 : Law3191.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3191_3110).trans sub_3110_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3192 : Law3192.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3192_3187).trans sub_3187_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3194 : Law3194.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3194_884).trans sub_884_2295).trans sub_2295_2508).trans sub_2508_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3196 : Law3196.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_3196_3194).trans sub_3194_884).trans sub_884_2295).trans sub_2295_2508).trans sub_2508_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3198 : Law3198.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3198_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3199 : Law3199.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3199_3198).trans sub_3198_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3200 : Law3200.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3200_3198).trans sub_3198_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3202 : Law3202.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3202_3224).trans sub_3224_3156).trans sub_3156_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3203 : Law3203.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3203_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3204 : Law3204.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3204_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3206 : Law3206.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3206_3198).trans sub_3198_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3207 : Law3207.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3207_3206).trans sub_3206_3198).trans sub_3198_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3208 : Law3208.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3208_3198).trans sub_3198_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3209 : Law3209.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3209_3158).trans sub_3158_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3212 : Law3212.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3212_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3213 : Law3213.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3213_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3215 : Law3215.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3215_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3216 : Law3216.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3216_3156).trans sub_3156_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3217 : Law3217.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3217_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3219 : Law3219.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3219_3217).trans sub_3217_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3220 : Law3220.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (sub_3220_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3221 : Law3221.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3221_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3223 : Law3223.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3223_3215).trans sub_3215_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3224 : Law3224.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3224_3156).trans sub_3156_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3225 : Law3225.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3225_3157).trans sub_3157_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3226 : Law3226.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3226_3213).trans sub_3213_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3228 : Law3228.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_3228_961).trans sub_961_3026).trans sub_3026_3009).trans sub_3009_475).trans sub_475_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3229 : Law3229.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_3229_3135).trans sub_3135_3127).trans sub_3127_794).trans sub_794_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3230 : Law3230.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3230_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3231 : Law3231.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3231_3125).trans sub_3125_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3233 : Law3233.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3233_3127).trans sub_3127_794).trans sub_794_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3234 : Law3234.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((((sub_3234_3233).trans sub_3233_3127).trans sub_3127_794).trans sub_794_688).trans sub_688_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3235 : Law3235.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3235_3216).trans sub_3216_3156).trans sub_3156_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3236 : Law3236.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3236_3129).trans sub_3129_3107).trans sub_3107_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3238 : Law3238.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3238_3236).trans sub_3236_3129).trans sub_3129_3107).trans sub_3107_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3239 : Law3239.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3239_3186).trans sub_3186_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3240 : Law3240.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3240_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3241 : Law3241.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3241_3166).trans sub_3166_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3243 : Law3243.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3243_3168).trans sub_3168_3166).trans sub_3166_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3244 : Law3244.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3244_3199).trans sub_3199_3198).trans sub_3198_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3245 : Law3245.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3245_3169).trans sub_3169_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3246 : Law3246.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3246_3170).trans sub_3170_3154).trans sub_3154_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3248 : Law3248.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((((sub_3248_3226).trans sub_3226_3213).trans sub_3213_3104).trans sub_3104_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3249 : Law3249.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3249_3190).trans sub_3190_3146).trans sub_3146_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3250 : Law3250.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3250_3240).trans sub_3240_3124).trans sub_3124_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3251 : Law3251.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans (((sub_3251_3191).trans sub_3191_3110).trans sub_3110_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

theorem singleton_3252 : Law3252.spectrum = {1} := by
  apply Set.Subset.antisymm
  · exact Set.Subset.trans ((sub_3252_3175).trans sub_3175_2) spectrum_two.subset
  · intro n hn
    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _

end Spectrum.ImplicationTransfer

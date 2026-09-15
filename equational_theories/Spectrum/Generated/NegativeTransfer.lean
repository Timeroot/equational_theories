import equational_theories.Spectrum.Definability
import equational_theories.Duals.All
import equational_theories.Spectrum.Generated.ImplicationTransfer
import equational_theories.Definability.Cover
import equational_theories.Definability.PositiveStructural
import equational_theories.Definability.PositiveTermsBig
import equational_theories.Definability.PositiveTermsFin
import equational_theories.Generated.MagmaEgg.small._002
import equational_theories.Generated.MagmaEgg.small._005
import equational_theories.Generated.MagmaEgg.small._007
import equational_theories.Generated.MagmaEgg.small._013
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_vu
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_zx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_zy
import equational_theories.Generated.TrivialBruteforce.theorems.Apply2
import equational_theories.Generated.VampireProven.Proofs1
import equational_theories.Generated.VampireProven.Proofs8
import equational_theories.Subgraph

/-! Exclusion propagation selected from existing proved
implication, duality, and definability theorems. No finite search here. -/

open Law Law.MagmaLaw
namespace Spectrum.NegativeTransfer

theorem sub_2_7 : Law2.Subspectral Law7 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law7.models_iff (Fin n) M).mpr ?_⟩
  exact Subgraph.Equation2_implies_Equation7 (Fin n) ((@Law2.models_iff (Fin n) M).mp hM)

theorem sub_7_613 : Law7.Subspectral Law613 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law613.models_iff (Fin n) M).mpr ?_⟩
  exact Apply.Equation7_implies_Equation613 (Fin n) ((@Law7.models_iff (Fin n) M).mp hM)

theorem sub_63_73 : Law63.Subspectral Law73 := by
  exact subspectral_of_termDefinableFin Equation73_termDefinableFromFin_Equation63

theorem sub_66_281 : Law66.Subspectral Law281 := by
  exact (spectrum_eq_of_isDual dual_66).subset

theorem sub_73_1685 : Law73.Subspectral Law1685 := by
  exact subspectral_of_termDefinableFin Equation1685_termDefinableFromFin_Equation73

theorem sub_115_219 : Law115.Subspectral Law219 := by
  exact (spectrum_eq_of_isDual dual_115).subset

theorem sub_118_1685 : Law118.Subspectral Law1685 := by
  exact subspectral_of_termDefinableFin Equation1685_termDefinableFromFin_Equation118

theorem sub_125_1685 : Law125.Subspectral Law1685 := by
  exact subspectral_of_termStructural Equation1685_termStructuralFrom_Equation125

theorem sub_168_167 : Law168.Subspectral Law167 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law167.models_iff (Fin n) M).mpr ?_⟩
  exact SimpleRewrites.Equation168_implies_Equation167 (Fin n) ((@Law168.models_iff (Fin n) M).mp hM)

theorem sub_219_873 : Law219.Subspectral Law873 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_219, spectrum_eq_of_isDual dual_873]
  change Law115.Subspectral Law2734
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2734.models_iff (Fin n) M).mpr ?_⟩
  exact Equation115_implies_Equation2734 (Fin n) ((@Law115.models_iff (Fin n) M).mp hM)

theorem sub_281_2707 : Law281.Subspectral Law2707 := by
  exact subspectral_of_termDefinable Equation2707_termDefinableFrom_Equation281

theorem sub_521_1703 : Law521.Subspectral Law1703 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_521, spectrum_eq_of_isDual dual_1703]
  change Law3127.Subspectral Law1896
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1896.models_iff (Fin n) M).mpr ?_⟩
  exact Equation3127_implies_Equation1896 (Fin n) ((@Law3127.models_iff (Fin n) M).mp hM)

theorem sub_533_521 : Law533.Subspectral Law521 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law521.models_iff (Fin n) M).mpr ?_⟩
  exact SimpleRewrites.Equation533_implies_Equation521 (Fin n) ((@Law533.models_iff (Fin n) M).mp hM)

theorem sub_536_533 : Law536.Subspectral Law533 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law533.models_iff (Fin n) M).mpr ?_⟩
  exact SimpleRewrites.Equation536_implies_Equation533 (Fin n) ((@Law536.models_iff (Fin n) M).mp hM)

theorem sub_546_667 : Law546.Subspectral Law667 := by
  exact subspectral_of_termStructural Equation667_termStructuralFrom_Equation546

theorem sub_556_546 : Law556.Subspectral Law546 := by
  exact subspectral_of_termStructural Equation546_termStructuralFrom_Equation556

theorem sub_613_536 : Law613.Subspectral Law536 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_613, spectrum_eq_of_isDual dual_536]
  change Law3252.Subspectral Law3251
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law3251.models_iff (Fin n) M).mpr ?_⟩
  exact SimpleRewrites.Equation3252_implies_Equation3251 (Fin n) ((@Law3252.models_iff (Fin n) M).mp hM)

theorem sub_695_667 : Law695.Subspectral Law667 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law667.models_iff (Fin n) M).mpr ?_⟩
  exact SimpleRewrites.Equation695_implies_Equation667 (Fin n) ((@Law695.models_iff (Fin n) M).mp hM)

theorem sub_880_219 : Law880.Subspectral Law219 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law219.models_iff (Fin n) M).mpr ?_⟩
  exact Equation880_implies_Equation219 (Fin n) ((@Law880.models_iff (Fin n) M).mp hM)

theorem sub_887_1537 : Law887.Subspectral Law1537 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_887, spectrum_eq_of_isDual dual_1537]
  change Law2755.Subspectral Law2105
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law2105.models_iff (Fin n) M).mpr ?_⟩
  exact Equation2755_implies_Equation2105 (Fin n) ((@Law2755.models_iff (Fin n) M).mp hM)

theorem sub_895_962 : Law895.Subspectral Law962 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law962.models_iff (Fin n) M).mpr ?_⟩
  exact Equation895_implies_Equation962 (Fin n) ((@Law895.models_iff (Fin n) M).mp hM)

theorem sub_898_667 : Law898.Subspectral Law667 := by
  exact subspectral_of_termDefinable Equation667_termDefinableFrom_Equation898

theorem sub_962_546 : Law962.Subspectral Law546 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law546.models_iff (Fin n) M).mpr ?_⟩
  exact Equation962_implies_Equation546 (Fin n) ((@Law962.models_iff (Fin n) M).mp hM)

theorem sub_1323_883 : Law1323.Subspectral Law883 := by
  exact subspectral_of_termDefinableFin Equation883_termDefinableFromFin_Equation1323

theorem sub_1496_481 : Law1496.Subspectral Law481 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law481.models_iff (Fin n) M).mpr ?_⟩
  exact Equation1496_implies_Equation481 (Fin n) ((@Law1496.models_iff (Fin n) M).mp hM)

theorem sub_1526_883 : Law1526.Subspectral Law883 := by
  exact subspectral_of_termDefinableFin Equation883_termDefinableFromFin_Equation1526

theorem sub_1537_695 : Law1537.Subspectral Law695 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law695.models_iff (Fin n) M).mpr ?_⟩
  exact Equation1537_implies_Equation695 (Fin n) ((@Law1537.models_iff (Fin n) M).mp hM)

theorem sub_1692_73 : Law1692.Subspectral Law73 := by
  exact subspectral_of_termStructural Equation73_termStructuralFrom_Equation1692

theorem sub_1703_1692 : Law1703.Subspectral Law1692 := by
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law1692.models_iff (Fin n) M).mpr ?_⟩
  exact SimpleRewrites.Equation1703_implies_Equation1692 (Fin n) ((@Law1703.models_iff (Fin n) M).mp hM)

theorem sub_2707_115 : Law2707.Subspectral Law115 := by
  unfold Subspectral
  rw [spectrum_eq_of_isDual dual_2707, spectrum_eq_of_isDual dual_115]
  change Law880.Subspectral Law219
  apply subspectral_iff_hasModel.mpr
  rintro n ⟨M, hM⟩
  letI := M
  refine ⟨M, (@Law219.models_iff (Fin n) M).mpr ?_⟩
  exact Equation880_implies_Equation219 (Fin n) ((@Law880.models_iff (Fin n) M).mp hM)

theorem basis_route_2_2 : Law2.Subspectral Law1685 := ((((((((sub_2_7).trans sub_7_613).trans sub_613_536).trans sub_536_533).trans sub_533_521).trans sub_521_1703).trans sub_1703_1692).trans sub_1692_73).trans sub_73_1685

theorem basis_route_63_2 : Law63.Subspectral Law1685 := (sub_63_73).trans sub_73_1685

theorem basis_route_63_6 : Law63.Subspectral Law63 := Subspectral.refl _

theorem basis_route_63_10 : Law63.Subspectral Law63 := Subspectral.refl _

theorem basis_route_66_2 : Law66.Subspectral Law873 := ((((sub_66_281).trans sub_281_2707).trans sub_2707_115).trans sub_115_219).trans sub_219_873

theorem basis_route_73_2 : Law73.Subspectral Law1685 := sub_73_1685

theorem basis_route_115_2 : Law115.Subspectral Law873 := (sub_115_219).trans sub_219_873

theorem basis_route_115_6 : Law115.Subspectral Law873 := (sub_115_219).trans sub_219_873

theorem basis_route_118_2 : Law118.Subspectral Law1685 := sub_118_1685

theorem basis_route_125_2 : Law125.Subspectral Law1685 := sub_125_1685

theorem basis_route_167_2 : Law167.Subspectral Law167 := Subspectral.refl _

theorem basis_route_168_2 : Law168.Subspectral Law167 := sub_168_167

theorem basis_route_467_2 : Law467.Subspectral Law467 := Subspectral.refl _

theorem basis_route_467_3 : Law467.Subspectral Law467 := Subspectral.refl _

theorem basis_route_467_4 : Law467.Subspectral Law467 := Subspectral.refl _

theorem basis_route_467_6 : Law467.Subspectral Law467 := Subspectral.refl _

theorem basis_route_474_2 : Law474.Subspectral Law474 := Subspectral.refl _

theorem basis_route_474_4 : Law474.Subspectral Law474 := Subspectral.refl _

theorem basis_route_481_3 : Law481.Subspectral Law481 := Subspectral.refl _

theorem basis_route_481_6 : Law481.Subspectral Law481 := Subspectral.refl _

theorem basis_route_501_2 : Law501.Subspectral Law501 := Subspectral.refl _

theorem basis_route_546_3 : Law546.Subspectral Law667 := sub_546_667

theorem basis_route_556_3 : Law556.Subspectral Law667 := (sub_556_546).trans sub_546_667

theorem basis_route_667_3 : Law667.Subspectral Law667 := Subspectral.refl _

theorem basis_route_670_2 : Law670.Subspectral Law670 := Subspectral.refl _

theorem basis_route_670_3 : Law670.Subspectral Law670 := Subspectral.refl _

theorem basis_route_670_6 : Law670.Subspectral Law670 := Subspectral.refl _

theorem basis_route_670_7 : Law670.Subspectral Law670 := Subspectral.refl _

theorem basis_route_677_2 : Law677.Subspectral Law677 := Subspectral.refl _

theorem basis_route_695_3 : Law695.Subspectral Law667 := sub_695_667

theorem basis_route_704_2 : Law704.Subspectral Law704 := Subspectral.refl _

theorem basis_route_704_3 : Law704.Subspectral Law704 := Subspectral.refl _

theorem basis_route_704_4 : Law704.Subspectral Law704 := Subspectral.refl _

theorem basis_route_704_6 : Law704.Subspectral Law704 := Subspectral.refl _

theorem basis_route_704_9 : Law704.Subspectral Law704 := Subspectral.refl _

theorem basis_route_873_2 : Law873.Subspectral Law873 := Subspectral.refl _

theorem basis_route_873_6 : Law873.Subspectral Law873 := Subspectral.refl _

theorem basis_route_880_2 : Law880.Subspectral Law873 := (sub_880_219).trans sub_219_873

theorem basis_route_883_3 : Law883.Subspectral Law883 := Subspectral.refl _

theorem basis_route_887_3 : Law887.Subspectral Law667 := ((sub_887_1537).trans sub_1537_695).trans sub_695_667

theorem basis_route_895_3 : Law895.Subspectral Law667 := ((sub_895_962).trans sub_962_546).trans sub_546_667

theorem basis_route_898_3 : Law898.Subspectral Law667 := sub_898_667

theorem basis_route_907_2 : Law907.Subspectral Law907 := Subspectral.refl _

theorem basis_route_907_4 : Law907.Subspectral Law907 := Subspectral.refl _

theorem basis_route_907_5 : Law907.Subspectral Law907 := Subspectral.refl _

theorem basis_route_907_6 : Law907.Subspectral Law907 := Subspectral.refl _

theorem basis_route_1076_2 : Law1076.Subspectral Law1076 := Subspectral.refl _

theorem basis_route_1076_3 : Law1076.Subspectral Law1076 := Subspectral.refl _

theorem basis_route_1076_4 : Law1076.Subspectral Law1076 := Subspectral.refl _

theorem basis_route_1076_6 : Law1076.Subspectral Law1076 := Subspectral.refl _

theorem basis_route_1076_7 : Law1076.Subspectral Law1076 := Subspectral.refl _

theorem basis_route_1083_2 : Law1083.Subspectral Law1083 := Subspectral.refl _

theorem basis_route_1110_2 : Law1110.Subspectral Law1110 := Subspectral.refl _

theorem basis_route_1110_3 : Law1110.Subspectral Law1110 := Subspectral.refl _

theorem basis_route_1110_6 : Law1110.Subspectral Law1110 := Subspectral.refl _

theorem basis_route_1279_2 : Law1279.Subspectral Law1279 := Subspectral.refl _

theorem basis_route_1279_3 : Law1279.Subspectral Law1279 := Subspectral.refl _

theorem basis_route_1279_4 : Law1279.Subspectral Law1279 := Subspectral.refl _

theorem basis_route_1279_6 : Law1279.Subspectral Law1279 := Subspectral.refl _

theorem basis_route_1279_9 : Law1279.Subspectral Law1279 := Subspectral.refl _

theorem basis_route_1286_2 : Law1286.Subspectral Law1286 := Subspectral.refl _

theorem basis_route_1286_3 : Law1286.Subspectral Law1286 := Subspectral.refl _

theorem basis_route_1286_4 : Law1286.Subspectral Law1286 := Subspectral.refl _

theorem basis_route_1286_5 : Law1286.Subspectral Law1286 := Subspectral.refl _

theorem basis_route_1286_6 : Law1286.Subspectral Law1286 := Subspectral.refl _

theorem basis_route_1313_2 : Law1313.Subspectral Law1313 := Subspectral.refl _

theorem basis_route_1313_3 : Law1313.Subspectral Law1313 := Subspectral.refl _

theorem basis_route_1313_4 : Law1313.Subspectral Law1313 := Subspectral.refl _

theorem basis_route_1313_6 : Law1313.Subspectral Law1313 := Subspectral.refl _

theorem basis_route_1323_3 : Law1323.Subspectral Law883 := sub_1323_883

theorem basis_route_1480_2 : Law1480.Subspectral Law1480 := Subspectral.refl _

theorem basis_route_1480_3 : Law1480.Subspectral Law1480 := Subspectral.refl _

theorem basis_route_1483_3 : Law1483.Subspectral Law1483 := Subspectral.refl _

theorem basis_route_1483_5 : Law1483.Subspectral Law1483 := Subspectral.refl _

theorem basis_route_1483_6 : Law1483.Subspectral Law1483 := Subspectral.refl _

theorem basis_route_1483_7 : Law1483.Subspectral Law1483 := Subspectral.refl _

theorem basis_route_1485_3 : Law1485.Subspectral Law1485 := Subspectral.refl _

theorem basis_route_1486_2 : Law1486.Subspectral Law1486 := Subspectral.refl _

theorem basis_route_1489_2 : Law1489.Subspectral Law1489 := Subspectral.refl _

theorem basis_route_1489_4 : Law1489.Subspectral Law1489 := Subspectral.refl _

theorem basis_route_1496_3 : Law1496.Subspectral Law481 := sub_1496_481

theorem basis_route_1516_2 : Law1516.Subspectral Law1516 := Subspectral.refl _

theorem basis_route_1516_3 : Law1516.Subspectral Law1516 := Subspectral.refl _

theorem basis_route_1516_4 : Law1516.Subspectral Law1516 := Subspectral.refl _

theorem basis_route_1516_6 : Law1516.Subspectral Law1516 := Subspectral.refl _

theorem basis_route_1526_3 : Law1526.Subspectral Law883 := sub_1526_883

theorem basis_route_1685_2 : Law1685.Subspectral Law1685 := Subspectral.refl _

theorem basis_route_1692_2 : Law1692.Subspectral Law1685 := (sub_1692_73).trans sub_73_1685

theorem basis_route_1719_2 : Law1719.Subspectral Law1719 := Subspectral.refl _

theorem route_2_2 : Law2.Subspectral Law1685 := basis_route_2_2

theorem route_6_2 : Law6.Subspectral Law1685 := (show Law6.Subspectral Law2 from (ImplicationTransfer.singleton_6 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_7_2 : Law7.Subspectral Law1685 := (show Law7.Subspectral Law2 from (ImplicationTransfer.singleton_7 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_15_2 : Law15.Subspectral Law1685 := (show Law15.Subspectral Law2 from (ImplicationTransfer.singleton_15 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_17_2 : Law17.Subspectral Law1685 := (show Law17.Subspectral Law2 from (ImplicationTransfer.singleton_17 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_18_2 : Law18.Subspectral Law1685 := (show Law18.Subspectral Law2 from (ImplicationTransfer.singleton_18 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_20_2 : Law20.Subspectral Law1685 := (show Law20.Subspectral Law2 from (ImplicationTransfer.singleton_20 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_21_2 : Law21.Subspectral Law1685 := (show Law21.Subspectral Law2 from (ImplicationTransfer.singleton_21 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_22_2 : Law22.Subspectral Law1685 := (show Law22.Subspectral Law2 from (ImplicationTransfer.singleton_22 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_30_2 : Law30.Subspectral Law1685 := (show Law30.Subspectral Law2 from (ImplicationTransfer.singleton_30 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_32_2 : Law32.Subspectral Law1685 := (show Law32.Subspectral Law2 from (ImplicationTransfer.singleton_32 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_33_2 : Law33.Subspectral Law1685 := (show Law33.Subspectral Law2 from (ImplicationTransfer.singleton_33 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_35_2 : Law35.Subspectral Law1685 := (show Law35.Subspectral Law2 from (ImplicationTransfer.singleton_35 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_36_2 : Law36.Subspectral Law1685 := (show Law36.Subspectral Law2 from (ImplicationTransfer.singleton_36 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_37_2 : Law37.Subspectral Law1685 := (show Law37.Subspectral Law2 from (ImplicationTransfer.singleton_37 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_63_2 : Law63.Subspectral Law1685 := basis_route_63_2

theorem route_63_6 : Law63.Subspectral Law63 := basis_route_63_6

theorem route_63_10 : Law63.Subspectral Law63 := basis_route_63_10

theorem route_64_2 : Law64.Subspectral Law1685 := (show Law64.Subspectral Law2 from (ImplicationTransfer.singleton_64 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_66_2 : Law66.Subspectral Law873 := basis_route_66_2

theorem route_67_2 : Law67.Subspectral Law1685 := (show Law67.Subspectral Law2 from (ImplicationTransfer.singleton_67 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_69_2 : Law69.Subspectral Law1685 := (show Law69.Subspectral Law2 from (ImplicationTransfer.singleton_69 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_70_2 : Law70.Subspectral Law1685 := (show Law70.Subspectral Law2 from (ImplicationTransfer.singleton_70 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_71_2 : Law71.Subspectral Law1685 := (show Law71.Subspectral Law2 from (ImplicationTransfer.singleton_71 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_73_2 : Law73.Subspectral Law1685 := basis_route_73_2

theorem route_74_2 : Law74.Subspectral Law1685 := (show Law74.Subspectral Law2 from (ImplicationTransfer.singleton_74 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_76_2 : Law76.Subspectral Law1685 := (show Law76.Subspectral Law2 from (ImplicationTransfer.singleton_76 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_77_2 : Law77.Subspectral Law1685 := (show Law77.Subspectral Law2 from (ImplicationTransfer.singleton_77 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_79_2 : Law79.Subspectral Law1685 := (show Law79.Subspectral Law2 from (ImplicationTransfer.singleton_79 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_80_2 : Law80.Subspectral Law1685 := (show Law80.Subspectral Law2 from (ImplicationTransfer.singleton_80 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_81_2 : Law81.Subspectral Law1685 := (show Law81.Subspectral Law2 from (ImplicationTransfer.singleton_81 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_83_2 : Law83.Subspectral Law1685 := (show Law83.Subspectral Law2 from (ImplicationTransfer.singleton_83 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_84_2 : Law84.Subspectral Law1685 := (show Law84.Subspectral Law2 from (ImplicationTransfer.singleton_84 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_85_2 : Law85.Subspectral Law1685 := (show Law85.Subspectral Law2 from (ImplicationTransfer.singleton_85 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_87_2 : Law87.Subspectral Law1685 := (show Law87.Subspectral Law2 from (ImplicationTransfer.singleton_87 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_88_2 : Law88.Subspectral Law1685 := (show Law88.Subspectral Law2 from (ImplicationTransfer.singleton_88 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_89_2 : Law89.Subspectral Law1685 := (show Law89.Subspectral Law2 from (ImplicationTransfer.singleton_89 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_91_2 : Law91.Subspectral Law1685 := (show Law91.Subspectral Law2 from (ImplicationTransfer.singleton_91 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_92_2 : Law92.Subspectral Law1685 := (show Law92.Subspectral Law2 from (ImplicationTransfer.singleton_92 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_93_2 : Law93.Subspectral Law1685 := (show Law93.Subspectral Law2 from (ImplicationTransfer.singleton_93 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_95_2 : Law95.Subspectral Law1685 := (show Law95.Subspectral Law2 from (ImplicationTransfer.singleton_95 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_96_2 : Law96.Subspectral Law1685 := (show Law96.Subspectral Law2 from (ImplicationTransfer.singleton_96 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_97_2 : Law97.Subspectral Law1685 := (show Law97.Subspectral Law2 from (ImplicationTransfer.singleton_97 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_98_2 : Law98.Subspectral Law1685 := (show Law98.Subspectral Law2 from (ImplicationTransfer.singleton_98 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_115_2 : Law115.Subspectral Law873 := basis_route_115_2

theorem route_115_6 : Law115.Subspectral Law873 := basis_route_115_6

theorem route_116_2 : Law116.Subspectral Law1685 := (show Law116.Subspectral Law2 from (ImplicationTransfer.singleton_116 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_118_2 : Law118.Subspectral Law1685 := basis_route_118_2

theorem route_119_2 : Law119.Subspectral Law1685 := (show Law119.Subspectral Law2 from (ImplicationTransfer.singleton_119 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_121_2 : Law121.Subspectral Law1685 := (show Law121.Subspectral Law2 from (ImplicationTransfer.singleton_121 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_122_2 : Law122.Subspectral Law1685 := (show Law122.Subspectral Law2 from (ImplicationTransfer.singleton_122 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_123_2 : Law123.Subspectral Law1685 := (show Law123.Subspectral Law2 from (ImplicationTransfer.singleton_123 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_125_2 : Law125.Subspectral Law1685 := basis_route_125_2

theorem route_126_2 : Law126.Subspectral Law1685 := (show Law126.Subspectral Law2 from (ImplicationTransfer.singleton_126 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_128_2 : Law128.Subspectral Law1685 := (show Law128.Subspectral Law2 from (ImplicationTransfer.singleton_128 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_129_2 : Law129.Subspectral Law1685 := (show Law129.Subspectral Law2 from (ImplicationTransfer.singleton_129 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_131_2 : Law131.Subspectral Law1685 := (show Law131.Subspectral Law2 from (ImplicationTransfer.singleton_131 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_132_2 : Law132.Subspectral Law1685 := (show Law132.Subspectral Law2 from (ImplicationTransfer.singleton_132 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_133_2 : Law133.Subspectral Law1685 := (show Law133.Subspectral Law2 from (ImplicationTransfer.singleton_133 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_135_2 : Law135.Subspectral Law1685 := (show Law135.Subspectral Law2 from (ImplicationTransfer.singleton_135 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_136_2 : Law136.Subspectral Law1685 := (show Law136.Subspectral Law2 from (ImplicationTransfer.singleton_136 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_137_2 : Law137.Subspectral Law1685 := (show Law137.Subspectral Law2 from (ImplicationTransfer.singleton_137 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_139_2 : Law139.Subspectral Law1685 := (show Law139.Subspectral Law2 from (ImplicationTransfer.singleton_139 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_140_2 : Law140.Subspectral Law1685 := (show Law140.Subspectral Law2 from (ImplicationTransfer.singleton_140 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_141_2 : Law141.Subspectral Law1685 := (show Law141.Subspectral Law2 from (ImplicationTransfer.singleton_141 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_143_2 : Law143.Subspectral Law1685 := (show Law143.Subspectral Law2 from (ImplicationTransfer.singleton_143 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_144_2 : Law144.Subspectral Law1685 := (show Law144.Subspectral Law2 from (ImplicationTransfer.singleton_144 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_145_2 : Law145.Subspectral Law1685 := (show Law145.Subspectral Law2 from (ImplicationTransfer.singleton_145 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_147_2 : Law147.Subspectral Law1685 := (show Law147.Subspectral Law2 from (ImplicationTransfer.singleton_147 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_148_2 : Law148.Subspectral Law1685 := (show Law148.Subspectral Law2 from (ImplicationTransfer.singleton_148 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_149_2 : Law149.Subspectral Law1685 := (show Law149.Subspectral Law2 from (ImplicationTransfer.singleton_149 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_150_2 : Law150.Subspectral Law1685 := (show Law150.Subspectral Law2 from (ImplicationTransfer.singleton_150 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_167_2 : Law167.Subspectral Law167 := basis_route_167_2

theorem route_168_2 : Law168.Subspectral Law167 := basis_route_168_2

theorem route_170_2 : Law170.Subspectral Law873 := (show Law170.Subspectral Law66 from (ImplicationTransfer.spectrum_170_eq_66).subset).trans basis_route_66_2

theorem route_171_2 : Law171.Subspectral Law1685 := (show Law171.Subspectral Law2 from (ImplicationTransfer.singleton_171 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_173_2 : Law173.Subspectral Law1685 := (show Law173.Subspectral Law2 from (ImplicationTransfer.singleton_173 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_174_2 : Law174.Subspectral Law1685 := (show Law174.Subspectral Law2 from (ImplicationTransfer.singleton_174 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_175_2 : Law175.Subspectral Law1685 := (show Law175.Subspectral Law2 from (ImplicationTransfer.singleton_175 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_177_2 : Law177.Subspectral Law873 := (show Law177.Subspectral Law66 from (ImplicationTransfer.spectrum_177_eq_66).subset).trans basis_route_66_2

theorem route_178_2 : Law178.Subspectral Law1685 := (show Law178.Subspectral Law2 from (ImplicationTransfer.singleton_178 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_180_2 : Law180.Subspectral Law1685 := (show Law180.Subspectral Law2 from (ImplicationTransfer.singleton_180 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_181_2 : Law181.Subspectral Law1685 := (show Law181.Subspectral Law2 from (ImplicationTransfer.singleton_181 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_183_2 : Law183.Subspectral Law1685 := (show Law183.Subspectral Law2 from (ImplicationTransfer.singleton_183 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_184_2 : Law184.Subspectral Law1685 := (show Law184.Subspectral Law2 from (ImplicationTransfer.singleton_184 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_185_2 : Law185.Subspectral Law1685 := (show Law185.Subspectral Law2 from (ImplicationTransfer.singleton_185 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_187_2 : Law187.Subspectral Law1685 := (show Law187.Subspectral Law2 from (ImplicationTransfer.singleton_187 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_188_2 : Law188.Subspectral Law1685 := (show Law188.Subspectral Law2 from (ImplicationTransfer.singleton_188 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_189_2 : Law189.Subspectral Law1685 := (show Law189.Subspectral Law2 from (ImplicationTransfer.singleton_189 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_191_2 : Law191.Subspectral Law1685 := (show Law191.Subspectral Law2 from (ImplicationTransfer.singleton_191 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_192_2 : Law192.Subspectral Law1685 := (show Law192.Subspectral Law2 from (ImplicationTransfer.singleton_192 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_193_2 : Law193.Subspectral Law1685 := (show Law193.Subspectral Law2 from (ImplicationTransfer.singleton_193 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_195_2 : Law195.Subspectral Law1685 := (show Law195.Subspectral Law2 from (ImplicationTransfer.singleton_195 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_196_2 : Law196.Subspectral Law1685 := (show Law196.Subspectral Law2 from (ImplicationTransfer.singleton_196 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_197_2 : Law197.Subspectral Law1685 := (show Law197.Subspectral Law2 from (ImplicationTransfer.singleton_197 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_199_2 : Law199.Subspectral Law1685 := (show Law199.Subspectral Law2 from (ImplicationTransfer.singleton_199 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_200_2 : Law200.Subspectral Law1685 := (show Law200.Subspectral Law2 from (ImplicationTransfer.singleton_200 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_201_2 : Law201.Subspectral Law1685 := (show Law201.Subspectral Law2 from (ImplicationTransfer.singleton_201 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_202_2 : Law202.Subspectral Law1685 := (show Law202.Subspectral Law2 from (ImplicationTransfer.singleton_202 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_219_2 : Law219.Subspectral Law873 := (show Law219.Subspectral Law115 from (ImplicationTransfer.spectrum_219_eq_115).subset).trans basis_route_115_2

theorem route_220_2 : Law220.Subspectral Law1685 := (show Law220.Subspectral Law2 from (ImplicationTransfer.singleton_220 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_222_2 : Law222.Subspectral Law1685 := (show Law222.Subspectral Law125 from (ImplicationTransfer.spectrum_222_eq_125).subset).trans basis_route_125_2

theorem route_223_2 : Law223.Subspectral Law1685 := (show Law223.Subspectral Law2 from (ImplicationTransfer.singleton_223 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_225_2 : Law225.Subspectral Law1685 := (show Law225.Subspectral Law2 from (ImplicationTransfer.singleton_225 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_226_2 : Law226.Subspectral Law1685 := (show Law226.Subspectral Law2 from (ImplicationTransfer.singleton_226 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_227_2 : Law227.Subspectral Law1685 := (show Law227.Subspectral Law2 from (ImplicationTransfer.singleton_227 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_229_2 : Law229.Subspectral Law1685 := (show Law229.Subspectral Law118 from (ImplicationTransfer.spectrum_229_eq_118).subset).trans basis_route_118_2

theorem route_230_2 : Law230.Subspectral Law1685 := (show Law230.Subspectral Law2 from (ImplicationTransfer.singleton_230 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_232_2 : Law232.Subspectral Law1685 := (show Law232.Subspectral Law2 from (ImplicationTransfer.singleton_232 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_233_2 : Law233.Subspectral Law1685 := (show Law233.Subspectral Law2 from (ImplicationTransfer.singleton_233 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_235_2 : Law235.Subspectral Law1685 := (show Law235.Subspectral Law2 from (ImplicationTransfer.singleton_235 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_236_2 : Law236.Subspectral Law1685 := (show Law236.Subspectral Law2 from (ImplicationTransfer.singleton_236 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_237_2 : Law237.Subspectral Law1685 := (show Law237.Subspectral Law2 from (ImplicationTransfer.singleton_237 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_239_2 : Law239.Subspectral Law1685 := (show Law239.Subspectral Law2 from (ImplicationTransfer.singleton_239 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_240_2 : Law240.Subspectral Law1685 := (show Law240.Subspectral Law2 from (ImplicationTransfer.singleton_240 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_241_2 : Law241.Subspectral Law1685 := (show Law241.Subspectral Law2 from (ImplicationTransfer.singleton_241 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_243_2 : Law243.Subspectral Law1685 := (show Law243.Subspectral Law2 from (ImplicationTransfer.singleton_243 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_244_2 : Law244.Subspectral Law1685 := (show Law244.Subspectral Law2 from (ImplicationTransfer.singleton_244 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_245_2 : Law245.Subspectral Law1685 := (show Law245.Subspectral Law2 from (ImplicationTransfer.singleton_245 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_247_2 : Law247.Subspectral Law1685 := (show Law247.Subspectral Law2 from (ImplicationTransfer.singleton_247 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_248_2 : Law248.Subspectral Law1685 := (show Law248.Subspectral Law2 from (ImplicationTransfer.singleton_248 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_249_2 : Law249.Subspectral Law1685 := (show Law249.Subspectral Law2 from (ImplicationTransfer.singleton_249 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_251_2 : Law251.Subspectral Law1685 := (show Law251.Subspectral Law2 from (ImplicationTransfer.singleton_251 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_252_2 : Law252.Subspectral Law1685 := (show Law252.Subspectral Law2 from (ImplicationTransfer.singleton_252 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_253_2 : Law253.Subspectral Law1685 := (show Law253.Subspectral Law2 from (ImplicationTransfer.singleton_253 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_254_2 : Law254.Subspectral Law1685 := (show Law254.Subspectral Law2 from (ImplicationTransfer.singleton_254 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_271_2 : Law271.Subspectral Law1685 := (show Law271.Subspectral Law63 from (ImplicationTransfer.spectrum_271_eq_63).subset).trans basis_route_63_2

theorem route_272_2 : Law272.Subspectral Law1685 := (show Law272.Subspectral Law2 from (ImplicationTransfer.singleton_272 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_274_2 : Law274.Subspectral Law1685 := (show Law274.Subspectral Law73 from (ImplicationTransfer.spectrum_274_eq_73).subset).trans basis_route_73_2

theorem route_275_2 : Law275.Subspectral Law1685 := (show Law275.Subspectral Law2 from (ImplicationTransfer.singleton_275 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_277_2 : Law277.Subspectral Law1685 := (show Law277.Subspectral Law2 from (ImplicationTransfer.singleton_277 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_278_2 : Law278.Subspectral Law1685 := (show Law278.Subspectral Law2 from (ImplicationTransfer.singleton_278 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_279_2 : Law279.Subspectral Law1685 := (show Law279.Subspectral Law2 from (ImplicationTransfer.singleton_279 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_281_2 : Law281.Subspectral Law873 := (show Law281.Subspectral Law66 from (ImplicationTransfer.spectrum_281_eq_66).subset).trans basis_route_66_2

theorem route_282_2 : Law282.Subspectral Law1685 := (show Law282.Subspectral Law2 from (ImplicationTransfer.singleton_282 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_284_2 : Law284.Subspectral Law1685 := (show Law284.Subspectral Law2 from (ImplicationTransfer.singleton_284 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_285_2 : Law285.Subspectral Law1685 := (show Law285.Subspectral Law2 from (ImplicationTransfer.singleton_285 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_287_2 : Law287.Subspectral Law1685 := (show Law287.Subspectral Law2 from (ImplicationTransfer.singleton_287 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_288_2 : Law288.Subspectral Law1685 := (show Law288.Subspectral Law2 from (ImplicationTransfer.singleton_288 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_289_2 : Law289.Subspectral Law1685 := (show Law289.Subspectral Law2 from (ImplicationTransfer.singleton_289 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_291_2 : Law291.Subspectral Law1685 := (show Law291.Subspectral Law2 from (ImplicationTransfer.singleton_291 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_292_2 : Law292.Subspectral Law1685 := (show Law292.Subspectral Law2 from (ImplicationTransfer.singleton_292 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_293_2 : Law293.Subspectral Law1685 := (show Law293.Subspectral Law2 from (ImplicationTransfer.singleton_293 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_295_2 : Law295.Subspectral Law1685 := (show Law295.Subspectral Law2 from (ImplicationTransfer.singleton_295 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_296_2 : Law296.Subspectral Law1685 := (show Law296.Subspectral Law2 from (ImplicationTransfer.singleton_296 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_297_2 : Law297.Subspectral Law1685 := (show Law297.Subspectral Law2 from (ImplicationTransfer.singleton_297 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_299_2 : Law299.Subspectral Law1685 := (show Law299.Subspectral Law2 from (ImplicationTransfer.singleton_299 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_300_2 : Law300.Subspectral Law1685 := (show Law300.Subspectral Law2 from (ImplicationTransfer.singleton_300 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_301_2 : Law301.Subspectral Law1685 := (show Law301.Subspectral Law2 from (ImplicationTransfer.singleton_301 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_303_2 : Law303.Subspectral Law1685 := (show Law303.Subspectral Law2 from (ImplicationTransfer.singleton_303 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_304_2 : Law304.Subspectral Law1685 := (show Law304.Subspectral Law2 from (ImplicationTransfer.singleton_304 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_305_2 : Law305.Subspectral Law1685 := (show Law305.Subspectral Law2 from (ImplicationTransfer.singleton_305 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_306_2 : Law306.Subspectral Law1685 := (show Law306.Subspectral Law2 from (ImplicationTransfer.singleton_306 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_465_2 : Law465.Subspectral Law1685 := (show Law465.Subspectral Law2 from (ImplicationTransfer.singleton_465 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_467_2 : Law467.Subspectral Law467 := basis_route_467_2

theorem route_467_3 : Law467.Subspectral Law467 := basis_route_467_3

theorem route_467_4 : Law467.Subspectral Law467 := basis_route_467_4

theorem route_467_6 : Law467.Subspectral Law467 := basis_route_467_6

theorem route_468_2 : Law468.Subspectral Law1685 := (show Law468.Subspectral Law2 from (ImplicationTransfer.singleton_468 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_470_2 : Law470.Subspectral Law1685 := (show Law470.Subspectral Law2 from (ImplicationTransfer.singleton_470 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_471_2 : Law471.Subspectral Law1685 := (show Law471.Subspectral Law2 from (ImplicationTransfer.singleton_471 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_472_2 : Law472.Subspectral Law1685 := (show Law472.Subspectral Law2 from (ImplicationTransfer.singleton_472 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_474_2 : Law474.Subspectral Law474 := basis_route_474_2

theorem route_474_4 : Law474.Subspectral Law474 := basis_route_474_4

theorem route_475_2 : Law475.Subspectral Law1685 := (show Law475.Subspectral Law2 from (ImplicationTransfer.singleton_475 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_478_2 : Law478.Subspectral Law1685 := (show Law478.Subspectral Law2 from (ImplicationTransfer.singleton_478 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_480_2 : Law480.Subspectral Law1685 := (show Law480.Subspectral Law2 from (ImplicationTransfer.singleton_480 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_481_3 : Law481.Subspectral Law481 := basis_route_481_3

theorem route_481_6 : Law481.Subspectral Law481 := basis_route_481_6

theorem route_482_2 : Law482.Subspectral Law1685 := (show Law482.Subspectral Law2 from (ImplicationTransfer.singleton_482 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_484_2 : Law484.Subspectral Law1685 := (show Law484.Subspectral Law2 from (ImplicationTransfer.singleton_484 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_485_2 : Law485.Subspectral Law1685 := (show Law485.Subspectral Law2 from (ImplicationTransfer.singleton_485 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_486_2 : Law486.Subspectral Law1685 := (show Law486.Subspectral Law2 from (ImplicationTransfer.singleton_486 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_488_2 : Law488.Subspectral Law1685 := (show Law488.Subspectral Law2 from (ImplicationTransfer.singleton_488 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_490_2 : Law490.Subspectral Law1685 := (show Law490.Subspectral Law2 from (ImplicationTransfer.singleton_490 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_493_2 : Law493.Subspectral Law1685 := (show Law493.Subspectral Law2 from (ImplicationTransfer.singleton_493 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_494_2 : Law494.Subspectral Law1685 := (show Law494.Subspectral Law2 from (ImplicationTransfer.singleton_494 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_496_2 : Law496.Subspectral Law1685 := (show Law496.Subspectral Law2 from (ImplicationTransfer.singleton_496 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_497_2 : Law497.Subspectral Law1685 := (show Law497.Subspectral Law2 from (ImplicationTransfer.singleton_497 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_498_2 : Law498.Subspectral Law1685 := (show Law498.Subspectral Law2 from (ImplicationTransfer.singleton_498 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_499_2 : Law499.Subspectral Law1685 := (show Law499.Subspectral Law2 from (ImplicationTransfer.singleton_499 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_501_2 : Law501.Subspectral Law501 := basis_route_501_2

theorem route_502_2 : Law502.Subspectral Law1685 := (show Law502.Subspectral Law2 from (ImplicationTransfer.singleton_502 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_505_2 : Law505.Subspectral Law1685 := (show Law505.Subspectral Law2 from (ImplicationTransfer.singleton_505 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_507_2 : Law507.Subspectral Law1685 := (show Law507.Subspectral Law2 from (ImplicationTransfer.singleton_507 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_509_2 : Law509.Subspectral Law1685 := (show Law509.Subspectral Law2 from (ImplicationTransfer.singleton_509 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_512_2 : Law512.Subspectral Law1685 := (show Law512.Subspectral Law2 from (ImplicationTransfer.singleton_512 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_514_2 : Law514.Subspectral Law1685 := (show Law514.Subspectral Law2 from (ImplicationTransfer.singleton_514 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_515_2 : Law515.Subspectral Law1685 := (show Law515.Subspectral Law2 from (ImplicationTransfer.singleton_515 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_517_2 : Law517.Subspectral Law1685 := (show Law517.Subspectral Law2 from (ImplicationTransfer.singleton_517 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_518_2 : Law518.Subspectral Law1685 := (show Law518.Subspectral Law2 from (ImplicationTransfer.singleton_518 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_519_2 : Law519.Subspectral Law1685 := (show Law519.Subspectral Law2 from (ImplicationTransfer.singleton_519 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_521_2 : Law521.Subspectral Law1685 := (show Law521.Subspectral Law2 from (ImplicationTransfer.singleton_521 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_523_2 : Law523.Subspectral Law1685 := (show Law523.Subspectral Law2 from (ImplicationTransfer.singleton_523 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_525_2 : Law525.Subspectral Law1685 := (show Law525.Subspectral Law2 from (ImplicationTransfer.singleton_525 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_526_2 : Law526.Subspectral Law1685 := (show Law526.Subspectral Law2 from (ImplicationTransfer.singleton_526 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_527_2 : Law527.Subspectral Law1685 := (show Law527.Subspectral Law2 from (ImplicationTransfer.singleton_527 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_529_2 : Law529.Subspectral Law1685 := (show Law529.Subspectral Law2 from (ImplicationTransfer.singleton_529 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_530_2 : Law530.Subspectral Law1685 := (show Law530.Subspectral Law2 from (ImplicationTransfer.singleton_530 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_531_2 : Law531.Subspectral Law1685 := (show Law531.Subspectral Law2 from (ImplicationTransfer.singleton_531 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_533_2 : Law533.Subspectral Law1685 := (show Law533.Subspectral Law2 from (ImplicationTransfer.singleton_533 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_534_2 : Law534.Subspectral Law1685 := (show Law534.Subspectral Law2 from (ImplicationTransfer.singleton_534 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_535_2 : Law535.Subspectral Law1685 := (show Law535.Subspectral Law2 from (ImplicationTransfer.singleton_535 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_536_2 : Law536.Subspectral Law1685 := (show Law536.Subspectral Law2 from (ImplicationTransfer.singleton_536 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_538_2 : Law538.Subspectral Law1685 := (show Law538.Subspectral Law2 from (ImplicationTransfer.singleton_538 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_539_2 : Law539.Subspectral Law1685 := (show Law539.Subspectral Law2 from (ImplicationTransfer.singleton_539 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_540_2 : Law540.Subspectral Law1685 := (show Law540.Subspectral Law2 from (ImplicationTransfer.singleton_540 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_542_2 : Law542.Subspectral Law1685 := (show Law542.Subspectral Law2 from (ImplicationTransfer.singleton_542 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_544_2 : Law544.Subspectral Law1685 := (show Law544.Subspectral Law2 from (ImplicationTransfer.singleton_544 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_546_3 : Law546.Subspectral Law667 := basis_route_546_3

theorem route_547_2 : Law547.Subspectral Law1685 := (show Law547.Subspectral Law2 from (ImplicationTransfer.singleton_547 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_548_2 : Law548.Subspectral Law1685 := (show Law548.Subspectral Law2 from (ImplicationTransfer.singleton_548 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_550_2 : Law550.Subspectral Law1685 := (show Law550.Subspectral Law2 from (ImplicationTransfer.singleton_550 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_551_2 : Law551.Subspectral Law1685 := (show Law551.Subspectral Law2 from (ImplicationTransfer.singleton_551 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_552_2 : Law552.Subspectral Law1685 := (show Law552.Subspectral Law2 from (ImplicationTransfer.singleton_552 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_553_2 : Law553.Subspectral Law1685 := (show Law553.Subspectral Law2 from (ImplicationTransfer.singleton_553 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_555_2 : Law555.Subspectral Law1685 := (show Law555.Subspectral Law2 from (ImplicationTransfer.singleton_555 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_556_3 : Law556.Subspectral Law667 := basis_route_556_3

theorem route_557_2 : Law557.Subspectral Law1685 := (show Law557.Subspectral Law2 from (ImplicationTransfer.singleton_557 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_559_2 : Law559.Subspectral Law1685 := (show Law559.Subspectral Law2 from (ImplicationTransfer.singleton_559 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_560_2 : Law560.Subspectral Law1685 := (show Law560.Subspectral Law2 from (ImplicationTransfer.singleton_560 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_561_2 : Law561.Subspectral Law1685 := (show Law561.Subspectral Law2 from (ImplicationTransfer.singleton_561 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_563_2 : Law563.Subspectral Law1685 := (show Law563.Subspectral Law2 from (ImplicationTransfer.singleton_563 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_564_2 : Law564.Subspectral Law1685 := (show Law564.Subspectral Law2 from (ImplicationTransfer.singleton_564 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_565_2 : Law565.Subspectral Law1685 := (show Law565.Subspectral Law2 from (ImplicationTransfer.singleton_565 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_567_2 : Law567.Subspectral Law1685 := (show Law567.Subspectral Law2 from (ImplicationTransfer.singleton_567 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_568_2 : Law568.Subspectral Law1685 := (show Law568.Subspectral Law2 from (ImplicationTransfer.singleton_568 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_569_2 : Law569.Subspectral Law1685 := (show Law569.Subspectral Law2 from (ImplicationTransfer.singleton_569 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_570_2 : Law570.Subspectral Law1685 := (show Law570.Subspectral Law2 from (ImplicationTransfer.singleton_570 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_573_2 : Law573.Subspectral Law1685 := (show Law573.Subspectral Law2 from (ImplicationTransfer.singleton_573 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_574_2 : Law574.Subspectral Law1685 := (show Law574.Subspectral Law2 from (ImplicationTransfer.singleton_574 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_576_2 : Law576.Subspectral Law1685 := (show Law576.Subspectral Law2 from (ImplicationTransfer.singleton_576 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_577_2 : Law577.Subspectral Law1685 := (show Law577.Subspectral Law2 from (ImplicationTransfer.singleton_577 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_578_2 : Law578.Subspectral Law1685 := (show Law578.Subspectral Law2 from (ImplicationTransfer.singleton_578 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_580_2 : Law580.Subspectral Law1685 := (show Law580.Subspectral Law2 from (ImplicationTransfer.singleton_580 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_581_2 : Law581.Subspectral Law1685 := (show Law581.Subspectral Law2 from (ImplicationTransfer.singleton_581 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_582_2 : Law582.Subspectral Law1685 := (show Law582.Subspectral Law2 from (ImplicationTransfer.singleton_582 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_584_2 : Law584.Subspectral Law1685 := (show Law584.Subspectral Law2 from (ImplicationTransfer.singleton_584 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_585_2 : Law585.Subspectral Law1685 := (show Law585.Subspectral Law2 from (ImplicationTransfer.singleton_585 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_586_2 : Law586.Subspectral Law1685 := (show Law586.Subspectral Law2 from (ImplicationTransfer.singleton_586 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_587_2 : Law587.Subspectral Law1685 := (show Law587.Subspectral Law2 from (ImplicationTransfer.singleton_587 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_589_2 : Law589.Subspectral Law1685 := (show Law589.Subspectral Law2 from (ImplicationTransfer.singleton_589 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_590_2 : Law590.Subspectral Law1685 := (show Law590.Subspectral Law2 from (ImplicationTransfer.singleton_590 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_591_2 : Law591.Subspectral Law1685 := (show Law591.Subspectral Law2 from (ImplicationTransfer.singleton_591 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_592_2 : Law592.Subspectral Law1685 := (show Law592.Subspectral Law2 from (ImplicationTransfer.singleton_592 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_594_2 : Law594.Subspectral Law1685 := (show Law594.Subspectral Law2 from (ImplicationTransfer.singleton_594 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_595_2 : Law595.Subspectral Law1685 := (show Law595.Subspectral Law2 from (ImplicationTransfer.singleton_595 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_596_2 : Law596.Subspectral Law1685 := (show Law596.Subspectral Law2 from (ImplicationTransfer.singleton_596 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_597_2 : Law597.Subspectral Law1685 := (show Law597.Subspectral Law2 from (ImplicationTransfer.singleton_597 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_599_2 : Law599.Subspectral Law1685 := (show Law599.Subspectral Law2 from (ImplicationTransfer.singleton_599 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_600_2 : Law600.Subspectral Law1685 := (show Law600.Subspectral Law2 from (ImplicationTransfer.singleton_600 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_601_2 : Law601.Subspectral Law1685 := (show Law601.Subspectral Law2 from (ImplicationTransfer.singleton_601 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_602_2 : Law602.Subspectral Law1685 := (show Law602.Subspectral Law2 from (ImplicationTransfer.singleton_602 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_604_2 : Law604.Subspectral Law1685 := (show Law604.Subspectral Law2 from (ImplicationTransfer.singleton_604 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_605_2 : Law605.Subspectral Law1685 := (show Law605.Subspectral Law2 from (ImplicationTransfer.singleton_605 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_606_2 : Law606.Subspectral Law1685 := (show Law606.Subspectral Law2 from (ImplicationTransfer.singleton_606 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_607_2 : Law607.Subspectral Law1685 := (show Law607.Subspectral Law2 from (ImplicationTransfer.singleton_607 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_609_2 : Law609.Subspectral Law1685 := (show Law609.Subspectral Law2 from (ImplicationTransfer.singleton_609 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_610_2 : Law610.Subspectral Law1685 := (show Law610.Subspectral Law2 from (ImplicationTransfer.singleton_610 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_611_2 : Law611.Subspectral Law1685 := (show Law611.Subspectral Law2 from (ImplicationTransfer.singleton_611 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_612_2 : Law612.Subspectral Law1685 := (show Law612.Subspectral Law2 from (ImplicationTransfer.singleton_612 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_613_2 : Law613.Subspectral Law1685 := (show Law613.Subspectral Law2 from (ImplicationTransfer.singleton_613 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_667_3 : Law667.Subspectral Law667 := basis_route_667_3

theorem route_668_2 : Law668.Subspectral Law1685 := (show Law668.Subspectral Law2 from (ImplicationTransfer.singleton_668 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_670_2 : Law670.Subspectral Law670 := basis_route_670_2

theorem route_670_3 : Law670.Subspectral Law670 := basis_route_670_3

theorem route_670_6 : Law670.Subspectral Law670 := basis_route_670_6

theorem route_670_7 : Law670.Subspectral Law670 := basis_route_670_7

theorem route_671_2 : Law671.Subspectral Law1685 := (show Law671.Subspectral Law2 from (ImplicationTransfer.singleton_671 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_673_2 : Law673.Subspectral Law1685 := (show Law673.Subspectral Law2 from (ImplicationTransfer.singleton_673 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_674_2 : Law674.Subspectral Law1685 := (show Law674.Subspectral Law2 from (ImplicationTransfer.singleton_674 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_675_2 : Law675.Subspectral Law1685 := (show Law675.Subspectral Law2 from (ImplicationTransfer.singleton_675 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_677_2 : Law677.Subspectral Law677 := basis_route_677_2

theorem route_678_2 : Law678.Subspectral Law1685 := (show Law678.Subspectral Law2 from (ImplicationTransfer.singleton_678 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_681_2 : Law681.Subspectral Law1685 := (show Law681.Subspectral Law2 from (ImplicationTransfer.singleton_681 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_683_2 : Law683.Subspectral Law1685 := (show Law683.Subspectral Law2 from (ImplicationTransfer.singleton_683 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_685_2 : Law685.Subspectral Law1685 := (show Law685.Subspectral Law2 from (ImplicationTransfer.singleton_685 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_687_2 : Law687.Subspectral Law1685 := (show Law687.Subspectral Law2 from (ImplicationTransfer.singleton_687 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_688_2 : Law688.Subspectral Law1685 := (show Law688.Subspectral Law2 from (ImplicationTransfer.singleton_688 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_689_2 : Law689.Subspectral Law1685 := (show Law689.Subspectral Law2 from (ImplicationTransfer.singleton_689 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_691_2 : Law691.Subspectral Law1685 := (show Law691.Subspectral Law2 from (ImplicationTransfer.singleton_691 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_693_2 : Law693.Subspectral Law1685 := (show Law693.Subspectral Law2 from (ImplicationTransfer.singleton_693 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_695_3 : Law695.Subspectral Law667 := basis_route_695_3

theorem route_696_2 : Law696.Subspectral Law1685 := (show Law696.Subspectral Law2 from (ImplicationTransfer.singleton_696 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_697_2 : Law697.Subspectral Law1685 := (show Law697.Subspectral Law2 from (ImplicationTransfer.singleton_697 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_699_2 : Law699.Subspectral Law1685 := (show Law699.Subspectral Law2 from (ImplicationTransfer.singleton_699 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_700_2 : Law700.Subspectral Law1685 := (show Law700.Subspectral Law2 from (ImplicationTransfer.singleton_700 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_701_2 : Law701.Subspectral Law1685 := (show Law701.Subspectral Law2 from (ImplicationTransfer.singleton_701 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_702_2 : Law702.Subspectral Law1685 := (show Law702.Subspectral Law2 from (ImplicationTransfer.singleton_702 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_704_2 : Law704.Subspectral Law704 := basis_route_704_2

theorem route_704_3 : Law704.Subspectral Law704 := basis_route_704_3

theorem route_704_4 : Law704.Subspectral Law704 := basis_route_704_4

theorem route_704_6 : Law704.Subspectral Law704 := basis_route_704_6

theorem route_704_9 : Law704.Subspectral Law704 := basis_route_704_9

theorem route_705_2 : Law705.Subspectral Law1685 := (show Law705.Subspectral Law2 from (ImplicationTransfer.singleton_705 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_708_2 : Law708.Subspectral Law1685 := (show Law708.Subspectral Law2 from (ImplicationTransfer.singleton_708 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_710_2 : Law710.Subspectral Law1685 := (show Law710.Subspectral Law2 from (ImplicationTransfer.singleton_710 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_712_2 : Law712.Subspectral Law1685 := (show Law712.Subspectral Law2 from (ImplicationTransfer.singleton_712 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_715_2 : Law715.Subspectral Law1685 := (show Law715.Subspectral Law2 from (ImplicationTransfer.singleton_715 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_717_2 : Law717.Subspectral Law1685 := (show Law717.Subspectral Law2 from (ImplicationTransfer.singleton_717 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_718_2 : Law718.Subspectral Law1685 := (show Law718.Subspectral Law2 from (ImplicationTransfer.singleton_718 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_720_2 : Law720.Subspectral Law1685 := (show Law720.Subspectral Law2 from (ImplicationTransfer.singleton_720 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_721_2 : Law721.Subspectral Law1685 := (show Law721.Subspectral Law2 from (ImplicationTransfer.singleton_721 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_722_2 : Law722.Subspectral Law1685 := (show Law722.Subspectral Law2 from (ImplicationTransfer.singleton_722 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_724_2 : Law724.Subspectral Law1685 := (show Law724.Subspectral Law2 from (ImplicationTransfer.singleton_724 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_726_2 : Law726.Subspectral Law1685 := (show Law726.Subspectral Law2 from (ImplicationTransfer.singleton_726 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_728_2 : Law728.Subspectral Law1685 := (show Law728.Subspectral Law2 from (ImplicationTransfer.singleton_728 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_729_2 : Law729.Subspectral Law1685 := (show Law729.Subspectral Law2 from (ImplicationTransfer.singleton_729 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_730_2 : Law730.Subspectral Law1685 := (show Law730.Subspectral Law2 from (ImplicationTransfer.singleton_730 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_732_2 : Law732.Subspectral Law1685 := (show Law732.Subspectral Law2 from (ImplicationTransfer.singleton_732 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_733_2 : Law733.Subspectral Law1685 := (show Law733.Subspectral Law2 from (ImplicationTransfer.singleton_733 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_734_2 : Law734.Subspectral Law1685 := (show Law734.Subspectral Law2 from (ImplicationTransfer.singleton_734 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_736_2 : Law736.Subspectral Law1685 := (show Law736.Subspectral Law2 from (ImplicationTransfer.singleton_736 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_737_2 : Law737.Subspectral Law1685 := (show Law737.Subspectral Law2 from (ImplicationTransfer.singleton_737 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_738_2 : Law738.Subspectral Law1685 := (show Law738.Subspectral Law2 from (ImplicationTransfer.singleton_738 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_739_2 : Law739.Subspectral Law1685 := (show Law739.Subspectral Law2 from (ImplicationTransfer.singleton_739 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_741_2 : Law741.Subspectral Law1685 := (show Law741.Subspectral Law2 from (ImplicationTransfer.singleton_741 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_742_2 : Law742.Subspectral Law1685 := (show Law742.Subspectral Law2 from (ImplicationTransfer.singleton_742 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_743_2 : Law743.Subspectral Law1685 := (show Law743.Subspectral Law2 from (ImplicationTransfer.singleton_743 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_745_2 : Law745.Subspectral Law1685 := (show Law745.Subspectral Law2 from (ImplicationTransfer.singleton_745 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_747_2 : Law747.Subspectral Law1685 := (show Law747.Subspectral Law2 from (ImplicationTransfer.singleton_747 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_749_3 : Law749.Subspectral Law667 := (show Law749.Subspectral Law556 from (ImplicationTransfer.spectrum_749_eq_556).subset).trans basis_route_556_3

theorem route_750_2 : Law750.Subspectral Law1685 := (show Law750.Subspectral Law2 from (ImplicationTransfer.singleton_750 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_751_2 : Law751.Subspectral Law1685 := (show Law751.Subspectral Law2 from (ImplicationTransfer.singleton_751 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_753_2 : Law753.Subspectral Law1685 := (show Law753.Subspectral Law2 from (ImplicationTransfer.singleton_753 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_754_2 : Law754.Subspectral Law1685 := (show Law754.Subspectral Law2 from (ImplicationTransfer.singleton_754 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_755_2 : Law755.Subspectral Law1685 := (show Law755.Subspectral Law2 from (ImplicationTransfer.singleton_755 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_756_2 : Law756.Subspectral Law1685 := (show Law756.Subspectral Law2 from (ImplicationTransfer.singleton_756 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_758_2 : Law758.Subspectral Law1685 := (show Law758.Subspectral Law2 from (ImplicationTransfer.singleton_758 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_760_2 : Law760.Subspectral Law1685 := (show Law760.Subspectral Law2 from (ImplicationTransfer.singleton_760 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_762_2 : Law762.Subspectral Law1685 := (show Law762.Subspectral Law2 from (ImplicationTransfer.singleton_762 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_763_2 : Law763.Subspectral Law1685 := (show Law763.Subspectral Law2 from (ImplicationTransfer.singleton_763 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_764_2 : Law764.Subspectral Law1685 := (show Law764.Subspectral Law2 from (ImplicationTransfer.singleton_764 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_766_2 : Law766.Subspectral Law1685 := (show Law766.Subspectral Law2 from (ImplicationTransfer.singleton_766 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_767_2 : Law767.Subspectral Law1685 := (show Law767.Subspectral Law2 from (ImplicationTransfer.singleton_767 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_768_2 : Law768.Subspectral Law1685 := (show Law768.Subspectral Law2 from (ImplicationTransfer.singleton_768 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_770_2 : Law770.Subspectral Law1685 := (show Law770.Subspectral Law2 from (ImplicationTransfer.singleton_770 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_771_2 : Law771.Subspectral Law1685 := (show Law771.Subspectral Law2 from (ImplicationTransfer.singleton_771 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_772_2 : Law772.Subspectral Law1685 := (show Law772.Subspectral Law2 from (ImplicationTransfer.singleton_772 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_773_2 : Law773.Subspectral Law1685 := (show Law773.Subspectral Law2 from (ImplicationTransfer.singleton_773 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_775_3 : Law775.Subspectral Law667 := (show Law775.Subspectral Law556 from (ImplicationTransfer.spectrum_775_eq_556).subset).trans basis_route_556_3

theorem route_776_2 : Law776.Subspectral Law1685 := (show Law776.Subspectral Law2 from (ImplicationTransfer.singleton_776 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_777_2 : Law777.Subspectral Law1685 := (show Law777.Subspectral Law2 from (ImplicationTransfer.singleton_777 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_779_2 : Law779.Subspectral Law1685 := (show Law779.Subspectral Law2 from (ImplicationTransfer.singleton_779 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_780_2 : Law780.Subspectral Law1685 := (show Law780.Subspectral Law2 from (ImplicationTransfer.singleton_780 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_781_2 : Law781.Subspectral Law1685 := (show Law781.Subspectral Law2 from (ImplicationTransfer.singleton_781 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_783_2 : Law783.Subspectral Law1685 := (show Law783.Subspectral Law2 from (ImplicationTransfer.singleton_783 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_784_2 : Law784.Subspectral Law1685 := (show Law784.Subspectral Law2 from (ImplicationTransfer.singleton_784 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_785_2 : Law785.Subspectral Law1685 := (show Law785.Subspectral Law2 from (ImplicationTransfer.singleton_785 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_787_2 : Law787.Subspectral Law1685 := (show Law787.Subspectral Law2 from (ImplicationTransfer.singleton_787 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_788_2 : Law788.Subspectral Law1685 := (show Law788.Subspectral Law2 from (ImplicationTransfer.singleton_788 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_789_2 : Law789.Subspectral Law1685 := (show Law789.Subspectral Law2 from (ImplicationTransfer.singleton_789 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_790_2 : Law790.Subspectral Law1685 := (show Law790.Subspectral Law2 from (ImplicationTransfer.singleton_790 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_792_2 : Law792.Subspectral Law1685 := (show Law792.Subspectral Law2 from (ImplicationTransfer.singleton_792 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_793_2 : Law793.Subspectral Law1685 := (show Law793.Subspectral Law2 from (ImplicationTransfer.singleton_793 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_794_2 : Law794.Subspectral Law1685 := (show Law794.Subspectral Law2 from (ImplicationTransfer.singleton_794 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_795_2 : Law795.Subspectral Law1685 := (show Law795.Subspectral Law2 from (ImplicationTransfer.singleton_795 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_797_2 : Law797.Subspectral Law1685 := (show Law797.Subspectral Law2 from (ImplicationTransfer.singleton_797 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_798_2 : Law798.Subspectral Law1685 := (show Law798.Subspectral Law2 from (ImplicationTransfer.singleton_798 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_799_2 : Law799.Subspectral Law1685 := (show Law799.Subspectral Law2 from (ImplicationTransfer.singleton_799 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_800_2 : Law800.Subspectral Law1685 := (show Law800.Subspectral Law2 from (ImplicationTransfer.singleton_800 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_802_2 : Law802.Subspectral Law1685 := (show Law802.Subspectral Law2 from (ImplicationTransfer.singleton_802 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_803_2 : Law803.Subspectral Law1685 := (show Law803.Subspectral Law2 from (ImplicationTransfer.singleton_803 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_804_2 : Law804.Subspectral Law1685 := (show Law804.Subspectral Law2 from (ImplicationTransfer.singleton_804 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_805_2 : Law805.Subspectral Law1685 := (show Law805.Subspectral Law2 from (ImplicationTransfer.singleton_805 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_807_2 : Law807.Subspectral Law1685 := (show Law807.Subspectral Law2 from (ImplicationTransfer.singleton_807 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_808_2 : Law808.Subspectral Law1685 := (show Law808.Subspectral Law2 from (ImplicationTransfer.singleton_808 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_809_2 : Law809.Subspectral Law1685 := (show Law809.Subspectral Law2 from (ImplicationTransfer.singleton_809 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_810_2 : Law810.Subspectral Law1685 := (show Law810.Subspectral Law2 from (ImplicationTransfer.singleton_810 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_812_2 : Law812.Subspectral Law1685 := (show Law812.Subspectral Law2 from (ImplicationTransfer.singleton_812 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_813_2 : Law813.Subspectral Law1685 := (show Law813.Subspectral Law2 from (ImplicationTransfer.singleton_813 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_814_2 : Law814.Subspectral Law1685 := (show Law814.Subspectral Law2 from (ImplicationTransfer.singleton_814 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_815_2 : Law815.Subspectral Law1685 := (show Law815.Subspectral Law2 from (ImplicationTransfer.singleton_815 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_816_2 : Law816.Subspectral Law1685 := (show Law816.Subspectral Law2 from (ImplicationTransfer.singleton_816 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_871_2 : Law871.Subspectral Law1685 := (show Law871.Subspectral Law2 from (ImplicationTransfer.singleton_871 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_873_2 : Law873.Subspectral Law873 := basis_route_873_2

theorem route_873_6 : Law873.Subspectral Law873 := basis_route_873_6

theorem route_874_2 : Law874.Subspectral Law1685 := (show Law874.Subspectral Law2 from (ImplicationTransfer.singleton_874 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_876_2 : Law876.Subspectral Law1685 := (show Law876.Subspectral Law2 from (ImplicationTransfer.singleton_876 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_877_2 : Law877.Subspectral Law1685 := (show Law877.Subspectral Law2 from (ImplicationTransfer.singleton_877 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_878_2 : Law878.Subspectral Law1685 := (show Law878.Subspectral Law2 from (ImplicationTransfer.singleton_878 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_880_2 : Law880.Subspectral Law873 := basis_route_880_2

theorem route_881_2 : Law881.Subspectral Law1685 := (show Law881.Subspectral Law2 from (ImplicationTransfer.singleton_881 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_883_3 : Law883.Subspectral Law883 := basis_route_883_3

theorem route_884_2 : Law884.Subspectral Law1685 := (show Law884.Subspectral Law2 from (ImplicationTransfer.singleton_884 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_886_2 : Law886.Subspectral Law1685 := (show Law886.Subspectral Law2 from (ImplicationTransfer.singleton_886 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_887_3 : Law887.Subspectral Law667 := basis_route_887_3

theorem route_888_2 : Law888.Subspectral Law1685 := (show Law888.Subspectral Law2 from (ImplicationTransfer.singleton_888 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_890_2 : Law890.Subspectral Law1685 := (show Law890.Subspectral Law2 from (ImplicationTransfer.singleton_890 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_891_2 : Law891.Subspectral Law1685 := (show Law891.Subspectral Law2 from (ImplicationTransfer.singleton_891 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_892_2 : Law892.Subspectral Law1685 := (show Law892.Subspectral Law2 from (ImplicationTransfer.singleton_892 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_894_2 : Law894.Subspectral Law1685 := (show Law894.Subspectral Law2 from (ImplicationTransfer.singleton_894 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_895_3 : Law895.Subspectral Law667 := basis_route_895_3

theorem route_896_2 : Law896.Subspectral Law1685 := (show Law896.Subspectral Law2 from (ImplicationTransfer.singleton_896 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_898_3 : Law898.Subspectral Law667 := basis_route_898_3

theorem route_899_2 : Law899.Subspectral Law1685 := (show Law899.Subspectral Law2 from (ImplicationTransfer.singleton_899 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_900_2 : Law900.Subspectral Law1685 := (show Law900.Subspectral Law2 from (ImplicationTransfer.singleton_900 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_902_2 : Law902.Subspectral Law1685 := (show Law902.Subspectral Law2 from (ImplicationTransfer.singleton_902 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_903_2 : Law903.Subspectral Law1685 := (show Law903.Subspectral Law2 from (ImplicationTransfer.singleton_903 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_904_2 : Law904.Subspectral Law1685 := (show Law904.Subspectral Law2 from (ImplicationTransfer.singleton_904 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_905_2 : Law905.Subspectral Law1685 := (show Law905.Subspectral Law2 from (ImplicationTransfer.singleton_905 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_907_2 : Law907.Subspectral Law907 := basis_route_907_2

theorem route_907_4 : Law907.Subspectral Law907 := basis_route_907_4

theorem route_907_5 : Law907.Subspectral Law907 := basis_route_907_5

theorem route_907_6 : Law907.Subspectral Law907 := basis_route_907_6

theorem route_908_2 : Law908.Subspectral Law1685 := (show Law908.Subspectral Law2 from (ImplicationTransfer.singleton_908 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_911_2 : Law911.Subspectral Law1685 := (show Law911.Subspectral Law2 from (ImplicationTransfer.singleton_911 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_913_2 : Law913.Subspectral Law1685 := (show Law913.Subspectral Law2 from (ImplicationTransfer.singleton_913 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_915_2 : Law915.Subspectral Law1685 := (show Law915.Subspectral Law2 from (ImplicationTransfer.singleton_915 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_918_2 : Law918.Subspectral Law1685 := (show Law918.Subspectral Law2 from (ImplicationTransfer.singleton_918 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_920_2 : Law920.Subspectral Law1685 := (show Law920.Subspectral Law2 from (ImplicationTransfer.singleton_920 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_921_2 : Law921.Subspectral Law1685 := (show Law921.Subspectral Law2 from (ImplicationTransfer.singleton_921 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_923_2 : Law923.Subspectral Law1685 := (show Law923.Subspectral Law2 from (ImplicationTransfer.singleton_923 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_924_2 : Law924.Subspectral Law1685 := (show Law924.Subspectral Law2 from (ImplicationTransfer.singleton_924 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_925_2 : Law925.Subspectral Law1685 := (show Law925.Subspectral Law2 from (ImplicationTransfer.singleton_925 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_927_2 : Law927.Subspectral Law1685 := (show Law927.Subspectral Law2 from (ImplicationTransfer.singleton_927 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_929_2 : Law929.Subspectral Law1685 := (show Law929.Subspectral Law2 from (ImplicationTransfer.singleton_929 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_931_2 : Law931.Subspectral Law1685 := (show Law931.Subspectral Law2 from (ImplicationTransfer.singleton_931 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_932_2 : Law932.Subspectral Law1685 := (show Law932.Subspectral Law2 from (ImplicationTransfer.singleton_932 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_933_2 : Law933.Subspectral Law1685 := (show Law933.Subspectral Law2 from (ImplicationTransfer.singleton_933 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_935_2 : Law935.Subspectral Law1685 := (show Law935.Subspectral Law2 from (ImplicationTransfer.singleton_935 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_936_2 : Law936.Subspectral Law1685 := (show Law936.Subspectral Law2 from (ImplicationTransfer.singleton_936 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_937_2 : Law937.Subspectral Law1685 := (show Law937.Subspectral Law2 from (ImplicationTransfer.singleton_937 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_939_2 : Law939.Subspectral Law1685 := (show Law939.Subspectral Law2 from (ImplicationTransfer.singleton_939 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_940_2 : Law940.Subspectral Law1685 := (show Law940.Subspectral Law2 from (ImplicationTransfer.singleton_940 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_941_2 : Law941.Subspectral Law1685 := (show Law941.Subspectral Law2 from (ImplicationTransfer.singleton_941 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_942_2 : Law942.Subspectral Law1685 := (show Law942.Subspectral Law2 from (ImplicationTransfer.singleton_942 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_944_2 : Law944.Subspectral Law1685 := (show Law944.Subspectral Law2 from (ImplicationTransfer.singleton_944 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_945_2 : Law945.Subspectral Law1685 := (show Law945.Subspectral Law2 from (ImplicationTransfer.singleton_945 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_946_2 : Law946.Subspectral Law1685 := (show Law946.Subspectral Law2 from (ImplicationTransfer.singleton_946 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_948_2 : Law948.Subspectral Law1685 := (show Law948.Subspectral Law2 from (ImplicationTransfer.singleton_948 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_949_3 : Law949.Subspectral Law667 := (show Law949.Subspectral Law546 from (ImplicationTransfer.spectrum_949_eq_546).subset).trans basis_route_546_3

theorem route_950_2 : Law950.Subspectral Law1685 := (show Law950.Subspectral Law2 from (ImplicationTransfer.singleton_950 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_953_2 : Law953.Subspectral Law1685 := (show Law953.Subspectral Law2 from (ImplicationTransfer.singleton_953 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_954_2 : Law954.Subspectral Law1685 := (show Law954.Subspectral Law2 from (ImplicationTransfer.singleton_954 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_956_2 : Law956.Subspectral Law1685 := (show Law956.Subspectral Law2 from (ImplicationTransfer.singleton_956 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_957_2 : Law957.Subspectral Law1685 := (show Law957.Subspectral Law2 from (ImplicationTransfer.singleton_957 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_958_2 : Law958.Subspectral Law1685 := (show Law958.Subspectral Law2 from (ImplicationTransfer.singleton_958 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_959_2 : Law959.Subspectral Law1685 := (show Law959.Subspectral Law2 from (ImplicationTransfer.singleton_959 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_961_2 : Law961.Subspectral Law1685 := (show Law961.Subspectral Law2 from (ImplicationTransfer.singleton_961 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_962_3 : Law962.Subspectral Law667 := (show Law962.Subspectral Law546 from (ImplicationTransfer.spectrum_962_eq_546).subset).trans basis_route_546_3

theorem route_963_2 : Law963.Subspectral Law1685 := (show Law963.Subspectral Law2 from (ImplicationTransfer.singleton_963 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_965_2 : Law965.Subspectral Law1685 := (show Law965.Subspectral Law2 from (ImplicationTransfer.singleton_965 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_966_2 : Law966.Subspectral Law1685 := (show Law966.Subspectral Law2 from (ImplicationTransfer.singleton_966 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_967_2 : Law967.Subspectral Law1685 := (show Law967.Subspectral Law2 from (ImplicationTransfer.singleton_967 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_969_2 : Law969.Subspectral Law1685 := (show Law969.Subspectral Law2 from (ImplicationTransfer.singleton_969 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_970_2 : Law970.Subspectral Law1685 := (show Law970.Subspectral Law2 from (ImplicationTransfer.singleton_970 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_971_2 : Law971.Subspectral Law1685 := (show Law971.Subspectral Law2 from (ImplicationTransfer.singleton_971 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_973_2 : Law973.Subspectral Law1685 := (show Law973.Subspectral Law2 from (ImplicationTransfer.singleton_973 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_974_2 : Law974.Subspectral Law1685 := (show Law974.Subspectral Law2 from (ImplicationTransfer.singleton_974 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_975_2 : Law975.Subspectral Law1685 := (show Law975.Subspectral Law2 from (ImplicationTransfer.singleton_975 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_976_2 : Law976.Subspectral Law1685 := (show Law976.Subspectral Law2 from (ImplicationTransfer.singleton_976 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_979_2 : Law979.Subspectral Law1685 := (show Law979.Subspectral Law2 from (ImplicationTransfer.singleton_979 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_980_2 : Law980.Subspectral Law1685 := (show Law980.Subspectral Law2 from (ImplicationTransfer.singleton_980 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_982_2 : Law982.Subspectral Law1685 := (show Law982.Subspectral Law2 from (ImplicationTransfer.singleton_982 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_983_2 : Law983.Subspectral Law1685 := (show Law983.Subspectral Law2 from (ImplicationTransfer.singleton_983 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_984_2 : Law984.Subspectral Law1685 := (show Law984.Subspectral Law2 from (ImplicationTransfer.singleton_984 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_986_2 : Law986.Subspectral Law1685 := (show Law986.Subspectral Law2 from (ImplicationTransfer.singleton_986 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_987_2 : Law987.Subspectral Law1685 := (show Law987.Subspectral Law2 from (ImplicationTransfer.singleton_987 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_988_2 : Law988.Subspectral Law1685 := (show Law988.Subspectral Law2 from (ImplicationTransfer.singleton_988 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_990_2 : Law990.Subspectral Law1685 := (show Law990.Subspectral Law2 from (ImplicationTransfer.singleton_990 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_991_2 : Law991.Subspectral Law1685 := (show Law991.Subspectral Law2 from (ImplicationTransfer.singleton_991 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_992_2 : Law992.Subspectral Law1685 := (show Law992.Subspectral Law2 from (ImplicationTransfer.singleton_992 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_993_2 : Law993.Subspectral Law1685 := (show Law993.Subspectral Law2 from (ImplicationTransfer.singleton_993 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_995_2 : Law995.Subspectral Law1685 := (show Law995.Subspectral Law2 from (ImplicationTransfer.singleton_995 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_996_2 : Law996.Subspectral Law1685 := (show Law996.Subspectral Law2 from (ImplicationTransfer.singleton_996 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_997_2 : Law997.Subspectral Law1685 := (show Law997.Subspectral Law2 from (ImplicationTransfer.singleton_997 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_998_2 : Law998.Subspectral Law1685 := (show Law998.Subspectral Law2 from (ImplicationTransfer.singleton_998 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1000_2 : Law1000.Subspectral Law1685 := (show Law1000.Subspectral Law2 from (ImplicationTransfer.singleton_1000 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1001_2 : Law1001.Subspectral Law1685 := (show Law1001.Subspectral Law2 from (ImplicationTransfer.singleton_1001 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1002_2 : Law1002.Subspectral Law1685 := (show Law1002.Subspectral Law2 from (ImplicationTransfer.singleton_1002 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1003_2 : Law1003.Subspectral Law1685 := (show Law1003.Subspectral Law2 from (ImplicationTransfer.singleton_1003 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1005_2 : Law1005.Subspectral Law1685 := (show Law1005.Subspectral Law2 from (ImplicationTransfer.singleton_1005 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1006_2 : Law1006.Subspectral Law1685 := (show Law1006.Subspectral Law2 from (ImplicationTransfer.singleton_1006 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1007_2 : Law1007.Subspectral Law1685 := (show Law1007.Subspectral Law2 from (ImplicationTransfer.singleton_1007 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1008_2 : Law1008.Subspectral Law1685 := (show Law1008.Subspectral Law2 from (ImplicationTransfer.singleton_1008 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1010_2 : Law1010.Subspectral Law1685 := (show Law1010.Subspectral Law2 from (ImplicationTransfer.singleton_1010 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1011_2 : Law1011.Subspectral Law1685 := (show Law1011.Subspectral Law2 from (ImplicationTransfer.singleton_1011 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1012_2 : Law1012.Subspectral Law1685 := (show Law1012.Subspectral Law2 from (ImplicationTransfer.singleton_1012 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1013_2 : Law1013.Subspectral Law1685 := (show Law1013.Subspectral Law2 from (ImplicationTransfer.singleton_1013 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1015_2 : Law1015.Subspectral Law1685 := (show Law1015.Subspectral Law2 from (ImplicationTransfer.singleton_1015 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1016_2 : Law1016.Subspectral Law1685 := (show Law1016.Subspectral Law2 from (ImplicationTransfer.singleton_1016 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1017_2 : Law1017.Subspectral Law1685 := (show Law1017.Subspectral Law2 from (ImplicationTransfer.singleton_1017 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1018_2 : Law1018.Subspectral Law1685 := (show Law1018.Subspectral Law2 from (ImplicationTransfer.singleton_1018 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1019_2 : Law1019.Subspectral Law1685 := (show Law1019.Subspectral Law2 from (ImplicationTransfer.singleton_1019 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1074_2 : Law1074.Subspectral Law1685 := (show Law1074.Subspectral Law2 from (ImplicationTransfer.singleton_1074 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1076_2 : Law1076.Subspectral Law1076 := basis_route_1076_2

theorem route_1076_3 : Law1076.Subspectral Law1076 := basis_route_1076_3

theorem route_1076_4 : Law1076.Subspectral Law1076 := basis_route_1076_4

theorem route_1076_6 : Law1076.Subspectral Law1076 := basis_route_1076_6

theorem route_1076_7 : Law1076.Subspectral Law1076 := basis_route_1076_7

theorem route_1077_2 : Law1077.Subspectral Law1685 := (show Law1077.Subspectral Law2 from (ImplicationTransfer.singleton_1077 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1079_2 : Law1079.Subspectral Law1685 := (show Law1079.Subspectral Law2 from (ImplicationTransfer.singleton_1079 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1080_2 : Law1080.Subspectral Law1685 := (show Law1080.Subspectral Law2 from (ImplicationTransfer.singleton_1080 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1081_2 : Law1081.Subspectral Law1685 := (show Law1081.Subspectral Law2 from (ImplicationTransfer.singleton_1081 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1083_2 : Law1083.Subspectral Law1083 := basis_route_1083_2

theorem route_1084_2 : Law1084.Subspectral Law1685 := (show Law1084.Subspectral Law2 from (ImplicationTransfer.singleton_1084 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1087_2 : Law1087.Subspectral Law1685 := (show Law1087.Subspectral Law2 from (ImplicationTransfer.singleton_1087 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1089_2 : Law1089.Subspectral Law1685 := (show Law1089.Subspectral Law2 from (ImplicationTransfer.singleton_1089 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1091_2 : Law1091.Subspectral Law1685 := (show Law1091.Subspectral Law2 from (ImplicationTransfer.singleton_1091 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1093_2 : Law1093.Subspectral Law1685 := (show Law1093.Subspectral Law2 from (ImplicationTransfer.singleton_1093 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1094_2 : Law1094.Subspectral Law1685 := (show Law1094.Subspectral Law2 from (ImplicationTransfer.singleton_1094 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1095_2 : Law1095.Subspectral Law1685 := (show Law1095.Subspectral Law2 from (ImplicationTransfer.singleton_1095 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1097_2 : Law1097.Subspectral Law1685 := (show Law1097.Subspectral Law2 from (ImplicationTransfer.singleton_1097 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1098_3 : Law1098.Subspectral Law667 := (show Law1098.Subspectral Law546 from (ImplicationTransfer.spectrum_1098_eq_546).subset).trans basis_route_546_3

theorem route_1099_2 : Law1099.Subspectral Law1685 := (show Law1099.Subspectral Law2 from (ImplicationTransfer.singleton_1099 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1102_2 : Law1102.Subspectral Law1685 := (show Law1102.Subspectral Law2 from (ImplicationTransfer.singleton_1102 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1103_2 : Law1103.Subspectral Law1685 := (show Law1103.Subspectral Law2 from (ImplicationTransfer.singleton_1103 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1105_2 : Law1105.Subspectral Law1685 := (show Law1105.Subspectral Law2 from (ImplicationTransfer.singleton_1105 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1106_2 : Law1106.Subspectral Law1685 := (show Law1106.Subspectral Law2 from (ImplicationTransfer.singleton_1106 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1107_2 : Law1107.Subspectral Law1685 := (show Law1107.Subspectral Law2 from (ImplicationTransfer.singleton_1107 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1108_2 : Law1108.Subspectral Law1685 := (show Law1108.Subspectral Law2 from (ImplicationTransfer.singleton_1108 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1110_2 : Law1110.Subspectral Law1110 := basis_route_1110_2

theorem route_1110_3 : Law1110.Subspectral Law1110 := basis_route_1110_3

theorem route_1110_6 : Law1110.Subspectral Law1110 := basis_route_1110_6

theorem route_1111_2 : Law1111.Subspectral Law1685 := (show Law1111.Subspectral Law2 from (ImplicationTransfer.singleton_1111 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1114_2 : Law1114.Subspectral Law1685 := (show Law1114.Subspectral Law2 from (ImplicationTransfer.singleton_1114 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1116_2 : Law1116.Subspectral Law1685 := (show Law1116.Subspectral Law2 from (ImplicationTransfer.singleton_1116 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1118_2 : Law1118.Subspectral Law1685 := (show Law1118.Subspectral Law2 from (ImplicationTransfer.singleton_1118 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1121_2 : Law1121.Subspectral Law1685 := (show Law1121.Subspectral Law2 from (ImplicationTransfer.singleton_1121 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1123_2 : Law1123.Subspectral Law1685 := (show Law1123.Subspectral Law2 from (ImplicationTransfer.singleton_1123 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1124_2 : Law1124.Subspectral Law1685 := (show Law1124.Subspectral Law2 from (ImplicationTransfer.singleton_1124 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1126_2 : Law1126.Subspectral Law1685 := (show Law1126.Subspectral Law2 from (ImplicationTransfer.singleton_1126 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1127_2 : Law1127.Subspectral Law1685 := (show Law1127.Subspectral Law2 from (ImplicationTransfer.singleton_1127 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1128_2 : Law1128.Subspectral Law1685 := (show Law1128.Subspectral Law2 from (ImplicationTransfer.singleton_1128 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1130_2 : Law1130.Subspectral Law1685 := (show Law1130.Subspectral Law2 from (ImplicationTransfer.singleton_1130 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1131_3 : Law1131.Subspectral Law667 := (show Law1131.Subspectral Law556 from (ImplicationTransfer.spectrum_1131_eq_556).subset).trans basis_route_556_3

theorem route_1132_2 : Law1132.Subspectral Law1685 := (show Law1132.Subspectral Law2 from (ImplicationTransfer.singleton_1132 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1134_2 : Law1134.Subspectral Law1685 := (show Law1134.Subspectral Law2 from (ImplicationTransfer.singleton_1134 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1135_2 : Law1135.Subspectral Law1685 := (show Law1135.Subspectral Law2 from (ImplicationTransfer.singleton_1135 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1136_2 : Law1136.Subspectral Law1685 := (show Law1136.Subspectral Law2 from (ImplicationTransfer.singleton_1136 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1138_2 : Law1138.Subspectral Law1685 := (show Law1138.Subspectral Law2 from (ImplicationTransfer.singleton_1138 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1139_2 : Law1139.Subspectral Law1685 := (show Law1139.Subspectral Law2 from (ImplicationTransfer.singleton_1139 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1140_2 : Law1140.Subspectral Law1685 := (show Law1140.Subspectral Law2 from (ImplicationTransfer.singleton_1140 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1142_2 : Law1142.Subspectral Law1685 := (show Law1142.Subspectral Law2 from (ImplicationTransfer.singleton_1142 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1143_2 : Law1143.Subspectral Law1685 := (show Law1143.Subspectral Law2 from (ImplicationTransfer.singleton_1143 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1144_2 : Law1144.Subspectral Law1685 := (show Law1144.Subspectral Law2 from (ImplicationTransfer.singleton_1144 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1145_2 : Law1145.Subspectral Law1685 := (show Law1145.Subspectral Law2 from (ImplicationTransfer.singleton_1145 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1147_2 : Law1147.Subspectral Law1685 := (show Law1147.Subspectral Law2 from (ImplicationTransfer.singleton_1147 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1148_2 : Law1148.Subspectral Law1685 := (show Law1148.Subspectral Law2 from (ImplicationTransfer.singleton_1148 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1149_2 : Law1149.Subspectral Law1685 := (show Law1149.Subspectral Law2 from (ImplicationTransfer.singleton_1149 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1151_2 : Law1151.Subspectral Law1685 := (show Law1151.Subspectral Law2 from (ImplicationTransfer.singleton_1151 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1153_2 : Law1153.Subspectral Law1685 := (show Law1153.Subspectral Law2 from (ImplicationTransfer.singleton_1153 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1156_2 : Law1156.Subspectral Law1685 := (show Law1156.Subspectral Law2 from (ImplicationTransfer.singleton_1156 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1157_2 : Law1157.Subspectral Law1685 := (show Law1157.Subspectral Law2 from (ImplicationTransfer.singleton_1157 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1159_2 : Law1159.Subspectral Law1685 := (show Law1159.Subspectral Law2 from (ImplicationTransfer.singleton_1159 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1160_2 : Law1160.Subspectral Law1685 := (show Law1160.Subspectral Law2 from (ImplicationTransfer.singleton_1160 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1161_2 : Law1161.Subspectral Law1685 := (show Law1161.Subspectral Law2 from (ImplicationTransfer.singleton_1161 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1162_2 : Law1162.Subspectral Law1685 := (show Law1162.Subspectral Law2 from (ImplicationTransfer.singleton_1162 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1164_2 : Law1164.Subspectral Law1685 := (show Law1164.Subspectral Law2 from (ImplicationTransfer.singleton_1164 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1166_2 : Law1166.Subspectral Law1685 := (show Law1166.Subspectral Law2 from (ImplicationTransfer.singleton_1166 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1168_2 : Law1168.Subspectral Law1685 := (show Law1168.Subspectral Law2 from (ImplicationTransfer.singleton_1168 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1169_2 : Law1169.Subspectral Law1685 := (show Law1169.Subspectral Law2 from (ImplicationTransfer.singleton_1169 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1170_2 : Law1170.Subspectral Law1685 := (show Law1170.Subspectral Law2 from (ImplicationTransfer.singleton_1170 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1172_2 : Law1172.Subspectral Law1685 := (show Law1172.Subspectral Law2 from (ImplicationTransfer.singleton_1172 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1173_2 : Law1173.Subspectral Law1685 := (show Law1173.Subspectral Law2 from (ImplicationTransfer.singleton_1173 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1174_2 : Law1174.Subspectral Law1685 := (show Law1174.Subspectral Law2 from (ImplicationTransfer.singleton_1174 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1176_2 : Law1176.Subspectral Law1685 := (show Law1176.Subspectral Law2 from (ImplicationTransfer.singleton_1176 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1177_2 : Law1177.Subspectral Law1685 := (show Law1177.Subspectral Law2 from (ImplicationTransfer.singleton_1177 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1178_2 : Law1178.Subspectral Law1685 := (show Law1178.Subspectral Law2 from (ImplicationTransfer.singleton_1178 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1179_2 : Law1179.Subspectral Law1685 := (show Law1179.Subspectral Law2 from (ImplicationTransfer.singleton_1179 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1182_2 : Law1182.Subspectral Law1685 := (show Law1182.Subspectral Law2 from (ImplicationTransfer.singleton_1182 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1183_2 : Law1183.Subspectral Law1685 := (show Law1183.Subspectral Law2 from (ImplicationTransfer.singleton_1183 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1185_2 : Law1185.Subspectral Law1685 := (show Law1185.Subspectral Law2 from (ImplicationTransfer.singleton_1185 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1186_2 : Law1186.Subspectral Law1685 := (show Law1186.Subspectral Law2 from (ImplicationTransfer.singleton_1186 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1187_2 : Law1187.Subspectral Law1685 := (show Law1187.Subspectral Law2 from (ImplicationTransfer.singleton_1187 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1189_2 : Law1189.Subspectral Law1685 := (show Law1189.Subspectral Law2 from (ImplicationTransfer.singleton_1189 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1190_2 : Law1190.Subspectral Law1685 := (show Law1190.Subspectral Law2 from (ImplicationTransfer.singleton_1190 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1191_2 : Law1191.Subspectral Law1685 := (show Law1191.Subspectral Law2 from (ImplicationTransfer.singleton_1191 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1193_2 : Law1193.Subspectral Law1685 := (show Law1193.Subspectral Law2 from (ImplicationTransfer.singleton_1193 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1194_2 : Law1194.Subspectral Law1685 := (show Law1194.Subspectral Law2 from (ImplicationTransfer.singleton_1194 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1195_2 : Law1195.Subspectral Law1685 := (show Law1195.Subspectral Law2 from (ImplicationTransfer.singleton_1195 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1196_2 : Law1196.Subspectral Law1685 := (show Law1196.Subspectral Law2 from (ImplicationTransfer.singleton_1196 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1198_2 : Law1198.Subspectral Law1685 := (show Law1198.Subspectral Law2 from (ImplicationTransfer.singleton_1198 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1199_2 : Law1199.Subspectral Law1685 := (show Law1199.Subspectral Law2 from (ImplicationTransfer.singleton_1199 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1200_2 : Law1200.Subspectral Law1685 := (show Law1200.Subspectral Law2 from (ImplicationTransfer.singleton_1200 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1201_2 : Law1201.Subspectral Law1685 := (show Law1201.Subspectral Law2 from (ImplicationTransfer.singleton_1201 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1203_2 : Law1203.Subspectral Law1685 := (show Law1203.Subspectral Law2 from (ImplicationTransfer.singleton_1203 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1204_2 : Law1204.Subspectral Law1685 := (show Law1204.Subspectral Law2 from (ImplicationTransfer.singleton_1204 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1205_2 : Law1205.Subspectral Law1685 := (show Law1205.Subspectral Law2 from (ImplicationTransfer.singleton_1205 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1206_2 : Law1206.Subspectral Law1685 := (show Law1206.Subspectral Law2 from (ImplicationTransfer.singleton_1206 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1208_2 : Law1208.Subspectral Law1685 := (show Law1208.Subspectral Law2 from (ImplicationTransfer.singleton_1208 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1209_2 : Law1209.Subspectral Law1685 := (show Law1209.Subspectral Law2 from (ImplicationTransfer.singleton_1209 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1210_2 : Law1210.Subspectral Law1685 := (show Law1210.Subspectral Law2 from (ImplicationTransfer.singleton_1210 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1211_2 : Law1211.Subspectral Law1685 := (show Law1211.Subspectral Law2 from (ImplicationTransfer.singleton_1211 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1213_2 : Law1213.Subspectral Law1685 := (show Law1213.Subspectral Law2 from (ImplicationTransfer.singleton_1213 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1214_2 : Law1214.Subspectral Law1685 := (show Law1214.Subspectral Law2 from (ImplicationTransfer.singleton_1214 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1215_2 : Law1215.Subspectral Law1685 := (show Law1215.Subspectral Law2 from (ImplicationTransfer.singleton_1215 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1216_2 : Law1216.Subspectral Law1685 := (show Law1216.Subspectral Law2 from (ImplicationTransfer.singleton_1216 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1218_2 : Law1218.Subspectral Law1685 := (show Law1218.Subspectral Law2 from (ImplicationTransfer.singleton_1218 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1219_2 : Law1219.Subspectral Law1685 := (show Law1219.Subspectral Law2 from (ImplicationTransfer.singleton_1219 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1220_2 : Law1220.Subspectral Law1685 := (show Law1220.Subspectral Law2 from (ImplicationTransfer.singleton_1220 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1221_2 : Law1221.Subspectral Law1685 := (show Law1221.Subspectral Law2 from (ImplicationTransfer.singleton_1221 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1222_2 : Law1222.Subspectral Law1685 := (show Law1222.Subspectral Law2 from (ImplicationTransfer.singleton_1222 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1277_2 : Law1277.Subspectral Law1685 := (show Law1277.Subspectral Law2 from (ImplicationTransfer.singleton_1277 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1279_2 : Law1279.Subspectral Law1279 := basis_route_1279_2

theorem route_1279_3 : Law1279.Subspectral Law1279 := basis_route_1279_3

theorem route_1279_4 : Law1279.Subspectral Law1279 := basis_route_1279_4

theorem route_1279_6 : Law1279.Subspectral Law1279 := basis_route_1279_6

theorem route_1279_9 : Law1279.Subspectral Law1279 := basis_route_1279_9

theorem route_1280_2 : Law1280.Subspectral Law1685 := (show Law1280.Subspectral Law2 from (ImplicationTransfer.singleton_1280 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1282_2 : Law1282.Subspectral Law1685 := (show Law1282.Subspectral Law2 from (ImplicationTransfer.singleton_1282 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1283_2 : Law1283.Subspectral Law1685 := (show Law1283.Subspectral Law2 from (ImplicationTransfer.singleton_1283 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1284_2 : Law1284.Subspectral Law1685 := (show Law1284.Subspectral Law2 from (ImplicationTransfer.singleton_1284 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1286_2 : Law1286.Subspectral Law1286 := basis_route_1286_2

theorem route_1286_3 : Law1286.Subspectral Law1286 := basis_route_1286_3

theorem route_1286_4 : Law1286.Subspectral Law1286 := basis_route_1286_4

theorem route_1286_5 : Law1286.Subspectral Law1286 := basis_route_1286_5

theorem route_1286_6 : Law1286.Subspectral Law1286 := basis_route_1286_6

theorem route_1287_2 : Law1287.Subspectral Law1685 := (show Law1287.Subspectral Law2 from (ImplicationTransfer.singleton_1287 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1290_2 : Law1290.Subspectral Law1685 := (show Law1290.Subspectral Law2 from (ImplicationTransfer.singleton_1290 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1292_2 : Law1292.Subspectral Law1685 := (show Law1292.Subspectral Law2 from (ImplicationTransfer.singleton_1292 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1294_2 : Law1294.Subspectral Law1685 := (show Law1294.Subspectral Law2 from (ImplicationTransfer.singleton_1294 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1296_2 : Law1296.Subspectral Law1685 := (show Law1296.Subspectral Law2 from (ImplicationTransfer.singleton_1296 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1297_2 : Law1297.Subspectral Law1685 := (show Law1297.Subspectral Law2 from (ImplicationTransfer.singleton_1297 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1298_2 : Law1298.Subspectral Law1685 := (show Law1298.Subspectral Law2 from (ImplicationTransfer.singleton_1298 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1300_2 : Law1300.Subspectral Law1685 := (show Law1300.Subspectral Law2 from (ImplicationTransfer.singleton_1300 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1301_3 : Law1301.Subspectral Law667 := (show Law1301.Subspectral Law556 from (ImplicationTransfer.spectrum_1301_eq_556).subset).trans basis_route_556_3

theorem route_1302_2 : Law1302.Subspectral Law1685 := (show Law1302.Subspectral Law2 from (ImplicationTransfer.singleton_1302 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1305_2 : Law1305.Subspectral Law1685 := (show Law1305.Subspectral Law2 from (ImplicationTransfer.singleton_1305 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1306_2 : Law1306.Subspectral Law1685 := (show Law1306.Subspectral Law2 from (ImplicationTransfer.singleton_1306 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1308_2 : Law1308.Subspectral Law1685 := (show Law1308.Subspectral Law2 from (ImplicationTransfer.singleton_1308 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1309_2 : Law1309.Subspectral Law1685 := (show Law1309.Subspectral Law2 from (ImplicationTransfer.singleton_1309 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1310_2 : Law1310.Subspectral Law1685 := (show Law1310.Subspectral Law2 from (ImplicationTransfer.singleton_1310 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1311_2 : Law1311.Subspectral Law1685 := (show Law1311.Subspectral Law2 from (ImplicationTransfer.singleton_1311 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1313_2 : Law1313.Subspectral Law1313 := basis_route_1313_2

theorem route_1313_3 : Law1313.Subspectral Law1313 := basis_route_1313_3

theorem route_1313_4 : Law1313.Subspectral Law1313 := basis_route_1313_4

theorem route_1313_6 : Law1313.Subspectral Law1313 := basis_route_1313_6

theorem route_1314_2 : Law1314.Subspectral Law1685 := (show Law1314.Subspectral Law2 from (ImplicationTransfer.singleton_1314 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1317_2 : Law1317.Subspectral Law1685 := (show Law1317.Subspectral Law2 from (ImplicationTransfer.singleton_1317 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1319_2 : Law1319.Subspectral Law1685 := (show Law1319.Subspectral Law2 from (ImplicationTransfer.singleton_1319 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1321_2 : Law1321.Subspectral Law1685 := (show Law1321.Subspectral Law2 from (ImplicationTransfer.singleton_1321 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1323_3 : Law1323.Subspectral Law883 := basis_route_1323_3

theorem route_1324_2 : Law1324.Subspectral Law1685 := (show Law1324.Subspectral Law2 from (ImplicationTransfer.singleton_1324 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1326_2 : Law1326.Subspectral Law1685 := (show Law1326.Subspectral Law2 from (ImplicationTransfer.singleton_1326 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1327_2 : Law1327.Subspectral Law1685 := (show Law1327.Subspectral Law2 from (ImplicationTransfer.singleton_1327 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1329_2 : Law1329.Subspectral Law1685 := (show Law1329.Subspectral Law2 from (ImplicationTransfer.singleton_1329 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1330_2 : Law1330.Subspectral Law1685 := (show Law1330.Subspectral Law2 from (ImplicationTransfer.singleton_1330 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1331_2 : Law1331.Subspectral Law1685 := (show Law1331.Subspectral Law2 from (ImplicationTransfer.singleton_1331 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1333_2 : Law1333.Subspectral Law1685 := (show Law1333.Subspectral Law2 from (ImplicationTransfer.singleton_1333 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1334_3 : Law1334.Subspectral Law667 := (show Law1334.Subspectral Law895 from (ImplicationTransfer.spectrum_1334_eq_895).subset).trans basis_route_895_3

theorem route_1335_2 : Law1335.Subspectral Law1685 := (show Law1335.Subspectral Law2 from (ImplicationTransfer.singleton_1335 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1337_2 : Law1337.Subspectral Law1685 := (show Law1337.Subspectral Law2 from (ImplicationTransfer.singleton_1337 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1338_2 : Law1338.Subspectral Law1685 := (show Law1338.Subspectral Law2 from (ImplicationTransfer.singleton_1338 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1339_2 : Law1339.Subspectral Law1685 := (show Law1339.Subspectral Law2 from (ImplicationTransfer.singleton_1339 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1341_2 : Law1341.Subspectral Law1685 := (show Law1341.Subspectral Law2 from (ImplicationTransfer.singleton_1341 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1342_2 : Law1342.Subspectral Law1685 := (show Law1342.Subspectral Law2 from (ImplicationTransfer.singleton_1342 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1343_2 : Law1343.Subspectral Law1685 := (show Law1343.Subspectral Law2 from (ImplicationTransfer.singleton_1343 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1345_2 : Law1345.Subspectral Law1685 := (show Law1345.Subspectral Law2 from (ImplicationTransfer.singleton_1345 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1346_2 : Law1346.Subspectral Law1685 := (show Law1346.Subspectral Law2 from (ImplicationTransfer.singleton_1346 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1347_2 : Law1347.Subspectral Law1685 := (show Law1347.Subspectral Law2 from (ImplicationTransfer.singleton_1347 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1348_2 : Law1348.Subspectral Law1685 := (show Law1348.Subspectral Law2 from (ImplicationTransfer.singleton_1348 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1350_2 : Law1350.Subspectral Law1685 := (show Law1350.Subspectral Law2 from (ImplicationTransfer.singleton_1350 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1351_2 : Law1351.Subspectral Law1685 := (show Law1351.Subspectral Law2 from (ImplicationTransfer.singleton_1351 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1352_2 : Law1352.Subspectral Law1685 := (show Law1352.Subspectral Law2 from (ImplicationTransfer.singleton_1352 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1354_2 : Law1354.Subspectral Law1685 := (show Law1354.Subspectral Law2 from (ImplicationTransfer.singleton_1354 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1355_3 : Law1355.Subspectral Law667 := (show Law1355.Subspectral Law556 from (ImplicationTransfer.spectrum_1355_eq_556).subset).trans basis_route_556_3

theorem route_1356_2 : Law1356.Subspectral Law1685 := (show Law1356.Subspectral Law2 from (ImplicationTransfer.singleton_1356 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1359_2 : Law1359.Subspectral Law1685 := (show Law1359.Subspectral Law2 from (ImplicationTransfer.singleton_1359 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1360_2 : Law1360.Subspectral Law1685 := (show Law1360.Subspectral Law2 from (ImplicationTransfer.singleton_1360 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1362_2 : Law1362.Subspectral Law1685 := (show Law1362.Subspectral Law2 from (ImplicationTransfer.singleton_1362 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1363_2 : Law1363.Subspectral Law1685 := (show Law1363.Subspectral Law2 from (ImplicationTransfer.singleton_1363 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1364_2 : Law1364.Subspectral Law1685 := (show Law1364.Subspectral Law2 from (ImplicationTransfer.singleton_1364 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1365_2 : Law1365.Subspectral Law1685 := (show Law1365.Subspectral Law2 from (ImplicationTransfer.singleton_1365 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1367_2 : Law1367.Subspectral Law1685 := (show Law1367.Subspectral Law2 from (ImplicationTransfer.singleton_1367 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1368_3 : Law1368.Subspectral Law667 := (show Law1368.Subspectral Law898 from (ImplicationTransfer.spectrum_1368_eq_898).subset).trans basis_route_898_3

theorem route_1369_2 : Law1369.Subspectral Law1685 := (show Law1369.Subspectral Law2 from (ImplicationTransfer.singleton_1369 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1371_2 : Law1371.Subspectral Law1685 := (show Law1371.Subspectral Law2 from (ImplicationTransfer.singleton_1371 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1372_2 : Law1372.Subspectral Law1685 := (show Law1372.Subspectral Law2 from (ImplicationTransfer.singleton_1372 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1373_2 : Law1373.Subspectral Law1685 := (show Law1373.Subspectral Law2 from (ImplicationTransfer.singleton_1373 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1375_2 : Law1375.Subspectral Law1685 := (show Law1375.Subspectral Law2 from (ImplicationTransfer.singleton_1375 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1376_2 : Law1376.Subspectral Law1685 := (show Law1376.Subspectral Law2 from (ImplicationTransfer.singleton_1376 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1377_2 : Law1377.Subspectral Law1685 := (show Law1377.Subspectral Law2 from (ImplicationTransfer.singleton_1377 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1379_2 : Law1379.Subspectral Law1685 := (show Law1379.Subspectral Law2 from (ImplicationTransfer.singleton_1379 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1380_2 : Law1380.Subspectral Law1685 := (show Law1380.Subspectral Law2 from (ImplicationTransfer.singleton_1380 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1381_2 : Law1381.Subspectral Law1685 := (show Law1381.Subspectral Law2 from (ImplicationTransfer.singleton_1381 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1382_2 : Law1382.Subspectral Law1685 := (show Law1382.Subspectral Law2 from (ImplicationTransfer.singleton_1382 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1384_3 : Law1384.Subspectral Law667 := (show Law1384.Subspectral Law887 from (ImplicationTransfer.spectrum_1384_eq_887).subset).trans basis_route_887_3

theorem route_1385_2 : Law1385.Subspectral Law1685 := (show Law1385.Subspectral Law2 from (ImplicationTransfer.singleton_1385 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1386_2 : Law1386.Subspectral Law1685 := (show Law1386.Subspectral Law2 from (ImplicationTransfer.singleton_1386 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1388_2 : Law1388.Subspectral Law1685 := (show Law1388.Subspectral Law2 from (ImplicationTransfer.singleton_1388 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1389_2 : Law1389.Subspectral Law1685 := (show Law1389.Subspectral Law2 from (ImplicationTransfer.singleton_1389 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1390_2 : Law1390.Subspectral Law1685 := (show Law1390.Subspectral Law2 from (ImplicationTransfer.singleton_1390 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1392_2 : Law1392.Subspectral Law1685 := (show Law1392.Subspectral Law2 from (ImplicationTransfer.singleton_1392 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1393_2 : Law1393.Subspectral Law1685 := (show Law1393.Subspectral Law2 from (ImplicationTransfer.singleton_1393 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1394_2 : Law1394.Subspectral Law1685 := (show Law1394.Subspectral Law2 from (ImplicationTransfer.singleton_1394 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1396_2 : Law1396.Subspectral Law1685 := (show Law1396.Subspectral Law2 from (ImplicationTransfer.singleton_1396 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1397_2 : Law1397.Subspectral Law1685 := (show Law1397.Subspectral Law2 from (ImplicationTransfer.singleton_1397 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1398_2 : Law1398.Subspectral Law1685 := (show Law1398.Subspectral Law2 from (ImplicationTransfer.singleton_1398 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1399_2 : Law1399.Subspectral Law1685 := (show Law1399.Subspectral Law2 from (ImplicationTransfer.singleton_1399 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1401_2 : Law1401.Subspectral Law1685 := (show Law1401.Subspectral Law2 from (ImplicationTransfer.singleton_1401 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1402_2 : Law1402.Subspectral Law1685 := (show Law1402.Subspectral Law2 from (ImplicationTransfer.singleton_1402 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1403_2 : Law1403.Subspectral Law1685 := (show Law1403.Subspectral Law2 from (ImplicationTransfer.singleton_1403 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1404_2 : Law1404.Subspectral Law1685 := (show Law1404.Subspectral Law2 from (ImplicationTransfer.singleton_1404 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1406_2 : Law1406.Subspectral Law1685 := (show Law1406.Subspectral Law2 from (ImplicationTransfer.singleton_1406 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1407_2 : Law1407.Subspectral Law1685 := (show Law1407.Subspectral Law2 from (ImplicationTransfer.singleton_1407 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1408_2 : Law1408.Subspectral Law1685 := (show Law1408.Subspectral Law2 from (ImplicationTransfer.singleton_1408 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1409_2 : Law1409.Subspectral Law1685 := (show Law1409.Subspectral Law2 from (ImplicationTransfer.singleton_1409 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1411_2 : Law1411.Subspectral Law1685 := (show Law1411.Subspectral Law2 from (ImplicationTransfer.singleton_1411 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1412_2 : Law1412.Subspectral Law1685 := (show Law1412.Subspectral Law2 from (ImplicationTransfer.singleton_1412 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1413_2 : Law1413.Subspectral Law1685 := (show Law1413.Subspectral Law2 from (ImplicationTransfer.singleton_1413 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1414_2 : Law1414.Subspectral Law1685 := (show Law1414.Subspectral Law2 from (ImplicationTransfer.singleton_1414 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1416_2 : Law1416.Subspectral Law1685 := (show Law1416.Subspectral Law2 from (ImplicationTransfer.singleton_1416 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1417_2 : Law1417.Subspectral Law1685 := (show Law1417.Subspectral Law2 from (ImplicationTransfer.singleton_1417 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1418_2 : Law1418.Subspectral Law1685 := (show Law1418.Subspectral Law2 from (ImplicationTransfer.singleton_1418 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1419_2 : Law1419.Subspectral Law1685 := (show Law1419.Subspectral Law2 from (ImplicationTransfer.singleton_1419 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1421_2 : Law1421.Subspectral Law1685 := (show Law1421.Subspectral Law2 from (ImplicationTransfer.singleton_1421 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1422_2 : Law1422.Subspectral Law1685 := (show Law1422.Subspectral Law2 from (ImplicationTransfer.singleton_1422 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1423_2 : Law1423.Subspectral Law1685 := (show Law1423.Subspectral Law2 from (ImplicationTransfer.singleton_1423 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1424_2 : Law1424.Subspectral Law1685 := (show Law1424.Subspectral Law2 from (ImplicationTransfer.singleton_1424 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1425_2 : Law1425.Subspectral Law1685 := (show Law1425.Subspectral Law2 from (ImplicationTransfer.singleton_1425 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1480_2 : Law1480.Subspectral Law1480 := basis_route_1480_2

theorem route_1480_3 : Law1480.Subspectral Law1480 := basis_route_1480_3

theorem route_1483_3 : Law1483.Subspectral Law1483 := basis_route_1483_3

theorem route_1483_5 : Law1483.Subspectral Law1483 := basis_route_1483_5

theorem route_1483_6 : Law1483.Subspectral Law1483 := basis_route_1483_6

theorem route_1483_7 : Law1483.Subspectral Law1483 := basis_route_1483_7

theorem route_1485_3 : Law1485.Subspectral Law1485 := basis_route_1485_3

theorem route_1486_2 : Law1486.Subspectral Law1486 := basis_route_1486_2

theorem route_1487_2 : Law1487.Subspectral Law167 := (show Law1487.Subspectral Law168 from (ImplicationTransfer.spectrum_1487_eq_168).subset).trans basis_route_168_2

theorem route_1489_2 : Law1489.Subspectral Law1489 := basis_route_1489_2

theorem route_1489_4 : Law1489.Subspectral Law1489 := basis_route_1489_4

theorem route_1490_2 : Law1490.Subspectral Law1685 := (show Law1490.Subspectral Law2 from (ImplicationTransfer.singleton_1490 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1493_2 : Law1493.Subspectral Law1685 := (show Law1493.Subspectral Law2 from (ImplicationTransfer.singleton_1493 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1495_2 : Law1495.Subspectral Law1685 := (show Law1495.Subspectral Law2 from (ImplicationTransfer.singleton_1495 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1496_3 : Law1496.Subspectral Law481 := basis_route_1496_3

theorem route_1497_2 : Law1497.Subspectral Law1685 := (show Law1497.Subspectral Law2 from (ImplicationTransfer.singleton_1497 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1499_2 : Law1499.Subspectral Law1685 := (show Law1499.Subspectral Law2 from (ImplicationTransfer.singleton_1499 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1500_2 : Law1500.Subspectral Law1685 := (show Law1500.Subspectral Law2 from (ImplicationTransfer.singleton_1500 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1501_2 : Law1501.Subspectral Law1685 := (show Law1501.Subspectral Law2 from (ImplicationTransfer.singleton_1501 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1503_2 : Law1503.Subspectral Law1685 := (show Law1503.Subspectral Law2 from (ImplicationTransfer.singleton_1503 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1505_2 : Law1505.Subspectral Law1685 := (show Law1505.Subspectral Law2 from (ImplicationTransfer.singleton_1505 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1508_2 : Law1508.Subspectral Law1685 := (show Law1508.Subspectral Law2 from (ImplicationTransfer.singleton_1508 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1509_2 : Law1509.Subspectral Law1685 := (show Law1509.Subspectral Law2 from (ImplicationTransfer.singleton_1509 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1511_2 : Law1511.Subspectral Law1685 := (show Law1511.Subspectral Law2 from (ImplicationTransfer.singleton_1511 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1512_2 : Law1512.Subspectral Law1685 := (show Law1512.Subspectral Law2 from (ImplicationTransfer.singleton_1512 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1513_2 : Law1513.Subspectral Law1685 := (show Law1513.Subspectral Law2 from (ImplicationTransfer.singleton_1513 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1514_2 : Law1514.Subspectral Law1685 := (show Law1514.Subspectral Law2 from (ImplicationTransfer.singleton_1514 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1516_2 : Law1516.Subspectral Law1516 := basis_route_1516_2

theorem route_1516_3 : Law1516.Subspectral Law1516 := basis_route_1516_3

theorem route_1516_4 : Law1516.Subspectral Law1516 := basis_route_1516_4

theorem route_1516_6 : Law1516.Subspectral Law1516 := basis_route_1516_6

theorem route_1517_2 : Law1517.Subspectral Law1685 := (show Law1517.Subspectral Law2 from (ImplicationTransfer.singleton_1517 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1520_2 : Law1520.Subspectral Law1685 := (show Law1520.Subspectral Law2 from (ImplicationTransfer.singleton_1520 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1522_2 : Law1522.Subspectral Law1685 := (show Law1522.Subspectral Law2 from (ImplicationTransfer.singleton_1522 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1524_2 : Law1524.Subspectral Law1685 := (show Law1524.Subspectral Law2 from (ImplicationTransfer.singleton_1524 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1526_3 : Law1526.Subspectral Law883 := basis_route_1526_3

theorem route_1527_2 : Law1527.Subspectral Law1685 := (show Law1527.Subspectral Law2 from (ImplicationTransfer.singleton_1527 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1529_2 : Law1529.Subspectral Law1685 := (show Law1529.Subspectral Law2 from (ImplicationTransfer.singleton_1529 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1530_2 : Law1530.Subspectral Law1685 := (show Law1530.Subspectral Law2 from (ImplicationTransfer.singleton_1530 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1532_2 : Law1532.Subspectral Law1685 := (show Law1532.Subspectral Law2 from (ImplicationTransfer.singleton_1532 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1533_2 : Law1533.Subspectral Law1685 := (show Law1533.Subspectral Law2 from (ImplicationTransfer.singleton_1533 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1534_2 : Law1534.Subspectral Law1685 := (show Law1534.Subspectral Law2 from (ImplicationTransfer.singleton_1534 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1536_2 : Law1536.Subspectral Law1685 := (show Law1536.Subspectral Law2 from (ImplicationTransfer.singleton_1536 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1537_3 : Law1537.Subspectral Law667 := (show Law1537.Subspectral Law887 from (ImplicationTransfer.spectrum_1537_eq_887).subset).trans basis_route_887_3

theorem route_1538_2 : Law1538.Subspectral Law1685 := (show Law1538.Subspectral Law2 from (ImplicationTransfer.singleton_1538 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1540_2 : Law1540.Subspectral Law1685 := (show Law1540.Subspectral Law2 from (ImplicationTransfer.singleton_1540 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1541_2 : Law1541.Subspectral Law1685 := (show Law1541.Subspectral Law2 from (ImplicationTransfer.singleton_1541 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1542_2 : Law1542.Subspectral Law1685 := (show Law1542.Subspectral Law2 from (ImplicationTransfer.singleton_1542 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1544_2 : Law1544.Subspectral Law1685 := (show Law1544.Subspectral Law2 from (ImplicationTransfer.singleton_1544 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1545_2 : Law1545.Subspectral Law1685 := (show Law1545.Subspectral Law2 from (ImplicationTransfer.singleton_1545 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1546_2 : Law1546.Subspectral Law1685 := (show Law1546.Subspectral Law2 from (ImplicationTransfer.singleton_1546 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1548_2 : Law1548.Subspectral Law1685 := (show Law1548.Subspectral Law2 from (ImplicationTransfer.singleton_1548 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1549_2 : Law1549.Subspectral Law1685 := (show Law1549.Subspectral Law2 from (ImplicationTransfer.singleton_1549 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1550_2 : Law1550.Subspectral Law1685 := (show Law1550.Subspectral Law2 from (ImplicationTransfer.singleton_1550 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1551_2 : Law1551.Subspectral Law1685 := (show Law1551.Subspectral Law2 from (ImplicationTransfer.singleton_1551 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1553_2 : Law1553.Subspectral Law1685 := (show Law1553.Subspectral Law2 from (ImplicationTransfer.singleton_1553 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1554_2 : Law1554.Subspectral Law1685 := (show Law1554.Subspectral Law2 from (ImplicationTransfer.singleton_1554 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1555_2 : Law1555.Subspectral Law1685 := (show Law1555.Subspectral Law2 from (ImplicationTransfer.singleton_1555 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1557_2 : Law1557.Subspectral Law1685 := (show Law1557.Subspectral Law2 from (ImplicationTransfer.singleton_1557 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1559_2 : Law1559.Subspectral Law1685 := (show Law1559.Subspectral Law2 from (ImplicationTransfer.singleton_1559 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1562_2 : Law1562.Subspectral Law1685 := (show Law1562.Subspectral Law2 from (ImplicationTransfer.singleton_1562 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1563_2 : Law1563.Subspectral Law1685 := (show Law1563.Subspectral Law2 from (ImplicationTransfer.singleton_1563 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1565_2 : Law1565.Subspectral Law1685 := (show Law1565.Subspectral Law2 from (ImplicationTransfer.singleton_1565 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1566_2 : Law1566.Subspectral Law1685 := (show Law1566.Subspectral Law2 from (ImplicationTransfer.singleton_1566 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1567_2 : Law1567.Subspectral Law1685 := (show Law1567.Subspectral Law2 from (ImplicationTransfer.singleton_1567 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1568_2 : Law1568.Subspectral Law1685 := (show Law1568.Subspectral Law2 from (ImplicationTransfer.singleton_1568 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1570_2 : Law1570.Subspectral Law1685 := (show Law1570.Subspectral Law2 from (ImplicationTransfer.singleton_1570 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1571_3 : Law1571.Subspectral Law667 := (show Law1571.Subspectral Law895 from (ImplicationTransfer.spectrum_1571_eq_895).subset).trans basis_route_895_3

theorem route_1572_2 : Law1572.Subspectral Law1685 := (show Law1572.Subspectral Law2 from (ImplicationTransfer.singleton_1572 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1574_2 : Law1574.Subspectral Law1685 := (show Law1574.Subspectral Law2 from (ImplicationTransfer.singleton_1574 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1575_2 : Law1575.Subspectral Law1685 := (show Law1575.Subspectral Law2 from (ImplicationTransfer.singleton_1575 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1576_2 : Law1576.Subspectral Law1685 := (show Law1576.Subspectral Law2 from (ImplicationTransfer.singleton_1576 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1578_2 : Law1578.Subspectral Law1685 := (show Law1578.Subspectral Law2 from (ImplicationTransfer.singleton_1578 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1579_2 : Law1579.Subspectral Law1685 := (show Law1579.Subspectral Law2 from (ImplicationTransfer.singleton_1579 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1580_2 : Law1580.Subspectral Law1685 := (show Law1580.Subspectral Law2 from (ImplicationTransfer.singleton_1580 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1582_2 : Law1582.Subspectral Law1685 := (show Law1582.Subspectral Law2 from (ImplicationTransfer.singleton_1582 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1583_2 : Law1583.Subspectral Law1685 := (show Law1583.Subspectral Law2 from (ImplicationTransfer.singleton_1583 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1584_2 : Law1584.Subspectral Law1685 := (show Law1584.Subspectral Law2 from (ImplicationTransfer.singleton_1584 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1585_2 : Law1585.Subspectral Law1685 := (show Law1585.Subspectral Law2 from (ImplicationTransfer.singleton_1585 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1587_3 : Law1587.Subspectral Law667 := (show Law1587.Subspectral Law898 from (ImplicationTransfer.spectrum_1587_eq_898).subset).trans basis_route_898_3

theorem route_1588_2 : Law1588.Subspectral Law1685 := (show Law1588.Subspectral Law2 from (ImplicationTransfer.singleton_1588 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1589_2 : Law1589.Subspectral Law1685 := (show Law1589.Subspectral Law2 from (ImplicationTransfer.singleton_1589 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1591_2 : Law1591.Subspectral Law1685 := (show Law1591.Subspectral Law2 from (ImplicationTransfer.singleton_1591 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1592_2 : Law1592.Subspectral Law1685 := (show Law1592.Subspectral Law2 from (ImplicationTransfer.singleton_1592 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1593_2 : Law1593.Subspectral Law1685 := (show Law1593.Subspectral Law2 from (ImplicationTransfer.singleton_1593 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1595_2 : Law1595.Subspectral Law1685 := (show Law1595.Subspectral Law2 from (ImplicationTransfer.singleton_1595 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1596_2 : Law1596.Subspectral Law1685 := (show Law1596.Subspectral Law2 from (ImplicationTransfer.singleton_1596 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1597_2 : Law1597.Subspectral Law1685 := (show Law1597.Subspectral Law2 from (ImplicationTransfer.singleton_1597 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1599_2 : Law1599.Subspectral Law1685 := (show Law1599.Subspectral Law2 from (ImplicationTransfer.singleton_1599 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1600_2 : Law1600.Subspectral Law1685 := (show Law1600.Subspectral Law2 from (ImplicationTransfer.singleton_1600 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1601_2 : Law1601.Subspectral Law1685 := (show Law1601.Subspectral Law2 from (ImplicationTransfer.singleton_1601 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1602_2 : Law1602.Subspectral Law1685 := (show Law1602.Subspectral Law2 from (ImplicationTransfer.singleton_1602 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1604_2 : Law1604.Subspectral Law1685 := (show Law1604.Subspectral Law2 from (ImplicationTransfer.singleton_1604 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1605_2 : Law1605.Subspectral Law1685 := (show Law1605.Subspectral Law2 from (ImplicationTransfer.singleton_1605 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1606_2 : Law1606.Subspectral Law1685 := (show Law1606.Subspectral Law2 from (ImplicationTransfer.singleton_1606 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1607_2 : Law1607.Subspectral Law1685 := (show Law1607.Subspectral Law2 from (ImplicationTransfer.singleton_1607 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1609_2 : Law1609.Subspectral Law1685 := (show Law1609.Subspectral Law2 from (ImplicationTransfer.singleton_1609 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1610_2 : Law1610.Subspectral Law1685 := (show Law1610.Subspectral Law2 from (ImplicationTransfer.singleton_1610 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1611_2 : Law1611.Subspectral Law1685 := (show Law1611.Subspectral Law2 from (ImplicationTransfer.singleton_1611 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1612_2 : Law1612.Subspectral Law1685 := (show Law1612.Subspectral Law2 from (ImplicationTransfer.singleton_1612 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1614_2 : Law1614.Subspectral Law1685 := (show Law1614.Subspectral Law2 from (ImplicationTransfer.singleton_1614 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1615_2 : Law1615.Subspectral Law1685 := (show Law1615.Subspectral Law2 from (ImplicationTransfer.singleton_1615 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1616_2 : Law1616.Subspectral Law1685 := (show Law1616.Subspectral Law2 from (ImplicationTransfer.singleton_1616 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1617_2 : Law1617.Subspectral Law1685 := (show Law1617.Subspectral Law2 from (ImplicationTransfer.singleton_1617 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1619_2 : Law1619.Subspectral Law1685 := (show Law1619.Subspectral Law2 from (ImplicationTransfer.singleton_1619 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1620_2 : Law1620.Subspectral Law1685 := (show Law1620.Subspectral Law2 from (ImplicationTransfer.singleton_1620 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1621_2 : Law1621.Subspectral Law1685 := (show Law1621.Subspectral Law2 from (ImplicationTransfer.singleton_1621 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1622_2 : Law1622.Subspectral Law1685 := (show Law1622.Subspectral Law2 from (ImplicationTransfer.singleton_1622 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1624_2 : Law1624.Subspectral Law1685 := (show Law1624.Subspectral Law2 from (ImplicationTransfer.singleton_1624 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1625_2 : Law1625.Subspectral Law1685 := (show Law1625.Subspectral Law2 from (ImplicationTransfer.singleton_1625 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1626_2 : Law1626.Subspectral Law1685 := (show Law1626.Subspectral Law2 from (ImplicationTransfer.singleton_1626 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1627_2 : Law1627.Subspectral Law1685 := (show Law1627.Subspectral Law2 from (ImplicationTransfer.singleton_1627 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1628_2 : Law1628.Subspectral Law1685 := (show Law1628.Subspectral Law2 from (ImplicationTransfer.singleton_1628 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1683_2 : Law1683.Subspectral Law1685 := (show Law1683.Subspectral Law2 from (ImplicationTransfer.singleton_1683 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1685_2 : Law1685.Subspectral Law1685 := basis_route_1685_2

theorem route_1686_2 : Law1686.Subspectral Law1685 := (show Law1686.Subspectral Law2 from (ImplicationTransfer.singleton_1686 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1688_2 : Law1688.Subspectral Law1685 := (show Law1688.Subspectral Law2 from (ImplicationTransfer.singleton_1688 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1689_2 : Law1689.Subspectral Law1685 := (show Law1689.Subspectral Law2 from (ImplicationTransfer.singleton_1689 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1690_2 : Law1690.Subspectral Law1685 := (show Law1690.Subspectral Law2 from (ImplicationTransfer.singleton_1690 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1692_2 : Law1692.Subspectral Law1685 := basis_route_1692_2

theorem route_1693_2 : Law1693.Subspectral Law1685 := (show Law1693.Subspectral Law2 from (ImplicationTransfer.singleton_1693 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1696_2 : Law1696.Subspectral Law1685 := (show Law1696.Subspectral Law2 from (ImplicationTransfer.singleton_1696 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1698_2 : Law1698.Subspectral Law1685 := (show Law1698.Subspectral Law2 from (ImplicationTransfer.singleton_1698 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1700_2 : Law1700.Subspectral Law1685 := (show Law1700.Subspectral Law2 from (ImplicationTransfer.singleton_1700 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1702_2 : Law1702.Subspectral Law1685 := (show Law1702.Subspectral Law2 from (ImplicationTransfer.singleton_1702 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1703_2 : Law1703.Subspectral Law1685 := (show Law1703.Subspectral Law2 from (ImplicationTransfer.singleton_1703 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1704_2 : Law1704.Subspectral Law1685 := (show Law1704.Subspectral Law2 from (ImplicationTransfer.singleton_1704 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1706_2 : Law1706.Subspectral Law1685 := (show Law1706.Subspectral Law2 from (ImplicationTransfer.singleton_1706 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1708_2 : Law1708.Subspectral Law1685 := (show Law1708.Subspectral Law2 from (ImplicationTransfer.singleton_1708 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1710_3 : Law1710.Subspectral Law667 := (show Law1710.Subspectral Law695 from (ImplicationTransfer.spectrum_1710_eq_695).subset).trans basis_route_695_3

theorem route_1711_2 : Law1711.Subspectral Law1685 := (show Law1711.Subspectral Law2 from (ImplicationTransfer.singleton_1711 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1712_2 : Law1712.Subspectral Law1685 := (show Law1712.Subspectral Law2 from (ImplicationTransfer.singleton_1712 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1714_2 : Law1714.Subspectral Law1685 := (show Law1714.Subspectral Law2 from (ImplicationTransfer.singleton_1714 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1715_2 : Law1715.Subspectral Law1685 := (show Law1715.Subspectral Law2 from (ImplicationTransfer.singleton_1715 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1716_2 : Law1716.Subspectral Law1685 := (show Law1716.Subspectral Law2 from (ImplicationTransfer.singleton_1716 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1717_2 : Law1717.Subspectral Law1685 := (show Law1717.Subspectral Law2 from (ImplicationTransfer.singleton_1717 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1719_2 : Law1719.Subspectral Law1719 := basis_route_1719_2

theorem route_1720_2 : Law1720.Subspectral Law1685 := (show Law1720.Subspectral Law2 from (ImplicationTransfer.singleton_1720 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1723_2 : Law1723.Subspectral Law1685 := (show Law1723.Subspectral Law2 from (ImplicationTransfer.singleton_1723 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1725_2 : Law1725.Subspectral Law1685 := (show Law1725.Subspectral Law2 from (ImplicationTransfer.singleton_1725 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1727_2 : Law1727.Subspectral Law1685 := (show Law1727.Subspectral Law2 from (ImplicationTransfer.singleton_1727 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1730_2 : Law1730.Subspectral Law1685 := (show Law1730.Subspectral Law2 from (ImplicationTransfer.singleton_1730 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1732_2 : Law1732.Subspectral Law1685 := (show Law1732.Subspectral Law2 from (ImplicationTransfer.singleton_1732 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1733_2 : Law1733.Subspectral Law1685 := (show Law1733.Subspectral Law2 from (ImplicationTransfer.singleton_1733 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1735_2 : Law1735.Subspectral Law1685 := (show Law1735.Subspectral Law2 from (ImplicationTransfer.singleton_1735 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1736_2 : Law1736.Subspectral Law1685 := (show Law1736.Subspectral Law2 from (ImplicationTransfer.singleton_1736 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1737_2 : Law1737.Subspectral Law1685 := (show Law1737.Subspectral Law2 from (ImplicationTransfer.singleton_1737 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1739_2 : Law1739.Subspectral Law1685 := (show Law1739.Subspectral Law2 from (ImplicationTransfer.singleton_1739 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1741_2 : Law1741.Subspectral Law1685 := (show Law1741.Subspectral Law2 from (ImplicationTransfer.singleton_1741 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1743_2 : Law1743.Subspectral Law1685 := (show Law1743.Subspectral Law2 from (ImplicationTransfer.singleton_1743 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1744_2 : Law1744.Subspectral Law1685 := (show Law1744.Subspectral Law2 from (ImplicationTransfer.singleton_1744 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1745_2 : Law1745.Subspectral Law1685 := (show Law1745.Subspectral Law2 from (ImplicationTransfer.singleton_1745 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1747_2 : Law1747.Subspectral Law1685 := (show Law1747.Subspectral Law2 from (ImplicationTransfer.singleton_1747 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1748_2 : Law1748.Subspectral Law1685 := (show Law1748.Subspectral Law2 from (ImplicationTransfer.singleton_1748 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1749_2 : Law1749.Subspectral Law1685 := (show Law1749.Subspectral Law2 from (ImplicationTransfer.singleton_1749 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1751_2 : Law1751.Subspectral Law1685 := (show Law1751.Subspectral Law2 from (ImplicationTransfer.singleton_1751 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1752_2 : Law1752.Subspectral Law1685 := (show Law1752.Subspectral Law2 from (ImplicationTransfer.singleton_1752 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1753_2 : Law1753.Subspectral Law1685 := (show Law1753.Subspectral Law2 from (ImplicationTransfer.singleton_1753 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1754_2 : Law1754.Subspectral Law1685 := (show Law1754.Subspectral Law2 from (ImplicationTransfer.singleton_1754 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1756_2 : Law1756.Subspectral Law1685 := (show Law1756.Subspectral Law2 from (ImplicationTransfer.singleton_1756 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1757_2 : Law1757.Subspectral Law1685 := (show Law1757.Subspectral Law2 from (ImplicationTransfer.singleton_1757 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1758_2 : Law1758.Subspectral Law1685 := (show Law1758.Subspectral Law2 from (ImplicationTransfer.singleton_1758 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1760_2 : Law1760.Subspectral Law1685 := (show Law1760.Subspectral Law2 from (ImplicationTransfer.singleton_1760 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1762_2 : Law1762.Subspectral Law1685 := (show Law1762.Subspectral Law2 from (ImplicationTransfer.singleton_1762 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1764_3 : Law1764.Subspectral Law667 := (show Law1764.Subspectral Law546 from (ImplicationTransfer.spectrum_1764_eq_546).subset).trans basis_route_546_3

theorem route_1765_2 : Law1765.Subspectral Law1685 := (show Law1765.Subspectral Law2 from (ImplicationTransfer.singleton_1765 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1766_2 : Law1766.Subspectral Law1685 := (show Law1766.Subspectral Law2 from (ImplicationTransfer.singleton_1766 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1768_2 : Law1768.Subspectral Law1685 := (show Law1768.Subspectral Law2 from (ImplicationTransfer.singleton_1768 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1769_2 : Law1769.Subspectral Law1685 := (show Law1769.Subspectral Law2 from (ImplicationTransfer.singleton_1769 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1770_2 : Law1770.Subspectral Law1685 := (show Law1770.Subspectral Law2 from (ImplicationTransfer.singleton_1770 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1771_2 : Law1771.Subspectral Law1685 := (show Law1771.Subspectral Law2 from (ImplicationTransfer.singleton_1771 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1773_2 : Law1773.Subspectral Law1685 := (show Law1773.Subspectral Law2 from (ImplicationTransfer.singleton_1773 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1775_2 : Law1775.Subspectral Law1685 := (show Law1775.Subspectral Law2 from (ImplicationTransfer.singleton_1775 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1777_2 : Law1777.Subspectral Law1685 := (show Law1777.Subspectral Law2 from (ImplicationTransfer.singleton_1777 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1778_2 : Law1778.Subspectral Law1685 := (show Law1778.Subspectral Law2 from (ImplicationTransfer.singleton_1778 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1779_2 : Law1779.Subspectral Law1685 := (show Law1779.Subspectral Law2 from (ImplicationTransfer.singleton_1779 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1781_2 : Law1781.Subspectral Law1685 := (show Law1781.Subspectral Law2 from (ImplicationTransfer.singleton_1781 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1782_2 : Law1782.Subspectral Law1685 := (show Law1782.Subspectral Law2 from (ImplicationTransfer.singleton_1782 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1783_2 : Law1783.Subspectral Law1685 := (show Law1783.Subspectral Law2 from (ImplicationTransfer.singleton_1783 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1785_2 : Law1785.Subspectral Law1685 := (show Law1785.Subspectral Law2 from (ImplicationTransfer.singleton_1785 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1786_2 : Law1786.Subspectral Law1685 := (show Law1786.Subspectral Law2 from (ImplicationTransfer.singleton_1786 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1787_2 : Law1787.Subspectral Law1685 := (show Law1787.Subspectral Law2 from (ImplicationTransfer.singleton_1787 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1788_2 : Law1788.Subspectral Law1685 := (show Law1788.Subspectral Law2 from (ImplicationTransfer.singleton_1788 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1790_3 : Law1790.Subspectral Law667 := (show Law1790.Subspectral Law546 from (ImplicationTransfer.spectrum_1790_eq_546).subset).trans basis_route_546_3

theorem route_1791_2 : Law1791.Subspectral Law1685 := (show Law1791.Subspectral Law2 from (ImplicationTransfer.singleton_1791 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1792_2 : Law1792.Subspectral Law1685 := (show Law1792.Subspectral Law2 from (ImplicationTransfer.singleton_1792 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1794_2 : Law1794.Subspectral Law1685 := (show Law1794.Subspectral Law2 from (ImplicationTransfer.singleton_1794 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1795_2 : Law1795.Subspectral Law1685 := (show Law1795.Subspectral Law2 from (ImplicationTransfer.singleton_1795 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1796_2 : Law1796.Subspectral Law1685 := (show Law1796.Subspectral Law2 from (ImplicationTransfer.singleton_1796 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1798_2 : Law1798.Subspectral Law1685 := (show Law1798.Subspectral Law2 from (ImplicationTransfer.singleton_1798 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1799_2 : Law1799.Subspectral Law1685 := (show Law1799.Subspectral Law2 from (ImplicationTransfer.singleton_1799 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1800_2 : Law1800.Subspectral Law1685 := (show Law1800.Subspectral Law2 from (ImplicationTransfer.singleton_1800 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1802_2 : Law1802.Subspectral Law1685 := (show Law1802.Subspectral Law2 from (ImplicationTransfer.singleton_1802 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1803_2 : Law1803.Subspectral Law1685 := (show Law1803.Subspectral Law2 from (ImplicationTransfer.singleton_1803 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1804_2 : Law1804.Subspectral Law1685 := (show Law1804.Subspectral Law2 from (ImplicationTransfer.singleton_1804 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1805_2 : Law1805.Subspectral Law1685 := (show Law1805.Subspectral Law2 from (ImplicationTransfer.singleton_1805 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1807_2 : Law1807.Subspectral Law1685 := (show Law1807.Subspectral Law2 from (ImplicationTransfer.singleton_1807 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1808_2 : Law1808.Subspectral Law1685 := (show Law1808.Subspectral Law2 from (ImplicationTransfer.singleton_1808 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1809_2 : Law1809.Subspectral Law1685 := (show Law1809.Subspectral Law2 from (ImplicationTransfer.singleton_1809 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1810_2 : Law1810.Subspectral Law1685 := (show Law1810.Subspectral Law2 from (ImplicationTransfer.singleton_1810 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1812_2 : Law1812.Subspectral Law1685 := (show Law1812.Subspectral Law2 from (ImplicationTransfer.singleton_1812 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1813_2 : Law1813.Subspectral Law1685 := (show Law1813.Subspectral Law2 from (ImplicationTransfer.singleton_1813 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1814_2 : Law1814.Subspectral Law1685 := (show Law1814.Subspectral Law2 from (ImplicationTransfer.singleton_1814 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1815_2 : Law1815.Subspectral Law1685 := (show Law1815.Subspectral Law2 from (ImplicationTransfer.singleton_1815 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1817_2 : Law1817.Subspectral Law1685 := (show Law1817.Subspectral Law2 from (ImplicationTransfer.singleton_1817 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1818_2 : Law1818.Subspectral Law1685 := (show Law1818.Subspectral Law2 from (ImplicationTransfer.singleton_1818 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1819_2 : Law1819.Subspectral Law1685 := (show Law1819.Subspectral Law2 from (ImplicationTransfer.singleton_1819 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1820_2 : Law1820.Subspectral Law1685 := (show Law1820.Subspectral Law2 from (ImplicationTransfer.singleton_1820 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1822_2 : Law1822.Subspectral Law1685 := (show Law1822.Subspectral Law2 from (ImplicationTransfer.singleton_1822 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1823_2 : Law1823.Subspectral Law1685 := (show Law1823.Subspectral Law2 from (ImplicationTransfer.singleton_1823 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1824_2 : Law1824.Subspectral Law1685 := (show Law1824.Subspectral Law2 from (ImplicationTransfer.singleton_1824 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1825_2 : Law1825.Subspectral Law1685 := (show Law1825.Subspectral Law2 from (ImplicationTransfer.singleton_1825 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1827_2 : Law1827.Subspectral Law1685 := (show Law1827.Subspectral Law2 from (ImplicationTransfer.singleton_1827 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1828_2 : Law1828.Subspectral Law1685 := (show Law1828.Subspectral Law2 from (ImplicationTransfer.singleton_1828 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1829_2 : Law1829.Subspectral Law1685 := (show Law1829.Subspectral Law2 from (ImplicationTransfer.singleton_1829 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1830_2 : Law1830.Subspectral Law1685 := (show Law1830.Subspectral Law2 from (ImplicationTransfer.singleton_1830 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1831_2 : Law1831.Subspectral Law1685 := (show Law1831.Subspectral Law2 from (ImplicationTransfer.singleton_1831 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1886_2 : Law1886.Subspectral Law1685 := (show Law1886.Subspectral Law2 from (ImplicationTransfer.singleton_1886 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1888_2 : Law1888.Subspectral Law1719 := (show Law1888.Subspectral Law1719 from (ImplicationTransfer.spectrum_1888_eq_1719).subset).trans basis_route_1719_2

theorem route_1889_2 : Law1889.Subspectral Law1685 := (show Law1889.Subspectral Law2 from (ImplicationTransfer.singleton_1889 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1891_2 : Law1891.Subspectral Law1685 := (show Law1891.Subspectral Law2 from (ImplicationTransfer.singleton_1891 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1892_2 : Law1892.Subspectral Law1685 := (show Law1892.Subspectral Law2 from (ImplicationTransfer.singleton_1892 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1893_2 : Law1893.Subspectral Law1685 := (show Law1893.Subspectral Law2 from (ImplicationTransfer.singleton_1893 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1895_2 : Law1895.Subspectral Law1685 := (show Law1895.Subspectral Law1692 from (ImplicationTransfer.spectrum_1895_eq_1692).subset).trans basis_route_1692_2

theorem route_1896_2 : Law1896.Subspectral Law1685 := (show Law1896.Subspectral Law2 from (ImplicationTransfer.singleton_1896 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1899_2 : Law1899.Subspectral Law1685 := (show Law1899.Subspectral Law2 from (ImplicationTransfer.singleton_1899 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1901_2 : Law1901.Subspectral Law1685 := (show Law1901.Subspectral Law2 from (ImplicationTransfer.singleton_1901 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1903_2 : Law1903.Subspectral Law1685 := (show Law1903.Subspectral Law2 from (ImplicationTransfer.singleton_1903 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1905_2 : Law1905.Subspectral Law1685 := (show Law1905.Subspectral Law2 from (ImplicationTransfer.singleton_1905 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1906_2 : Law1906.Subspectral Law1685 := (show Law1906.Subspectral Law2 from (ImplicationTransfer.singleton_1906 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1907_2 : Law1907.Subspectral Law1685 := (show Law1907.Subspectral Law2 from (ImplicationTransfer.singleton_1907 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1909_2 : Law1909.Subspectral Law1685 := (show Law1909.Subspectral Law2 from (ImplicationTransfer.singleton_1909 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1911_2 : Law1911.Subspectral Law1685 := (show Law1911.Subspectral Law2 from (ImplicationTransfer.singleton_1911 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1913_3 : Law1913.Subspectral Law667 := (show Law1913.Subspectral Law546 from (ImplicationTransfer.spectrum_1913_eq_546).subset).trans basis_route_546_3

theorem route_1914_2 : Law1914.Subspectral Law1685 := (show Law1914.Subspectral Law2 from (ImplicationTransfer.singleton_1914 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1915_2 : Law1915.Subspectral Law1685 := (show Law1915.Subspectral Law2 from (ImplicationTransfer.singleton_1915 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1917_2 : Law1917.Subspectral Law1685 := (show Law1917.Subspectral Law2 from (ImplicationTransfer.singleton_1917 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1918_2 : Law1918.Subspectral Law1685 := (show Law1918.Subspectral Law2 from (ImplicationTransfer.singleton_1918 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1919_2 : Law1919.Subspectral Law1685 := (show Law1919.Subspectral Law2 from (ImplicationTransfer.singleton_1919 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1920_2 : Law1920.Subspectral Law1685 := (show Law1920.Subspectral Law2 from (ImplicationTransfer.singleton_1920 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1922_2 : Law1922.Subspectral Law1685 := (show Law1922.Subspectral Law1685 from (ImplicationTransfer.spectrum_1922_eq_1685).subset).trans basis_route_1685_2

theorem route_1923_2 : Law1923.Subspectral Law1685 := (show Law1923.Subspectral Law2 from (ImplicationTransfer.singleton_1923 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1926_2 : Law1926.Subspectral Law1685 := (show Law1926.Subspectral Law2 from (ImplicationTransfer.singleton_1926 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1928_2 : Law1928.Subspectral Law1685 := (show Law1928.Subspectral Law2 from (ImplicationTransfer.singleton_1928 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1930_2 : Law1930.Subspectral Law1685 := (show Law1930.Subspectral Law2 from (ImplicationTransfer.singleton_1930 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1933_2 : Law1933.Subspectral Law1685 := (show Law1933.Subspectral Law2 from (ImplicationTransfer.singleton_1933 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1935_2 : Law1935.Subspectral Law1685 := (show Law1935.Subspectral Law2 from (ImplicationTransfer.singleton_1935 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1936_2 : Law1936.Subspectral Law1685 := (show Law1936.Subspectral Law2 from (ImplicationTransfer.singleton_1936 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1938_2 : Law1938.Subspectral Law1685 := (show Law1938.Subspectral Law2 from (ImplicationTransfer.singleton_1938 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1939_2 : Law1939.Subspectral Law1685 := (show Law1939.Subspectral Law2 from (ImplicationTransfer.singleton_1939 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1940_2 : Law1940.Subspectral Law1685 := (show Law1940.Subspectral Law2 from (ImplicationTransfer.singleton_1940 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1942_2 : Law1942.Subspectral Law1685 := (show Law1942.Subspectral Law2 from (ImplicationTransfer.singleton_1942 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1944_2 : Law1944.Subspectral Law1685 := (show Law1944.Subspectral Law2 from (ImplicationTransfer.singleton_1944 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1946_2 : Law1946.Subspectral Law1685 := (show Law1946.Subspectral Law2 from (ImplicationTransfer.singleton_1946 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1947_2 : Law1947.Subspectral Law1685 := (show Law1947.Subspectral Law2 from (ImplicationTransfer.singleton_1947 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1948_2 : Law1948.Subspectral Law1685 := (show Law1948.Subspectral Law2 from (ImplicationTransfer.singleton_1948 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1950_2 : Law1950.Subspectral Law1685 := (show Law1950.Subspectral Law2 from (ImplicationTransfer.singleton_1950 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1951_2 : Law1951.Subspectral Law1685 := (show Law1951.Subspectral Law2 from (ImplicationTransfer.singleton_1951 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1952_2 : Law1952.Subspectral Law1685 := (show Law1952.Subspectral Law2 from (ImplicationTransfer.singleton_1952 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1954_2 : Law1954.Subspectral Law1685 := (show Law1954.Subspectral Law2 from (ImplicationTransfer.singleton_1954 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1955_2 : Law1955.Subspectral Law1685 := (show Law1955.Subspectral Law2 from (ImplicationTransfer.singleton_1955 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1956_2 : Law1956.Subspectral Law1685 := (show Law1956.Subspectral Law2 from (ImplicationTransfer.singleton_1956 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1957_2 : Law1957.Subspectral Law1685 := (show Law1957.Subspectral Law2 from (ImplicationTransfer.singleton_1957 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1959_2 : Law1959.Subspectral Law1685 := (show Law1959.Subspectral Law2 from (ImplicationTransfer.singleton_1959 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1960_2 : Law1960.Subspectral Law1685 := (show Law1960.Subspectral Law2 from (ImplicationTransfer.singleton_1960 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1961_2 : Law1961.Subspectral Law1685 := (show Law1961.Subspectral Law2 from (ImplicationTransfer.singleton_1961 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1963_2 : Law1963.Subspectral Law1685 := (show Law1963.Subspectral Law2 from (ImplicationTransfer.singleton_1963 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1965_2 : Law1965.Subspectral Law1685 := (show Law1965.Subspectral Law2 from (ImplicationTransfer.singleton_1965 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1967_3 : Law1967.Subspectral Law667 := (show Law1967.Subspectral Law546 from (ImplicationTransfer.spectrum_1967_eq_546).subset).trans basis_route_546_3

theorem route_1968_2 : Law1968.Subspectral Law1685 := (show Law1968.Subspectral Law2 from (ImplicationTransfer.singleton_1968 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1969_2 : Law1969.Subspectral Law1685 := (show Law1969.Subspectral Law2 from (ImplicationTransfer.singleton_1969 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1971_2 : Law1971.Subspectral Law1685 := (show Law1971.Subspectral Law2 from (ImplicationTransfer.singleton_1971 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1972_2 : Law1972.Subspectral Law1685 := (show Law1972.Subspectral Law2 from (ImplicationTransfer.singleton_1972 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1973_2 : Law1973.Subspectral Law1685 := (show Law1973.Subspectral Law2 from (ImplicationTransfer.singleton_1973 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1974_2 : Law1974.Subspectral Law1685 := (show Law1974.Subspectral Law2 from (ImplicationTransfer.singleton_1974 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1976_2 : Law1976.Subspectral Law1685 := (show Law1976.Subspectral Law2 from (ImplicationTransfer.singleton_1976 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1978_2 : Law1978.Subspectral Law1685 := (show Law1978.Subspectral Law2 from (ImplicationTransfer.singleton_1978 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1980_2 : Law1980.Subspectral Law1685 := (show Law1980.Subspectral Law2 from (ImplicationTransfer.singleton_1980 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1981_2 : Law1981.Subspectral Law1685 := (show Law1981.Subspectral Law2 from (ImplicationTransfer.singleton_1981 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1982_2 : Law1982.Subspectral Law1685 := (show Law1982.Subspectral Law2 from (ImplicationTransfer.singleton_1982 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1984_2 : Law1984.Subspectral Law1685 := (show Law1984.Subspectral Law2 from (ImplicationTransfer.singleton_1984 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1985_2 : Law1985.Subspectral Law1685 := (show Law1985.Subspectral Law2 from (ImplicationTransfer.singleton_1985 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1986_2 : Law1986.Subspectral Law1685 := (show Law1986.Subspectral Law2 from (ImplicationTransfer.singleton_1986 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1988_2 : Law1988.Subspectral Law1685 := (show Law1988.Subspectral Law2 from (ImplicationTransfer.singleton_1988 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1989_2 : Law1989.Subspectral Law1685 := (show Law1989.Subspectral Law2 from (ImplicationTransfer.singleton_1989 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1990_2 : Law1990.Subspectral Law1685 := (show Law1990.Subspectral Law2 from (ImplicationTransfer.singleton_1990 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1991_2 : Law1991.Subspectral Law1685 := (show Law1991.Subspectral Law2 from (ImplicationTransfer.singleton_1991 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1993_3 : Law1993.Subspectral Law667 := (show Law1993.Subspectral Law695 from (ImplicationTransfer.spectrum_1993_eq_695).subset).trans basis_route_695_3

theorem route_1994_2 : Law1994.Subspectral Law1685 := (show Law1994.Subspectral Law2 from (ImplicationTransfer.singleton_1994 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1995_2 : Law1995.Subspectral Law1685 := (show Law1995.Subspectral Law2 from (ImplicationTransfer.singleton_1995 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1997_2 : Law1997.Subspectral Law1685 := (show Law1997.Subspectral Law2 from (ImplicationTransfer.singleton_1997 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1998_2 : Law1998.Subspectral Law1685 := (show Law1998.Subspectral Law2 from (ImplicationTransfer.singleton_1998 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_1999_2 : Law1999.Subspectral Law1685 := (show Law1999.Subspectral Law2 from (ImplicationTransfer.singleton_1999 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2001_2 : Law2001.Subspectral Law1685 := (show Law2001.Subspectral Law2 from (ImplicationTransfer.singleton_2001 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2002_2 : Law2002.Subspectral Law1685 := (show Law2002.Subspectral Law2 from (ImplicationTransfer.singleton_2002 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2003_2 : Law2003.Subspectral Law1685 := (show Law2003.Subspectral Law2 from (ImplicationTransfer.singleton_2003 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2005_2 : Law2005.Subspectral Law1685 := (show Law2005.Subspectral Law2 from (ImplicationTransfer.singleton_2005 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2006_2 : Law2006.Subspectral Law1685 := (show Law2006.Subspectral Law2 from (ImplicationTransfer.singleton_2006 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2007_2 : Law2007.Subspectral Law1685 := (show Law2007.Subspectral Law2 from (ImplicationTransfer.singleton_2007 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2008_2 : Law2008.Subspectral Law1685 := (show Law2008.Subspectral Law2 from (ImplicationTransfer.singleton_2008 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2010_2 : Law2010.Subspectral Law1685 := (show Law2010.Subspectral Law2 from (ImplicationTransfer.singleton_2010 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2011_2 : Law2011.Subspectral Law1685 := (show Law2011.Subspectral Law2 from (ImplicationTransfer.singleton_2011 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2012_2 : Law2012.Subspectral Law1685 := (show Law2012.Subspectral Law2 from (ImplicationTransfer.singleton_2012 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2013_2 : Law2013.Subspectral Law1685 := (show Law2013.Subspectral Law2 from (ImplicationTransfer.singleton_2013 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2015_2 : Law2015.Subspectral Law1685 := (show Law2015.Subspectral Law2 from (ImplicationTransfer.singleton_2015 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2016_2 : Law2016.Subspectral Law1685 := (show Law2016.Subspectral Law2 from (ImplicationTransfer.singleton_2016 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2017_2 : Law2017.Subspectral Law1685 := (show Law2017.Subspectral Law2 from (ImplicationTransfer.singleton_2017 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2018_2 : Law2018.Subspectral Law1685 := (show Law2018.Subspectral Law2 from (ImplicationTransfer.singleton_2018 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2020_2 : Law2020.Subspectral Law1685 := (show Law2020.Subspectral Law2 from (ImplicationTransfer.singleton_2020 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2021_2 : Law2021.Subspectral Law1685 := (show Law2021.Subspectral Law2 from (ImplicationTransfer.singleton_2021 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2022_2 : Law2022.Subspectral Law1685 := (show Law2022.Subspectral Law2 from (ImplicationTransfer.singleton_2022 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2023_2 : Law2023.Subspectral Law1685 := (show Law2023.Subspectral Law2 from (ImplicationTransfer.singleton_2023 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2025_2 : Law2025.Subspectral Law1685 := (show Law2025.Subspectral Law2 from (ImplicationTransfer.singleton_2025 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2026_2 : Law2026.Subspectral Law1685 := (show Law2026.Subspectral Law2 from (ImplicationTransfer.singleton_2026 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2027_2 : Law2027.Subspectral Law1685 := (show Law2027.Subspectral Law2 from (ImplicationTransfer.singleton_2027 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2028_2 : Law2028.Subspectral Law1685 := (show Law2028.Subspectral Law2 from (ImplicationTransfer.singleton_2028 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2030_2 : Law2030.Subspectral Law1685 := (show Law2030.Subspectral Law2 from (ImplicationTransfer.singleton_2030 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2031_2 : Law2031.Subspectral Law1685 := (show Law2031.Subspectral Law2 from (ImplicationTransfer.singleton_2031 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2032_2 : Law2032.Subspectral Law1685 := (show Law2032.Subspectral Law2 from (ImplicationTransfer.singleton_2032 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2033_2 : Law2033.Subspectral Law1685 := (show Law2033.Subspectral Law2 from (ImplicationTransfer.singleton_2033 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2034_2 : Law2034.Subspectral Law1685 := (show Law2034.Subspectral Law2 from (ImplicationTransfer.singleton_2034 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2089_2 : Law2089.Subspectral Law1480 := (show Law2089.Subspectral Law1480 from (ImplicationTransfer.spectrum_2089_eq_1480).subset).trans basis_route_1480_2

theorem route_2091_2 : Law2091.Subspectral Law1516 := (show Law2091.Subspectral Law1516 from (ImplicationTransfer.spectrum_2091_eq_1516).subset).trans basis_route_1516_2

theorem route_2092_2 : Law2092.Subspectral Law1685 := (show Law2092.Subspectral Law2 from (ImplicationTransfer.singleton_2092 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2094_2 : Law2094.Subspectral Law1685 := (show Law2094.Subspectral Law2 from (ImplicationTransfer.singleton_2094 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2095_2 : Law2095.Subspectral Law1685 := (show Law2095.Subspectral Law2 from (ImplicationTransfer.singleton_2095 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2096_2 : Law2096.Subspectral Law1685 := (show Law2096.Subspectral Law2 from (ImplicationTransfer.singleton_2096 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2098_2 : Law2098.Subspectral Law1489 := (show Law2098.Subspectral Law1489 from (ImplicationTransfer.spectrum_2098_eq_1489).subset).trans basis_route_1489_2

theorem route_2099_2 : Law2099.Subspectral Law1685 := (show Law2099.Subspectral Law2 from (ImplicationTransfer.singleton_2099 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2101_3 : Law2101.Subspectral Law883 := (show Law2101.Subspectral Law1526 from (ImplicationTransfer.spectrum_2101_eq_1526).subset).trans basis_route_1526_3

theorem route_2102_2 : Law2102.Subspectral Law1685 := (show Law2102.Subspectral Law2 from (ImplicationTransfer.singleton_2102 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2104_2 : Law2104.Subspectral Law1685 := (show Law2104.Subspectral Law2 from (ImplicationTransfer.singleton_2104 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2105_3 : Law2105.Subspectral Law667 := (show Law2105.Subspectral Law887 from (ImplicationTransfer.spectrum_2105_eq_887).subset).trans basis_route_887_3

theorem route_2106_2 : Law2106.Subspectral Law1685 := (show Law2106.Subspectral Law2 from (ImplicationTransfer.singleton_2106 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2108_2 : Law2108.Subspectral Law1685 := (show Law2108.Subspectral Law2 from (ImplicationTransfer.singleton_2108 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2109_2 : Law2109.Subspectral Law1685 := (show Law2109.Subspectral Law2 from (ImplicationTransfer.singleton_2109 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2110_2 : Law2110.Subspectral Law1685 := (show Law2110.Subspectral Law2 from (ImplicationTransfer.singleton_2110 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2112_2 : Law2112.Subspectral Law1685 := (show Law2112.Subspectral Law2 from (ImplicationTransfer.singleton_2112 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2113_3 : Law2113.Subspectral Law667 := (show Law2113.Subspectral Law895 from (ImplicationTransfer.spectrum_2113_eq_895).subset).trans basis_route_895_3

theorem route_2114_2 : Law2114.Subspectral Law1685 := (show Law2114.Subspectral Law2 from (ImplicationTransfer.singleton_2114 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2116_3 : Law2116.Subspectral Law667 := (show Law2116.Subspectral Law898 from (ImplicationTransfer.spectrum_2116_eq_898).subset).trans basis_route_898_3

theorem route_2117_2 : Law2117.Subspectral Law1685 := (show Law2117.Subspectral Law2 from (ImplicationTransfer.singleton_2117 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2118_2 : Law2118.Subspectral Law1685 := (show Law2118.Subspectral Law2 from (ImplicationTransfer.singleton_2118 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2120_2 : Law2120.Subspectral Law1685 := (show Law2120.Subspectral Law2 from (ImplicationTransfer.singleton_2120 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2121_2 : Law2121.Subspectral Law1685 := (show Law2121.Subspectral Law2 from (ImplicationTransfer.singleton_2121 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2122_2 : Law2122.Subspectral Law1685 := (show Law2122.Subspectral Law2 from (ImplicationTransfer.singleton_2122 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2123_2 : Law2123.Subspectral Law1685 := (show Law2123.Subspectral Law2 from (ImplicationTransfer.singleton_2123 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2126_2 : Law2126.Subspectral Law1486 := (show Law2126.Subspectral Law1486 from (ImplicationTransfer.spectrum_2126_eq_1486).subset).trans basis_route_1486_2

theorem route_2129_2 : Law2129.Subspectral Law1685 := (show Law2129.Subspectral Law2 from (ImplicationTransfer.singleton_2129 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2131_2 : Law2131.Subspectral Law1685 := (show Law2131.Subspectral Law2 from (ImplicationTransfer.singleton_2131 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2133_2 : Law2133.Subspectral Law1685 := (show Law2133.Subspectral Law2 from (ImplicationTransfer.singleton_2133 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2136_2 : Law2136.Subspectral Law1685 := (show Law2136.Subspectral Law2 from (ImplicationTransfer.singleton_2136 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2138_2 : Law2138.Subspectral Law1685 := (show Law2138.Subspectral Law2 from (ImplicationTransfer.singleton_2138 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2139_2 : Law2139.Subspectral Law1685 := (show Law2139.Subspectral Law2 from (ImplicationTransfer.singleton_2139 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2141_2 : Law2141.Subspectral Law1685 := (show Law2141.Subspectral Law2 from (ImplicationTransfer.singleton_2141 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2142_2 : Law2142.Subspectral Law1685 := (show Law2142.Subspectral Law2 from (ImplicationTransfer.singleton_2142 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2143_2 : Law2143.Subspectral Law1685 := (show Law2143.Subspectral Law2 from (ImplicationTransfer.singleton_2143 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2145_2 : Law2145.Subspectral Law1685 := (show Law2145.Subspectral Law2 from (ImplicationTransfer.singleton_2145 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2146_3 : Law2146.Subspectral Law481 := (show Law2146.Subspectral Law1496 from (ImplicationTransfer.spectrum_2146_eq_1496).subset).trans basis_route_1496_3

theorem route_2147_2 : Law2147.Subspectral Law1685 := (show Law2147.Subspectral Law2 from (ImplicationTransfer.singleton_2147 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2149_2 : Law2149.Subspectral Law1685 := (show Law2149.Subspectral Law2 from (ImplicationTransfer.singleton_2149 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2150_2 : Law2150.Subspectral Law1685 := (show Law2150.Subspectral Law2 from (ImplicationTransfer.singleton_2150 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2151_2 : Law2151.Subspectral Law1685 := (show Law2151.Subspectral Law2 from (ImplicationTransfer.singleton_2151 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2153_2 : Law2153.Subspectral Law1685 := (show Law2153.Subspectral Law2 from (ImplicationTransfer.singleton_2153 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2154_2 : Law2154.Subspectral Law1685 := (show Law2154.Subspectral Law2 from (ImplicationTransfer.singleton_2154 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2155_2 : Law2155.Subspectral Law1685 := (show Law2155.Subspectral Law2 from (ImplicationTransfer.singleton_2155 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2157_2 : Law2157.Subspectral Law1685 := (show Law2157.Subspectral Law2 from (ImplicationTransfer.singleton_2157 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2158_2 : Law2158.Subspectral Law1685 := (show Law2158.Subspectral Law2 from (ImplicationTransfer.singleton_2158 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2159_2 : Law2159.Subspectral Law1685 := (show Law2159.Subspectral Law2 from (ImplicationTransfer.singleton_2159 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2160_2 : Law2160.Subspectral Law1685 := (show Law2160.Subspectral Law2 from (ImplicationTransfer.singleton_2160 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2162_3 : Law2162.Subspectral Law1485 := (show Law2162.Subspectral Law1485 from (ImplicationTransfer.spectrum_2162_eq_1485).subset).trans basis_route_1485_3

theorem route_2163_3 : Law2163.Subspectral Law1483 := (show Law2163.Subspectral Law1483 from (ImplicationTransfer.spectrum_2163_eq_1483).subset).trans basis_route_1483_3

theorem route_2164_2 : Law2164.Subspectral Law167 := (show Law2164.Subspectral Law168 from (ImplicationTransfer.spectrum_2164_eq_168).subset).trans basis_route_168_2

theorem route_2166_2 : Law2166.Subspectral Law1685 := (show Law2166.Subspectral Law2 from (ImplicationTransfer.singleton_2166 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2168_2 : Law2168.Subspectral Law1685 := (show Law2168.Subspectral Law2 from (ImplicationTransfer.singleton_2168 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2171_2 : Law2171.Subspectral Law1685 := (show Law2171.Subspectral Law2 from (ImplicationTransfer.singleton_2171 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2172_2 : Law2172.Subspectral Law1685 := (show Law2172.Subspectral Law2 from (ImplicationTransfer.singleton_2172 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2174_2 : Law2174.Subspectral Law1685 := (show Law2174.Subspectral Law2 from (ImplicationTransfer.singleton_2174 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2175_2 : Law2175.Subspectral Law1685 := (show Law2175.Subspectral Law2 from (ImplicationTransfer.singleton_2175 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2176_2 : Law2176.Subspectral Law1685 := (show Law2176.Subspectral Law2 from (ImplicationTransfer.singleton_2176 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2177_2 : Law2177.Subspectral Law1685 := (show Law2177.Subspectral Law2 from (ImplicationTransfer.singleton_2177 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2179_2 : Law2179.Subspectral Law1685 := (show Law2179.Subspectral Law2 from (ImplicationTransfer.singleton_2179 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2181_2 : Law2181.Subspectral Law1685 := (show Law2181.Subspectral Law2 from (ImplicationTransfer.singleton_2181 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2183_2 : Law2183.Subspectral Law1685 := (show Law2183.Subspectral Law2 from (ImplicationTransfer.singleton_2183 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2184_2 : Law2184.Subspectral Law1685 := (show Law2184.Subspectral Law2 from (ImplicationTransfer.singleton_2184 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2185_2 : Law2185.Subspectral Law1685 := (show Law2185.Subspectral Law2 from (ImplicationTransfer.singleton_2185 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2187_2 : Law2187.Subspectral Law1685 := (show Law2187.Subspectral Law2 from (ImplicationTransfer.singleton_2187 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2188_2 : Law2188.Subspectral Law1685 := (show Law2188.Subspectral Law2 from (ImplicationTransfer.singleton_2188 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2189_2 : Law2189.Subspectral Law1685 := (show Law2189.Subspectral Law2 from (ImplicationTransfer.singleton_2189 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2191_2 : Law2191.Subspectral Law1685 := (show Law2191.Subspectral Law2 from (ImplicationTransfer.singleton_2191 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2192_2 : Law2192.Subspectral Law1685 := (show Law2192.Subspectral Law2 from (ImplicationTransfer.singleton_2192 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2193_2 : Law2193.Subspectral Law1685 := (show Law2193.Subspectral Law2 from (ImplicationTransfer.singleton_2193 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2194_2 : Law2194.Subspectral Law1685 := (show Law2194.Subspectral Law2 from (ImplicationTransfer.singleton_2194 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2197_2 : Law2197.Subspectral Law1685 := (show Law2197.Subspectral Law2 from (ImplicationTransfer.singleton_2197 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2198_2 : Law2198.Subspectral Law1685 := (show Law2198.Subspectral Law2 from (ImplicationTransfer.singleton_2198 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2200_2 : Law2200.Subspectral Law1685 := (show Law2200.Subspectral Law2 from (ImplicationTransfer.singleton_2200 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2201_2 : Law2201.Subspectral Law1685 := (show Law2201.Subspectral Law2 from (ImplicationTransfer.singleton_2201 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2202_2 : Law2202.Subspectral Law1685 := (show Law2202.Subspectral Law2 from (ImplicationTransfer.singleton_2202 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2204_2 : Law2204.Subspectral Law1685 := (show Law2204.Subspectral Law2 from (ImplicationTransfer.singleton_2204 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2205_2 : Law2205.Subspectral Law1685 := (show Law2205.Subspectral Law2 from (ImplicationTransfer.singleton_2205 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2206_2 : Law2206.Subspectral Law1685 := (show Law2206.Subspectral Law2 from (ImplicationTransfer.singleton_2206 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2208_2 : Law2208.Subspectral Law1685 := (show Law2208.Subspectral Law2 from (ImplicationTransfer.singleton_2208 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2209_2 : Law2209.Subspectral Law1685 := (show Law2209.Subspectral Law2 from (ImplicationTransfer.singleton_2209 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2210_2 : Law2210.Subspectral Law1685 := (show Law2210.Subspectral Law2 from (ImplicationTransfer.singleton_2210 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2211_2 : Law2211.Subspectral Law1685 := (show Law2211.Subspectral Law2 from (ImplicationTransfer.singleton_2211 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2213_2 : Law2213.Subspectral Law1685 := (show Law2213.Subspectral Law2 from (ImplicationTransfer.singleton_2213 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2214_2 : Law2214.Subspectral Law1685 := (show Law2214.Subspectral Law2 from (ImplicationTransfer.singleton_2214 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2215_2 : Law2215.Subspectral Law1685 := (show Law2215.Subspectral Law2 from (ImplicationTransfer.singleton_2215 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2216_2 : Law2216.Subspectral Law1685 := (show Law2216.Subspectral Law2 from (ImplicationTransfer.singleton_2216 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2218_2 : Law2218.Subspectral Law1685 := (show Law2218.Subspectral Law2 from (ImplicationTransfer.singleton_2218 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2219_2 : Law2219.Subspectral Law1685 := (show Law2219.Subspectral Law2 from (ImplicationTransfer.singleton_2219 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2220_2 : Law2220.Subspectral Law1685 := (show Law2220.Subspectral Law2 from (ImplicationTransfer.singleton_2220 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2221_2 : Law2221.Subspectral Law1685 := (show Law2221.Subspectral Law2 from (ImplicationTransfer.singleton_2221 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2223_2 : Law2223.Subspectral Law1685 := (show Law2223.Subspectral Law2 from (ImplicationTransfer.singleton_2223 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2224_2 : Law2224.Subspectral Law1685 := (show Law2224.Subspectral Law2 from (ImplicationTransfer.singleton_2224 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2225_2 : Law2225.Subspectral Law1685 := (show Law2225.Subspectral Law2 from (ImplicationTransfer.singleton_2225 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2226_2 : Law2226.Subspectral Law1685 := (show Law2226.Subspectral Law2 from (ImplicationTransfer.singleton_2226 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2228_2 : Law2228.Subspectral Law1685 := (show Law2228.Subspectral Law2 from (ImplicationTransfer.singleton_2228 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2229_2 : Law2229.Subspectral Law1685 := (show Law2229.Subspectral Law2 from (ImplicationTransfer.singleton_2229 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2230_2 : Law2230.Subspectral Law1685 := (show Law2230.Subspectral Law2 from (ImplicationTransfer.singleton_2230 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2231_2 : Law2231.Subspectral Law1685 := (show Law2231.Subspectral Law2 from (ImplicationTransfer.singleton_2231 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2233_2 : Law2233.Subspectral Law1685 := (show Law2233.Subspectral Law2 from (ImplicationTransfer.singleton_2233 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2234_2 : Law2234.Subspectral Law1685 := (show Law2234.Subspectral Law2 from (ImplicationTransfer.singleton_2234 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2235_2 : Law2235.Subspectral Law1685 := (show Law2235.Subspectral Law2 from (ImplicationTransfer.singleton_2235 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2236_2 : Law2236.Subspectral Law1685 := (show Law2236.Subspectral Law2 from (ImplicationTransfer.singleton_2236 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2237_2 : Law2237.Subspectral Law1685 := (show Law2237.Subspectral Law2 from (ImplicationTransfer.singleton_2237 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2292_2 : Law2292.Subspectral Law1685 := (show Law2292.Subspectral Law2 from (ImplicationTransfer.singleton_2292 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2294_2 : Law2294.Subspectral Law1313 := (show Law2294.Subspectral Law1313 from (ImplicationTransfer.spectrum_2294_eq_1313).subset).trans basis_route_1313_2

theorem route_2295_2 : Law2295.Subspectral Law1685 := (show Law2295.Subspectral Law2 from (ImplicationTransfer.singleton_2295 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2297_2 : Law2297.Subspectral Law1685 := (show Law2297.Subspectral Law2 from (ImplicationTransfer.singleton_2297 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2298_2 : Law2298.Subspectral Law1685 := (show Law2298.Subspectral Law2 from (ImplicationTransfer.singleton_2298 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2299_2 : Law2299.Subspectral Law1685 := (show Law2299.Subspectral Law2 from (ImplicationTransfer.singleton_2299 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2301_2 : Law2301.Subspectral Law1286 := (show Law2301.Subspectral Law1286 from (ImplicationTransfer.spectrum_2301_eq_1286).subset).trans basis_route_1286_2

theorem route_2302_2 : Law2302.Subspectral Law1685 := (show Law2302.Subspectral Law2 from (ImplicationTransfer.singleton_2302 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2304_3 : Law2304.Subspectral Law883 := (show Law2304.Subspectral Law1323 from (ImplicationTransfer.spectrum_2304_eq_1323).subset).trans basis_route_1323_3

theorem route_2305_2 : Law2305.Subspectral Law1685 := (show Law2305.Subspectral Law2 from (ImplicationTransfer.singleton_2305 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2307_2 : Law2307.Subspectral Law1685 := (show Law2307.Subspectral Law2 from (ImplicationTransfer.singleton_2307 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2308_3 : Law2308.Subspectral Law667 := (show Law2308.Subspectral Law895 from (ImplicationTransfer.spectrum_2308_eq_895).subset).trans basis_route_895_3

theorem route_2309_2 : Law2309.Subspectral Law1685 := (show Law2309.Subspectral Law2 from (ImplicationTransfer.singleton_2309 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2311_2 : Law2311.Subspectral Law1685 := (show Law2311.Subspectral Law2 from (ImplicationTransfer.singleton_2311 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2312_2 : Law2312.Subspectral Law1685 := (show Law2312.Subspectral Law2 from (ImplicationTransfer.singleton_2312 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2313_2 : Law2313.Subspectral Law1685 := (show Law2313.Subspectral Law2 from (ImplicationTransfer.singleton_2313 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2315_2 : Law2315.Subspectral Law1685 := (show Law2315.Subspectral Law2 from (ImplicationTransfer.singleton_2315 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2316_3 : Law2316.Subspectral Law667 := (show Law2316.Subspectral Law898 from (ImplicationTransfer.spectrum_2316_eq_898).subset).trans basis_route_898_3

theorem route_2317_2 : Law2317.Subspectral Law1685 := (show Law2317.Subspectral Law2 from (ImplicationTransfer.singleton_2317 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2319_3 : Law2319.Subspectral Law667 := (show Law2319.Subspectral Law887 from (ImplicationTransfer.spectrum_2319_eq_887).subset).trans basis_route_887_3

theorem route_2320_2 : Law2320.Subspectral Law1685 := (show Law2320.Subspectral Law2 from (ImplicationTransfer.singleton_2320 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2321_2 : Law2321.Subspectral Law1685 := (show Law2321.Subspectral Law2 from (ImplicationTransfer.singleton_2321 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2323_2 : Law2323.Subspectral Law1685 := (show Law2323.Subspectral Law2 from (ImplicationTransfer.singleton_2323 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2324_2 : Law2324.Subspectral Law1685 := (show Law2324.Subspectral Law2 from (ImplicationTransfer.singleton_2324 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2325_2 : Law2325.Subspectral Law1685 := (show Law2325.Subspectral Law2 from (ImplicationTransfer.singleton_2325 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2326_2 : Law2326.Subspectral Law1685 := (show Law2326.Subspectral Law2 from (ImplicationTransfer.singleton_2326 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2328_2 : Law2328.Subspectral Law1279 := (show Law2328.Subspectral Law1279 from (ImplicationTransfer.spectrum_2328_eq_1279).subset).trans basis_route_1279_2

theorem route_2329_2 : Law2329.Subspectral Law1685 := (show Law2329.Subspectral Law2 from (ImplicationTransfer.singleton_2329 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2332_2 : Law2332.Subspectral Law1685 := (show Law2332.Subspectral Law2 from (ImplicationTransfer.singleton_2332 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2334_2 : Law2334.Subspectral Law1685 := (show Law2334.Subspectral Law2 from (ImplicationTransfer.singleton_2334 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2336_2 : Law2336.Subspectral Law1685 := (show Law2336.Subspectral Law2 from (ImplicationTransfer.singleton_2336 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2339_2 : Law2339.Subspectral Law1685 := (show Law2339.Subspectral Law2 from (ImplicationTransfer.singleton_2339 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2341_2 : Law2341.Subspectral Law1685 := (show Law2341.Subspectral Law2 from (ImplicationTransfer.singleton_2341 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2342_2 : Law2342.Subspectral Law1685 := (show Law2342.Subspectral Law2 from (ImplicationTransfer.singleton_2342 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2344_2 : Law2344.Subspectral Law1685 := (show Law2344.Subspectral Law2 from (ImplicationTransfer.singleton_2344 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2345_2 : Law2345.Subspectral Law1685 := (show Law2345.Subspectral Law2 from (ImplicationTransfer.singleton_2345 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2346_2 : Law2346.Subspectral Law1685 := (show Law2346.Subspectral Law2 from (ImplicationTransfer.singleton_2346 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2348_2 : Law2348.Subspectral Law1685 := (show Law2348.Subspectral Law2 from (ImplicationTransfer.singleton_2348 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2350_2 : Law2350.Subspectral Law1685 := (show Law2350.Subspectral Law2 from (ImplicationTransfer.singleton_2350 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2352_2 : Law2352.Subspectral Law1685 := (show Law2352.Subspectral Law2 from (ImplicationTransfer.singleton_2352 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2353_2 : Law2353.Subspectral Law1685 := (show Law2353.Subspectral Law2 from (ImplicationTransfer.singleton_2353 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2354_2 : Law2354.Subspectral Law1685 := (show Law2354.Subspectral Law2 from (ImplicationTransfer.singleton_2354 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2356_2 : Law2356.Subspectral Law1685 := (show Law2356.Subspectral Law2 from (ImplicationTransfer.singleton_2356 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2357_2 : Law2357.Subspectral Law1685 := (show Law2357.Subspectral Law2 from (ImplicationTransfer.singleton_2357 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2358_2 : Law2358.Subspectral Law1685 := (show Law2358.Subspectral Law2 from (ImplicationTransfer.singleton_2358 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2360_2 : Law2360.Subspectral Law1685 := (show Law2360.Subspectral Law2 from (ImplicationTransfer.singleton_2360 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2361_2 : Law2361.Subspectral Law1685 := (show Law2361.Subspectral Law2 from (ImplicationTransfer.singleton_2361 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2362_2 : Law2362.Subspectral Law1685 := (show Law2362.Subspectral Law2 from (ImplicationTransfer.singleton_2362 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2363_2 : Law2363.Subspectral Law1685 := (show Law2363.Subspectral Law2 from (ImplicationTransfer.singleton_2363 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2365_2 : Law2365.Subspectral Law1685 := (show Law2365.Subspectral Law2 from (ImplicationTransfer.singleton_2365 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2366_2 : Law2366.Subspectral Law1685 := (show Law2366.Subspectral Law2 from (ImplicationTransfer.singleton_2366 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2367_2 : Law2367.Subspectral Law1685 := (show Law2367.Subspectral Law2 from (ImplicationTransfer.singleton_2367 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2369_2 : Law2369.Subspectral Law1685 := (show Law2369.Subspectral Law2 from (ImplicationTransfer.singleton_2369 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2370_3 : Law2370.Subspectral Law667 := (show Law2370.Subspectral Law556 from (ImplicationTransfer.spectrum_2370_eq_556).subset).trans basis_route_556_3

theorem route_2371_2 : Law2371.Subspectral Law1685 := (show Law2371.Subspectral Law2 from (ImplicationTransfer.singleton_2371 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2374_2 : Law2374.Subspectral Law1685 := (show Law2374.Subspectral Law2 from (ImplicationTransfer.singleton_2374 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2375_2 : Law2375.Subspectral Law1685 := (show Law2375.Subspectral Law2 from (ImplicationTransfer.singleton_2375 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2377_2 : Law2377.Subspectral Law1685 := (show Law2377.Subspectral Law2 from (ImplicationTransfer.singleton_2377 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2378_2 : Law2378.Subspectral Law1685 := (show Law2378.Subspectral Law2 from (ImplicationTransfer.singleton_2378 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2379_2 : Law2379.Subspectral Law1685 := (show Law2379.Subspectral Law2 from (ImplicationTransfer.singleton_2379 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2380_2 : Law2380.Subspectral Law1685 := (show Law2380.Subspectral Law2 from (ImplicationTransfer.singleton_2380 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2382_2 : Law2382.Subspectral Law1685 := (show Law2382.Subspectral Law2 from (ImplicationTransfer.singleton_2382 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2383_3 : Law2383.Subspectral Law667 := (show Law2383.Subspectral Law556 from (ImplicationTransfer.spectrum_2383_eq_556).subset).trans basis_route_556_3

theorem route_2384_2 : Law2384.Subspectral Law1685 := (show Law2384.Subspectral Law2 from (ImplicationTransfer.singleton_2384 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2386_2 : Law2386.Subspectral Law1685 := (show Law2386.Subspectral Law2 from (ImplicationTransfer.singleton_2386 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2387_2 : Law2387.Subspectral Law1685 := (show Law2387.Subspectral Law2 from (ImplicationTransfer.singleton_2387 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2388_2 : Law2388.Subspectral Law1685 := (show Law2388.Subspectral Law2 from (ImplicationTransfer.singleton_2388 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2390_2 : Law2390.Subspectral Law1685 := (show Law2390.Subspectral Law2 from (ImplicationTransfer.singleton_2390 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2391_2 : Law2391.Subspectral Law1685 := (show Law2391.Subspectral Law2 from (ImplicationTransfer.singleton_2391 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2392_2 : Law2392.Subspectral Law1685 := (show Law2392.Subspectral Law2 from (ImplicationTransfer.singleton_2392 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2394_2 : Law2394.Subspectral Law1685 := (show Law2394.Subspectral Law2 from (ImplicationTransfer.singleton_2394 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2395_2 : Law2395.Subspectral Law1685 := (show Law2395.Subspectral Law2 from (ImplicationTransfer.singleton_2395 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2396_2 : Law2396.Subspectral Law1685 := (show Law2396.Subspectral Law2 from (ImplicationTransfer.singleton_2396 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2397_2 : Law2397.Subspectral Law1685 := (show Law2397.Subspectral Law2 from (ImplicationTransfer.singleton_2397 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2400_2 : Law2400.Subspectral Law1685 := (show Law2400.Subspectral Law2 from (ImplicationTransfer.singleton_2400 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2401_2 : Law2401.Subspectral Law1685 := (show Law2401.Subspectral Law2 from (ImplicationTransfer.singleton_2401 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2403_2 : Law2403.Subspectral Law1685 := (show Law2403.Subspectral Law2 from (ImplicationTransfer.singleton_2403 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2404_2 : Law2404.Subspectral Law1685 := (show Law2404.Subspectral Law2 from (ImplicationTransfer.singleton_2404 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2405_2 : Law2405.Subspectral Law1685 := (show Law2405.Subspectral Law2 from (ImplicationTransfer.singleton_2405 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2407_2 : Law2407.Subspectral Law1685 := (show Law2407.Subspectral Law2 from (ImplicationTransfer.singleton_2407 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2408_2 : Law2408.Subspectral Law1685 := (show Law2408.Subspectral Law2 from (ImplicationTransfer.singleton_2408 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2409_2 : Law2409.Subspectral Law1685 := (show Law2409.Subspectral Law2 from (ImplicationTransfer.singleton_2409 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2411_2 : Law2411.Subspectral Law1685 := (show Law2411.Subspectral Law2 from (ImplicationTransfer.singleton_2411 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2412_2 : Law2412.Subspectral Law1685 := (show Law2412.Subspectral Law2 from (ImplicationTransfer.singleton_2412 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2413_2 : Law2413.Subspectral Law1685 := (show Law2413.Subspectral Law2 from (ImplicationTransfer.singleton_2413 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2414_2 : Law2414.Subspectral Law1685 := (show Law2414.Subspectral Law2 from (ImplicationTransfer.singleton_2414 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2416_2 : Law2416.Subspectral Law1685 := (show Law2416.Subspectral Law2 from (ImplicationTransfer.singleton_2416 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2417_2 : Law2417.Subspectral Law1685 := (show Law2417.Subspectral Law2 from (ImplicationTransfer.singleton_2417 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2418_2 : Law2418.Subspectral Law1685 := (show Law2418.Subspectral Law2 from (ImplicationTransfer.singleton_2418 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2419_2 : Law2419.Subspectral Law1685 := (show Law2419.Subspectral Law2 from (ImplicationTransfer.singleton_2419 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2421_2 : Law2421.Subspectral Law1685 := (show Law2421.Subspectral Law2 from (ImplicationTransfer.singleton_2421 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2422_2 : Law2422.Subspectral Law1685 := (show Law2422.Subspectral Law2 from (ImplicationTransfer.singleton_2422 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2423_2 : Law2423.Subspectral Law1685 := (show Law2423.Subspectral Law2 from (ImplicationTransfer.singleton_2423 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2424_2 : Law2424.Subspectral Law1685 := (show Law2424.Subspectral Law2 from (ImplicationTransfer.singleton_2424 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2426_2 : Law2426.Subspectral Law1685 := (show Law2426.Subspectral Law2 from (ImplicationTransfer.singleton_2426 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2427_2 : Law2427.Subspectral Law1685 := (show Law2427.Subspectral Law2 from (ImplicationTransfer.singleton_2427 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2428_2 : Law2428.Subspectral Law1685 := (show Law2428.Subspectral Law2 from (ImplicationTransfer.singleton_2428 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2429_2 : Law2429.Subspectral Law1685 := (show Law2429.Subspectral Law2 from (ImplicationTransfer.singleton_2429 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2431_2 : Law2431.Subspectral Law1685 := (show Law2431.Subspectral Law2 from (ImplicationTransfer.singleton_2431 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2432_2 : Law2432.Subspectral Law1685 := (show Law2432.Subspectral Law2 from (ImplicationTransfer.singleton_2432 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2433_2 : Law2433.Subspectral Law1685 := (show Law2433.Subspectral Law2 from (ImplicationTransfer.singleton_2433 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2434_2 : Law2434.Subspectral Law1685 := (show Law2434.Subspectral Law2 from (ImplicationTransfer.singleton_2434 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2436_2 : Law2436.Subspectral Law1685 := (show Law2436.Subspectral Law2 from (ImplicationTransfer.singleton_2436 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2437_2 : Law2437.Subspectral Law1685 := (show Law2437.Subspectral Law2 from (ImplicationTransfer.singleton_2437 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2438_2 : Law2438.Subspectral Law1685 := (show Law2438.Subspectral Law2 from (ImplicationTransfer.singleton_2438 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2439_2 : Law2439.Subspectral Law1685 := (show Law2439.Subspectral Law2 from (ImplicationTransfer.singleton_2439 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2440_2 : Law2440.Subspectral Law1685 := (show Law2440.Subspectral Law2 from (ImplicationTransfer.singleton_2440 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2495_2 : Law2495.Subspectral Law1685 := (show Law2495.Subspectral Law2 from (ImplicationTransfer.singleton_2495 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2497_2 : Law2497.Subspectral Law1110 := (show Law2497.Subspectral Law1110 from (ImplicationTransfer.spectrum_2497_eq_1110).subset).trans basis_route_1110_2

theorem route_2498_2 : Law2498.Subspectral Law1685 := (show Law2498.Subspectral Law2 from (ImplicationTransfer.singleton_2498 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2500_2 : Law2500.Subspectral Law1685 := (show Law2500.Subspectral Law2 from (ImplicationTransfer.singleton_2500 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2501_2 : Law2501.Subspectral Law1685 := (show Law2501.Subspectral Law2 from (ImplicationTransfer.singleton_2501 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2502_2 : Law2502.Subspectral Law1685 := (show Law2502.Subspectral Law2 from (ImplicationTransfer.singleton_2502 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2504_2 : Law2504.Subspectral Law1083 := (show Law2504.Subspectral Law1083 from (ImplicationTransfer.spectrum_2504_eq_1083).subset).trans basis_route_1083_2

theorem route_2505_2 : Law2505.Subspectral Law1685 := (show Law2505.Subspectral Law2 from (ImplicationTransfer.singleton_2505 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2508_2 : Law2508.Subspectral Law1685 := (show Law2508.Subspectral Law2 from (ImplicationTransfer.singleton_2508 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2510_2 : Law2510.Subspectral Law1685 := (show Law2510.Subspectral Law2 from (ImplicationTransfer.singleton_2510 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2511_3 : Law2511.Subspectral Law667 := (show Law2511.Subspectral Law556 from (ImplicationTransfer.spectrum_2511_eq_556).subset).trans basis_route_556_3

theorem route_2512_2 : Law2512.Subspectral Law1685 := (show Law2512.Subspectral Law2 from (ImplicationTransfer.singleton_2512 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2514_2 : Law2514.Subspectral Law1685 := (show Law2514.Subspectral Law2 from (ImplicationTransfer.singleton_2514 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2515_2 : Law2515.Subspectral Law1685 := (show Law2515.Subspectral Law2 from (ImplicationTransfer.singleton_2515 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2516_2 : Law2516.Subspectral Law1685 := (show Law2516.Subspectral Law2 from (ImplicationTransfer.singleton_2516 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2518_2 : Law2518.Subspectral Law1685 := (show Law2518.Subspectral Law2 from (ImplicationTransfer.singleton_2518 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2520_2 : Law2520.Subspectral Law1685 := (show Law2520.Subspectral Law2 from (ImplicationTransfer.singleton_2520 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2523_2 : Law2523.Subspectral Law1685 := (show Law2523.Subspectral Law2 from (ImplicationTransfer.singleton_2523 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2524_2 : Law2524.Subspectral Law1685 := (show Law2524.Subspectral Law2 from (ImplicationTransfer.singleton_2524 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2526_2 : Law2526.Subspectral Law1685 := (show Law2526.Subspectral Law2 from (ImplicationTransfer.singleton_2526 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2527_2 : Law2527.Subspectral Law1685 := (show Law2527.Subspectral Law2 from (ImplicationTransfer.singleton_2527 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2528_2 : Law2528.Subspectral Law1685 := (show Law2528.Subspectral Law2 from (ImplicationTransfer.singleton_2528 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2529_2 : Law2529.Subspectral Law1685 := (show Law2529.Subspectral Law2 from (ImplicationTransfer.singleton_2529 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2531_2 : Law2531.Subspectral Law1076 := (show Law2531.Subspectral Law1076 from (ImplicationTransfer.spectrum_2531_eq_1076).subset).trans basis_route_1076_2

theorem route_2532_2 : Law2532.Subspectral Law1685 := (show Law2532.Subspectral Law2 from (ImplicationTransfer.singleton_2532 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2535_2 : Law2535.Subspectral Law1685 := (show Law2535.Subspectral Law2 from (ImplicationTransfer.singleton_2535 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2537_2 : Law2537.Subspectral Law1685 := (show Law2537.Subspectral Law2 from (ImplicationTransfer.singleton_2537 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2539_2 : Law2539.Subspectral Law1685 := (show Law2539.Subspectral Law2 from (ImplicationTransfer.singleton_2539 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2542_2 : Law2542.Subspectral Law1685 := (show Law2542.Subspectral Law2 from (ImplicationTransfer.singleton_2542 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2544_2 : Law2544.Subspectral Law1685 := (show Law2544.Subspectral Law2 from (ImplicationTransfer.singleton_2544 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2545_2 : Law2545.Subspectral Law1685 := (show Law2545.Subspectral Law2 from (ImplicationTransfer.singleton_2545 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2547_2 : Law2547.Subspectral Law1685 := (show Law2547.Subspectral Law2 from (ImplicationTransfer.singleton_2547 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2548_2 : Law2548.Subspectral Law1685 := (show Law2548.Subspectral Law2 from (ImplicationTransfer.singleton_2548 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2549_2 : Law2549.Subspectral Law1685 := (show Law2549.Subspectral Law2 from (ImplicationTransfer.singleton_2549 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2551_2 : Law2551.Subspectral Law1685 := (show Law2551.Subspectral Law2 from (ImplicationTransfer.singleton_2551 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2553_2 : Law2553.Subspectral Law1685 := (show Law2553.Subspectral Law2 from (ImplicationTransfer.singleton_2553 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2555_2 : Law2555.Subspectral Law1685 := (show Law2555.Subspectral Law2 from (ImplicationTransfer.singleton_2555 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2556_2 : Law2556.Subspectral Law1685 := (show Law2556.Subspectral Law2 from (ImplicationTransfer.singleton_2556 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2557_2 : Law2557.Subspectral Law1685 := (show Law2557.Subspectral Law2 from (ImplicationTransfer.singleton_2557 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2559_2 : Law2559.Subspectral Law1685 := (show Law2559.Subspectral Law2 from (ImplicationTransfer.singleton_2559 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2560_2 : Law2560.Subspectral Law1685 := (show Law2560.Subspectral Law2 from (ImplicationTransfer.singleton_2560 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2561_2 : Law2561.Subspectral Law1685 := (show Law2561.Subspectral Law2 from (ImplicationTransfer.singleton_2561 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2563_2 : Law2563.Subspectral Law1685 := (show Law2563.Subspectral Law2 from (ImplicationTransfer.singleton_2563 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2564_2 : Law2564.Subspectral Law1685 := (show Law2564.Subspectral Law2 from (ImplicationTransfer.singleton_2564 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2565_2 : Law2565.Subspectral Law1685 := (show Law2565.Subspectral Law2 from (ImplicationTransfer.singleton_2565 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2566_2 : Law2566.Subspectral Law1685 := (show Law2566.Subspectral Law2 from (ImplicationTransfer.singleton_2566 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2568_2 : Law2568.Subspectral Law1685 := (show Law2568.Subspectral Law2 from (ImplicationTransfer.singleton_2568 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2569_2 : Law2569.Subspectral Law1685 := (show Law2569.Subspectral Law2 from (ImplicationTransfer.singleton_2569 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2570_2 : Law2570.Subspectral Law1685 := (show Law2570.Subspectral Law2 from (ImplicationTransfer.singleton_2570 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2572_2 : Law2572.Subspectral Law1685 := (show Law2572.Subspectral Law2 from (ImplicationTransfer.singleton_2572 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2574_2 : Law2574.Subspectral Law1685 := (show Law2574.Subspectral Law2 from (ImplicationTransfer.singleton_2574 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2577_2 : Law2577.Subspectral Law1685 := (show Law2577.Subspectral Law2 from (ImplicationTransfer.singleton_2577 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2578_2 : Law2578.Subspectral Law1685 := (show Law2578.Subspectral Law2 from (ImplicationTransfer.singleton_2578 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2580_2 : Law2580.Subspectral Law1685 := (show Law2580.Subspectral Law2 from (ImplicationTransfer.singleton_2580 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2581_2 : Law2581.Subspectral Law1685 := (show Law2581.Subspectral Law2 from (ImplicationTransfer.singleton_2581 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2582_2 : Law2582.Subspectral Law1685 := (show Law2582.Subspectral Law2 from (ImplicationTransfer.singleton_2582 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2583_2 : Law2583.Subspectral Law1685 := (show Law2583.Subspectral Law2 from (ImplicationTransfer.singleton_2583 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2585_2 : Law2585.Subspectral Law1685 := (show Law2585.Subspectral Law2 from (ImplicationTransfer.singleton_2585 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2586_3 : Law2586.Subspectral Law667 := (show Law2586.Subspectral Law546 from (ImplicationTransfer.spectrum_2586_eq_546).subset).trans basis_route_546_3

theorem route_2587_2 : Law2587.Subspectral Law1685 := (show Law2587.Subspectral Law2 from (ImplicationTransfer.singleton_2587 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2589_2 : Law2589.Subspectral Law1685 := (show Law2589.Subspectral Law2 from (ImplicationTransfer.singleton_2589 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2590_2 : Law2590.Subspectral Law1685 := (show Law2590.Subspectral Law2 from (ImplicationTransfer.singleton_2590 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2591_2 : Law2591.Subspectral Law1685 := (show Law2591.Subspectral Law2 from (ImplicationTransfer.singleton_2591 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2593_2 : Law2593.Subspectral Law1685 := (show Law2593.Subspectral Law2 from (ImplicationTransfer.singleton_2593 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2594_2 : Law2594.Subspectral Law1685 := (show Law2594.Subspectral Law2 from (ImplicationTransfer.singleton_2594 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2595_2 : Law2595.Subspectral Law1685 := (show Law2595.Subspectral Law2 from (ImplicationTransfer.singleton_2595 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2597_2 : Law2597.Subspectral Law1685 := (show Law2597.Subspectral Law2 from (ImplicationTransfer.singleton_2597 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2598_2 : Law2598.Subspectral Law1685 := (show Law2598.Subspectral Law2 from (ImplicationTransfer.singleton_2598 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2599_2 : Law2599.Subspectral Law1685 := (show Law2599.Subspectral Law2 from (ImplicationTransfer.singleton_2599 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2600_2 : Law2600.Subspectral Law1685 := (show Law2600.Subspectral Law2 from (ImplicationTransfer.singleton_2600 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2603_2 : Law2603.Subspectral Law1685 := (show Law2603.Subspectral Law2 from (ImplicationTransfer.singleton_2603 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2604_2 : Law2604.Subspectral Law1685 := (show Law2604.Subspectral Law2 from (ImplicationTransfer.singleton_2604 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2606_2 : Law2606.Subspectral Law1685 := (show Law2606.Subspectral Law2 from (ImplicationTransfer.singleton_2606 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2607_2 : Law2607.Subspectral Law1685 := (show Law2607.Subspectral Law2 from (ImplicationTransfer.singleton_2607 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2608_2 : Law2608.Subspectral Law1685 := (show Law2608.Subspectral Law2 from (ImplicationTransfer.singleton_2608 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2610_2 : Law2610.Subspectral Law1685 := (show Law2610.Subspectral Law2 from (ImplicationTransfer.singleton_2610 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2611_2 : Law2611.Subspectral Law1685 := (show Law2611.Subspectral Law2 from (ImplicationTransfer.singleton_2611 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2612_2 : Law2612.Subspectral Law1685 := (show Law2612.Subspectral Law2 from (ImplicationTransfer.singleton_2612 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2614_2 : Law2614.Subspectral Law1685 := (show Law2614.Subspectral Law2 from (ImplicationTransfer.singleton_2614 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2615_2 : Law2615.Subspectral Law1685 := (show Law2615.Subspectral Law2 from (ImplicationTransfer.singleton_2615 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2616_2 : Law2616.Subspectral Law1685 := (show Law2616.Subspectral Law2 from (ImplicationTransfer.singleton_2616 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2617_2 : Law2617.Subspectral Law1685 := (show Law2617.Subspectral Law2 from (ImplicationTransfer.singleton_2617 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2619_2 : Law2619.Subspectral Law1685 := (show Law2619.Subspectral Law2 from (ImplicationTransfer.singleton_2619 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2620_2 : Law2620.Subspectral Law1685 := (show Law2620.Subspectral Law2 from (ImplicationTransfer.singleton_2620 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2621_2 : Law2621.Subspectral Law1685 := (show Law2621.Subspectral Law2 from (ImplicationTransfer.singleton_2621 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2622_2 : Law2622.Subspectral Law1685 := (show Law2622.Subspectral Law2 from (ImplicationTransfer.singleton_2622 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2624_2 : Law2624.Subspectral Law1685 := (show Law2624.Subspectral Law2 from (ImplicationTransfer.singleton_2624 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2625_2 : Law2625.Subspectral Law1685 := (show Law2625.Subspectral Law2 from (ImplicationTransfer.singleton_2625 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2626_2 : Law2626.Subspectral Law1685 := (show Law2626.Subspectral Law2 from (ImplicationTransfer.singleton_2626 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2627_2 : Law2627.Subspectral Law1685 := (show Law2627.Subspectral Law2 from (ImplicationTransfer.singleton_2627 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2629_2 : Law2629.Subspectral Law1685 := (show Law2629.Subspectral Law2 from (ImplicationTransfer.singleton_2629 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2630_2 : Law2630.Subspectral Law1685 := (show Law2630.Subspectral Law2 from (ImplicationTransfer.singleton_2630 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2631_2 : Law2631.Subspectral Law1685 := (show Law2631.Subspectral Law2 from (ImplicationTransfer.singleton_2631 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2632_2 : Law2632.Subspectral Law1685 := (show Law2632.Subspectral Law2 from (ImplicationTransfer.singleton_2632 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2634_2 : Law2634.Subspectral Law1685 := (show Law2634.Subspectral Law2 from (ImplicationTransfer.singleton_2634 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2635_2 : Law2635.Subspectral Law1685 := (show Law2635.Subspectral Law2 from (ImplicationTransfer.singleton_2635 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2636_2 : Law2636.Subspectral Law1685 := (show Law2636.Subspectral Law2 from (ImplicationTransfer.singleton_2636 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2637_2 : Law2637.Subspectral Law1685 := (show Law2637.Subspectral Law2 from (ImplicationTransfer.singleton_2637 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2639_2 : Law2639.Subspectral Law1685 := (show Law2639.Subspectral Law2 from (ImplicationTransfer.singleton_2639 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2640_2 : Law2640.Subspectral Law1685 := (show Law2640.Subspectral Law2 from (ImplicationTransfer.singleton_2640 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2641_2 : Law2641.Subspectral Law1685 := (show Law2641.Subspectral Law2 from (ImplicationTransfer.singleton_2641 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2642_2 : Law2642.Subspectral Law1685 := (show Law2642.Subspectral Law2 from (ImplicationTransfer.singleton_2642 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2643_2 : Law2643.Subspectral Law1685 := (show Law2643.Subspectral Law2 from (ImplicationTransfer.singleton_2643 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2698_2 : Law2698.Subspectral Law1685 := (show Law2698.Subspectral Law2 from (ImplicationTransfer.singleton_2698 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2700_2 : Law2700.Subspectral Law907 := (show Law2700.Subspectral Law907 from (ImplicationTransfer.spectrum_2700_eq_907).subset).trans basis_route_907_2

theorem route_2701_2 : Law2701.Subspectral Law1685 := (show Law2701.Subspectral Law2 from (ImplicationTransfer.singleton_2701 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2703_2 : Law2703.Subspectral Law1685 := (show Law2703.Subspectral Law2 from (ImplicationTransfer.singleton_2703 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2704_2 : Law2704.Subspectral Law1685 := (show Law2704.Subspectral Law2 from (ImplicationTransfer.singleton_2704 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2705_2 : Law2705.Subspectral Law1685 := (show Law2705.Subspectral Law2 from (ImplicationTransfer.singleton_2705 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2707_2 : Law2707.Subspectral Law873 := (show Law2707.Subspectral Law880 from (ImplicationTransfer.spectrum_2707_eq_880).subset).trans basis_route_880_2

theorem route_2708_2 : Law2708.Subspectral Law1685 := (show Law2708.Subspectral Law2 from (ImplicationTransfer.singleton_2708 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2711_2 : Law2711.Subspectral Law1685 := (show Law2711.Subspectral Law2 from (ImplicationTransfer.singleton_2711 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2713_2 : Law2713.Subspectral Law1685 := (show Law2713.Subspectral Law2 from (ImplicationTransfer.singleton_2713 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2715_2 : Law2715.Subspectral Law1685 := (show Law2715.Subspectral Law2 from (ImplicationTransfer.singleton_2715 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2717_2 : Law2717.Subspectral Law1685 := (show Law2717.Subspectral Law2 from (ImplicationTransfer.singleton_2717 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2718_2 : Law2718.Subspectral Law1685 := (show Law2718.Subspectral Law2 from (ImplicationTransfer.singleton_2718 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2719_2 : Law2719.Subspectral Law1685 := (show Law2719.Subspectral Law2 from (ImplicationTransfer.singleton_2719 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2721_2 : Law2721.Subspectral Law1685 := (show Law2721.Subspectral Law2 from (ImplicationTransfer.singleton_2721 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2722_3 : Law2722.Subspectral Law667 := (show Law2722.Subspectral Law546 from (ImplicationTransfer.spectrum_2722_eq_546).subset).trans basis_route_546_3

theorem route_2723_2 : Law2723.Subspectral Law1685 := (show Law2723.Subspectral Law2 from (ImplicationTransfer.singleton_2723 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2726_2 : Law2726.Subspectral Law1685 := (show Law2726.Subspectral Law2 from (ImplicationTransfer.singleton_2726 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2727_2 : Law2727.Subspectral Law1685 := (show Law2727.Subspectral Law2 from (ImplicationTransfer.singleton_2727 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2729_2 : Law2729.Subspectral Law1685 := (show Law2729.Subspectral Law2 from (ImplicationTransfer.singleton_2729 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2730_2 : Law2730.Subspectral Law1685 := (show Law2730.Subspectral Law2 from (ImplicationTransfer.singleton_2730 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2731_2 : Law2731.Subspectral Law1685 := (show Law2731.Subspectral Law2 from (ImplicationTransfer.singleton_2731 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2732_2 : Law2732.Subspectral Law1685 := (show Law2732.Subspectral Law2 from (ImplicationTransfer.singleton_2732 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2734_2 : Law2734.Subspectral Law873 := (show Law2734.Subspectral Law873 from (ImplicationTransfer.spectrum_2734_eq_873).subset).trans basis_route_873_2

theorem route_2735_2 : Law2735.Subspectral Law1685 := (show Law2735.Subspectral Law2 from (ImplicationTransfer.singleton_2735 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2738_2 : Law2738.Subspectral Law1685 := (show Law2738.Subspectral Law2 from (ImplicationTransfer.singleton_2738 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2740_2 : Law2740.Subspectral Law1685 := (show Law2740.Subspectral Law2 from (ImplicationTransfer.singleton_2740 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2742_2 : Law2742.Subspectral Law1685 := (show Law2742.Subspectral Law2 from (ImplicationTransfer.singleton_2742 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2744_3 : Law2744.Subspectral Law883 := (show Law2744.Subspectral Law883 from (ImplicationTransfer.spectrum_2744_eq_883).subset).trans basis_route_883_3

theorem route_2745_2 : Law2745.Subspectral Law1685 := (show Law2745.Subspectral Law2 from (ImplicationTransfer.singleton_2745 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2747_2 : Law2747.Subspectral Law1685 := (show Law2747.Subspectral Law2 from (ImplicationTransfer.singleton_2747 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2748_2 : Law2748.Subspectral Law1685 := (show Law2748.Subspectral Law2 from (ImplicationTransfer.singleton_2748 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2750_2 : Law2750.Subspectral Law1685 := (show Law2750.Subspectral Law2 from (ImplicationTransfer.singleton_2750 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2751_2 : Law2751.Subspectral Law1685 := (show Law2751.Subspectral Law2 from (ImplicationTransfer.singleton_2751 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2752_2 : Law2752.Subspectral Law1685 := (show Law2752.Subspectral Law2 from (ImplicationTransfer.singleton_2752 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2754_2 : Law2754.Subspectral Law1685 := (show Law2754.Subspectral Law2 from (ImplicationTransfer.singleton_2754 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2755_3 : Law2755.Subspectral Law667 := (show Law2755.Subspectral Law887 from (ImplicationTransfer.spectrum_2755_eq_887).subset).trans basis_route_887_3

theorem route_2756_2 : Law2756.Subspectral Law1685 := (show Law2756.Subspectral Law2 from (ImplicationTransfer.singleton_2756 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2758_2 : Law2758.Subspectral Law1685 := (show Law2758.Subspectral Law2 from (ImplicationTransfer.singleton_2758 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2759_2 : Law2759.Subspectral Law1685 := (show Law2759.Subspectral Law2 from (ImplicationTransfer.singleton_2759 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2760_2 : Law2760.Subspectral Law1685 := (show Law2760.Subspectral Law2 from (ImplicationTransfer.singleton_2760 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2762_2 : Law2762.Subspectral Law1685 := (show Law2762.Subspectral Law2 from (ImplicationTransfer.singleton_2762 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2763_2 : Law2763.Subspectral Law1685 := (show Law2763.Subspectral Law2 from (ImplicationTransfer.singleton_2763 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2764_2 : Law2764.Subspectral Law1685 := (show Law2764.Subspectral Law2 from (ImplicationTransfer.singleton_2764 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2766_2 : Law2766.Subspectral Law1685 := (show Law2766.Subspectral Law2 from (ImplicationTransfer.singleton_2766 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2767_2 : Law2767.Subspectral Law1685 := (show Law2767.Subspectral Law2 from (ImplicationTransfer.singleton_2767 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2768_2 : Law2768.Subspectral Law1685 := (show Law2768.Subspectral Law2 from (ImplicationTransfer.singleton_2768 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2769_2 : Law2769.Subspectral Law1685 := (show Law2769.Subspectral Law2 from (ImplicationTransfer.singleton_2769 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2771_2 : Law2771.Subspectral Law1685 := (show Law2771.Subspectral Law2 from (ImplicationTransfer.singleton_2771 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2772_2 : Law2772.Subspectral Law1685 := (show Law2772.Subspectral Law2 from (ImplicationTransfer.singleton_2772 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2773_2 : Law2773.Subspectral Law1685 := (show Law2773.Subspectral Law2 from (ImplicationTransfer.singleton_2773 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2775_2 : Law2775.Subspectral Law1685 := (show Law2775.Subspectral Law2 from (ImplicationTransfer.singleton_2775 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2776_3 : Law2776.Subspectral Law667 := (show Law2776.Subspectral Law546 from (ImplicationTransfer.spectrum_2776_eq_546).subset).trans basis_route_546_3

theorem route_2777_2 : Law2777.Subspectral Law1685 := (show Law2777.Subspectral Law2 from (ImplicationTransfer.singleton_2777 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2780_2 : Law2780.Subspectral Law1685 := (show Law2780.Subspectral Law2 from (ImplicationTransfer.singleton_2780 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2781_2 : Law2781.Subspectral Law1685 := (show Law2781.Subspectral Law2 from (ImplicationTransfer.singleton_2781 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2783_2 : Law2783.Subspectral Law1685 := (show Law2783.Subspectral Law2 from (ImplicationTransfer.singleton_2783 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2784_2 : Law2784.Subspectral Law1685 := (show Law2784.Subspectral Law2 from (ImplicationTransfer.singleton_2784 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2785_2 : Law2785.Subspectral Law1685 := (show Law2785.Subspectral Law2 from (ImplicationTransfer.singleton_2785 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2786_2 : Law2786.Subspectral Law1685 := (show Law2786.Subspectral Law2 from (ImplicationTransfer.singleton_2786 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2788_2 : Law2788.Subspectral Law1685 := (show Law2788.Subspectral Law2 from (ImplicationTransfer.singleton_2788 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2789_3 : Law2789.Subspectral Law667 := (show Law2789.Subspectral Law895 from (ImplicationTransfer.spectrum_2789_eq_895).subset).trans basis_route_895_3

theorem route_2790_2 : Law2790.Subspectral Law1685 := (show Law2790.Subspectral Law2 from (ImplicationTransfer.singleton_2790 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2792_2 : Law2792.Subspectral Law1685 := (show Law2792.Subspectral Law2 from (ImplicationTransfer.singleton_2792 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2793_2 : Law2793.Subspectral Law1685 := (show Law2793.Subspectral Law2 from (ImplicationTransfer.singleton_2793 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2794_2 : Law2794.Subspectral Law1685 := (show Law2794.Subspectral Law2 from (ImplicationTransfer.singleton_2794 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2796_2 : Law2796.Subspectral Law1685 := (show Law2796.Subspectral Law2 from (ImplicationTransfer.singleton_2796 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2797_2 : Law2797.Subspectral Law1685 := (show Law2797.Subspectral Law2 from (ImplicationTransfer.singleton_2797 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2798_2 : Law2798.Subspectral Law1685 := (show Law2798.Subspectral Law2 from (ImplicationTransfer.singleton_2798 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2800_2 : Law2800.Subspectral Law1685 := (show Law2800.Subspectral Law2 from (ImplicationTransfer.singleton_2800 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2801_2 : Law2801.Subspectral Law1685 := (show Law2801.Subspectral Law2 from (ImplicationTransfer.singleton_2801 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2802_2 : Law2802.Subspectral Law1685 := (show Law2802.Subspectral Law2 from (ImplicationTransfer.singleton_2802 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2803_2 : Law2803.Subspectral Law1685 := (show Law2803.Subspectral Law2 from (ImplicationTransfer.singleton_2803 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2805_3 : Law2805.Subspectral Law667 := (show Law2805.Subspectral Law898 from (ImplicationTransfer.spectrum_2805_eq_898).subset).trans basis_route_898_3

theorem route_2806_2 : Law2806.Subspectral Law1685 := (show Law2806.Subspectral Law2 from (ImplicationTransfer.singleton_2806 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2807_2 : Law2807.Subspectral Law1685 := (show Law2807.Subspectral Law2 from (ImplicationTransfer.singleton_2807 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2809_2 : Law2809.Subspectral Law1685 := (show Law2809.Subspectral Law2 from (ImplicationTransfer.singleton_2809 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2810_2 : Law2810.Subspectral Law1685 := (show Law2810.Subspectral Law2 from (ImplicationTransfer.singleton_2810 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2811_2 : Law2811.Subspectral Law1685 := (show Law2811.Subspectral Law2 from (ImplicationTransfer.singleton_2811 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2813_2 : Law2813.Subspectral Law1685 := (show Law2813.Subspectral Law2 from (ImplicationTransfer.singleton_2813 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2814_2 : Law2814.Subspectral Law1685 := (show Law2814.Subspectral Law2 from (ImplicationTransfer.singleton_2814 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2815_2 : Law2815.Subspectral Law1685 := (show Law2815.Subspectral Law2 from (ImplicationTransfer.singleton_2815 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2817_2 : Law2817.Subspectral Law1685 := (show Law2817.Subspectral Law2 from (ImplicationTransfer.singleton_2817 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2818_2 : Law2818.Subspectral Law1685 := (show Law2818.Subspectral Law2 from (ImplicationTransfer.singleton_2818 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2819_2 : Law2819.Subspectral Law1685 := (show Law2819.Subspectral Law2 from (ImplicationTransfer.singleton_2819 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2820_2 : Law2820.Subspectral Law1685 := (show Law2820.Subspectral Law2 from (ImplicationTransfer.singleton_2820 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2822_2 : Law2822.Subspectral Law1685 := (show Law2822.Subspectral Law2 from (ImplicationTransfer.singleton_2822 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2823_2 : Law2823.Subspectral Law1685 := (show Law2823.Subspectral Law2 from (ImplicationTransfer.singleton_2823 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2824_2 : Law2824.Subspectral Law1685 := (show Law2824.Subspectral Law2 from (ImplicationTransfer.singleton_2824 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2825_2 : Law2825.Subspectral Law1685 := (show Law2825.Subspectral Law2 from (ImplicationTransfer.singleton_2825 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2827_2 : Law2827.Subspectral Law1685 := (show Law2827.Subspectral Law2 from (ImplicationTransfer.singleton_2827 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2828_2 : Law2828.Subspectral Law1685 := (show Law2828.Subspectral Law2 from (ImplicationTransfer.singleton_2828 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2829_2 : Law2829.Subspectral Law1685 := (show Law2829.Subspectral Law2 from (ImplicationTransfer.singleton_2829 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2830_2 : Law2830.Subspectral Law1685 := (show Law2830.Subspectral Law2 from (ImplicationTransfer.singleton_2830 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2832_2 : Law2832.Subspectral Law1685 := (show Law2832.Subspectral Law2 from (ImplicationTransfer.singleton_2832 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2833_2 : Law2833.Subspectral Law1685 := (show Law2833.Subspectral Law2 from (ImplicationTransfer.singleton_2833 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2834_2 : Law2834.Subspectral Law1685 := (show Law2834.Subspectral Law2 from (ImplicationTransfer.singleton_2834 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2835_2 : Law2835.Subspectral Law1685 := (show Law2835.Subspectral Law2 from (ImplicationTransfer.singleton_2835 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2837_2 : Law2837.Subspectral Law1685 := (show Law2837.Subspectral Law2 from (ImplicationTransfer.singleton_2837 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2838_2 : Law2838.Subspectral Law1685 := (show Law2838.Subspectral Law2 from (ImplicationTransfer.singleton_2838 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2839_2 : Law2839.Subspectral Law1685 := (show Law2839.Subspectral Law2 from (ImplicationTransfer.singleton_2839 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2840_2 : Law2840.Subspectral Law1685 := (show Law2840.Subspectral Law2 from (ImplicationTransfer.singleton_2840 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2842_2 : Law2842.Subspectral Law1685 := (show Law2842.Subspectral Law2 from (ImplicationTransfer.singleton_2842 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2843_2 : Law2843.Subspectral Law1685 := (show Law2843.Subspectral Law2 from (ImplicationTransfer.singleton_2843 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2844_2 : Law2844.Subspectral Law1685 := (show Law2844.Subspectral Law2 from (ImplicationTransfer.singleton_2844 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2845_2 : Law2845.Subspectral Law1685 := (show Law2845.Subspectral Law2 from (ImplicationTransfer.singleton_2845 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2846_2 : Law2846.Subspectral Law1685 := (show Law2846.Subspectral Law2 from (ImplicationTransfer.singleton_2846 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2900_3 : Law2900.Subspectral Law667 := (show Law2900.Subspectral Law667 from (ImplicationTransfer.spectrum_2900_eq_667).subset).trans basis_route_667_3

theorem route_2901_2 : Law2901.Subspectral Law1685 := (show Law2901.Subspectral Law2 from (ImplicationTransfer.singleton_2901 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2903_2 : Law2903.Subspectral Law704 := (show Law2903.Subspectral Law704 from (ImplicationTransfer.spectrum_2903_eq_704).subset).trans basis_route_704_2

theorem route_2904_2 : Law2904.Subspectral Law1685 := (show Law2904.Subspectral Law2 from (ImplicationTransfer.singleton_2904 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2906_2 : Law2906.Subspectral Law1685 := (show Law2906.Subspectral Law2 from (ImplicationTransfer.singleton_2906 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2907_2 : Law2907.Subspectral Law1685 := (show Law2907.Subspectral Law2 from (ImplicationTransfer.singleton_2907 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2908_2 : Law2908.Subspectral Law1685 := (show Law2908.Subspectral Law2 from (ImplicationTransfer.singleton_2908 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2910_2 : Law2910.Subspectral Law677 := (show Law2910.Subspectral Law677 from (ImplicationTransfer.spectrum_2910_eq_677).subset).trans basis_route_677_2

theorem route_2911_2 : Law2911.Subspectral Law1685 := (show Law2911.Subspectral Law2 from (ImplicationTransfer.singleton_2911 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2914_2 : Law2914.Subspectral Law1685 := (show Law2914.Subspectral Law2 from (ImplicationTransfer.singleton_2914 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2916_2 : Law2916.Subspectral Law1685 := (show Law2916.Subspectral Law2 from (ImplicationTransfer.singleton_2916 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2918_2 : Law2918.Subspectral Law1685 := (show Law2918.Subspectral Law2 from (ImplicationTransfer.singleton_2918 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2920_2 : Law2920.Subspectral Law1685 := (show Law2920.Subspectral Law2 from (ImplicationTransfer.singleton_2920 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2921_2 : Law2921.Subspectral Law1685 := (show Law2921.Subspectral Law2 from (ImplicationTransfer.singleton_2921 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2922_2 : Law2922.Subspectral Law1685 := (show Law2922.Subspectral Law2 from (ImplicationTransfer.singleton_2922 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2924_2 : Law2924.Subspectral Law1685 := (show Law2924.Subspectral Law2 from (ImplicationTransfer.singleton_2924 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2926_2 : Law2926.Subspectral Law1685 := (show Law2926.Subspectral Law2 from (ImplicationTransfer.singleton_2926 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2928_3 : Law2928.Subspectral Law667 := (show Law2928.Subspectral Law556 from (ImplicationTransfer.spectrum_2928_eq_556).subset).trans basis_route_556_3

theorem route_2929_2 : Law2929.Subspectral Law1685 := (show Law2929.Subspectral Law2 from (ImplicationTransfer.singleton_2929 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2930_2 : Law2930.Subspectral Law1685 := (show Law2930.Subspectral Law2 from (ImplicationTransfer.singleton_2930 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2932_2 : Law2932.Subspectral Law1685 := (show Law2932.Subspectral Law2 from (ImplicationTransfer.singleton_2932 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2933_2 : Law2933.Subspectral Law1685 := (show Law2933.Subspectral Law2 from (ImplicationTransfer.singleton_2933 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2934_2 : Law2934.Subspectral Law1685 := (show Law2934.Subspectral Law2 from (ImplicationTransfer.singleton_2934 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2935_2 : Law2935.Subspectral Law1685 := (show Law2935.Subspectral Law2 from (ImplicationTransfer.singleton_2935 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2937_2 : Law2937.Subspectral Law670 := (show Law2937.Subspectral Law670 from (ImplicationTransfer.spectrum_2937_eq_670).subset).trans basis_route_670_2

theorem route_2938_2 : Law2938.Subspectral Law1685 := (show Law2938.Subspectral Law2 from (ImplicationTransfer.singleton_2938 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2941_2 : Law2941.Subspectral Law1685 := (show Law2941.Subspectral Law2 from (ImplicationTransfer.singleton_2941 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2943_2 : Law2943.Subspectral Law1685 := (show Law2943.Subspectral Law2 from (ImplicationTransfer.singleton_2943 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2945_2 : Law2945.Subspectral Law1685 := (show Law2945.Subspectral Law2 from (ImplicationTransfer.singleton_2945 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2948_2 : Law2948.Subspectral Law1685 := (show Law2948.Subspectral Law2 from (ImplicationTransfer.singleton_2948 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2950_2 : Law2950.Subspectral Law1685 := (show Law2950.Subspectral Law2 from (ImplicationTransfer.singleton_2950 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2951_2 : Law2951.Subspectral Law1685 := (show Law2951.Subspectral Law2 from (ImplicationTransfer.singleton_2951 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2953_2 : Law2953.Subspectral Law1685 := (show Law2953.Subspectral Law2 from (ImplicationTransfer.singleton_2953 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2954_2 : Law2954.Subspectral Law1685 := (show Law2954.Subspectral Law2 from (ImplicationTransfer.singleton_2954 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2955_2 : Law2955.Subspectral Law1685 := (show Law2955.Subspectral Law2 from (ImplicationTransfer.singleton_2955 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2957_2 : Law2957.Subspectral Law1685 := (show Law2957.Subspectral Law2 from (ImplicationTransfer.singleton_2957 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2959_2 : Law2959.Subspectral Law1685 := (show Law2959.Subspectral Law2 from (ImplicationTransfer.singleton_2959 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2961_2 : Law2961.Subspectral Law1685 := (show Law2961.Subspectral Law2 from (ImplicationTransfer.singleton_2961 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2962_2 : Law2962.Subspectral Law1685 := (show Law2962.Subspectral Law2 from (ImplicationTransfer.singleton_2962 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2963_2 : Law2963.Subspectral Law1685 := (show Law2963.Subspectral Law2 from (ImplicationTransfer.singleton_2963 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2965_2 : Law2965.Subspectral Law1685 := (show Law2965.Subspectral Law2 from (ImplicationTransfer.singleton_2965 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2966_2 : Law2966.Subspectral Law1685 := (show Law2966.Subspectral Law2 from (ImplicationTransfer.singleton_2966 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2967_2 : Law2967.Subspectral Law1685 := (show Law2967.Subspectral Law2 from (ImplicationTransfer.singleton_2967 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2969_2 : Law2969.Subspectral Law1685 := (show Law2969.Subspectral Law2 from (ImplicationTransfer.singleton_2969 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2970_2 : Law2970.Subspectral Law1685 := (show Law2970.Subspectral Law2 from (ImplicationTransfer.singleton_2970 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2971_2 : Law2971.Subspectral Law1685 := (show Law2971.Subspectral Law2 from (ImplicationTransfer.singleton_2971 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2972_2 : Law2972.Subspectral Law1685 := (show Law2972.Subspectral Law2 from (ImplicationTransfer.singleton_2972 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2974_2 : Law2974.Subspectral Law1685 := (show Law2974.Subspectral Law2 from (ImplicationTransfer.singleton_2974 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2975_2 : Law2975.Subspectral Law1685 := (show Law2975.Subspectral Law2 from (ImplicationTransfer.singleton_2975 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2976_2 : Law2976.Subspectral Law1685 := (show Law2976.Subspectral Law2 from (ImplicationTransfer.singleton_2976 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2978_2 : Law2978.Subspectral Law1685 := (show Law2978.Subspectral Law2 from (ImplicationTransfer.singleton_2978 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2980_2 : Law2980.Subspectral Law1685 := (show Law2980.Subspectral Law2 from (ImplicationTransfer.singleton_2980 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2982_3 : Law2982.Subspectral Law667 := (show Law2982.Subspectral Law556 from (ImplicationTransfer.spectrum_2982_eq_556).subset).trans basis_route_556_3

theorem route_2983_2 : Law2983.Subspectral Law1685 := (show Law2983.Subspectral Law2 from (ImplicationTransfer.singleton_2983 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2984_2 : Law2984.Subspectral Law1685 := (show Law2984.Subspectral Law2 from (ImplicationTransfer.singleton_2984 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2986_2 : Law2986.Subspectral Law1685 := (show Law2986.Subspectral Law2 from (ImplicationTransfer.singleton_2986 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2987_2 : Law2987.Subspectral Law1685 := (show Law2987.Subspectral Law2 from (ImplicationTransfer.singleton_2987 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2988_2 : Law2988.Subspectral Law1685 := (show Law2988.Subspectral Law2 from (ImplicationTransfer.singleton_2988 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2989_2 : Law2989.Subspectral Law1685 := (show Law2989.Subspectral Law2 from (ImplicationTransfer.singleton_2989 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2991_2 : Law2991.Subspectral Law1685 := (show Law2991.Subspectral Law2 from (ImplicationTransfer.singleton_2991 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2993_2 : Law2993.Subspectral Law1685 := (show Law2993.Subspectral Law2 from (ImplicationTransfer.singleton_2993 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2995_2 : Law2995.Subspectral Law1685 := (show Law2995.Subspectral Law2 from (ImplicationTransfer.singleton_2995 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2996_2 : Law2996.Subspectral Law1685 := (show Law2996.Subspectral Law2 from (ImplicationTransfer.singleton_2996 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2997_2 : Law2997.Subspectral Law1685 := (show Law2997.Subspectral Law2 from (ImplicationTransfer.singleton_2997 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_2999_2 : Law2999.Subspectral Law1685 := (show Law2999.Subspectral Law2 from (ImplicationTransfer.singleton_2999 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3000_2 : Law3000.Subspectral Law1685 := (show Law3000.Subspectral Law2 from (ImplicationTransfer.singleton_3000 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3001_2 : Law3001.Subspectral Law1685 := (show Law3001.Subspectral Law2 from (ImplicationTransfer.singleton_3001 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3003_2 : Law3003.Subspectral Law1685 := (show Law3003.Subspectral Law2 from (ImplicationTransfer.singleton_3003 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3004_2 : Law3004.Subspectral Law1685 := (show Law3004.Subspectral Law2 from (ImplicationTransfer.singleton_3004 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3005_2 : Law3005.Subspectral Law1685 := (show Law3005.Subspectral Law2 from (ImplicationTransfer.singleton_3005 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3006_2 : Law3006.Subspectral Law1685 := (show Law3006.Subspectral Law2 from (ImplicationTransfer.singleton_3006 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3008_3 : Law3008.Subspectral Law667 := (show Law3008.Subspectral Law695 from (ImplicationTransfer.spectrum_3008_eq_695).subset).trans basis_route_695_3

theorem route_3009_2 : Law3009.Subspectral Law1685 := (show Law3009.Subspectral Law2 from (ImplicationTransfer.singleton_3009 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3010_2 : Law3010.Subspectral Law1685 := (show Law3010.Subspectral Law2 from (ImplicationTransfer.singleton_3010 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3012_2 : Law3012.Subspectral Law1685 := (show Law3012.Subspectral Law2 from (ImplicationTransfer.singleton_3012 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3013_2 : Law3013.Subspectral Law1685 := (show Law3013.Subspectral Law2 from (ImplicationTransfer.singleton_3013 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3014_2 : Law3014.Subspectral Law1685 := (show Law3014.Subspectral Law2 from (ImplicationTransfer.singleton_3014 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3016_2 : Law3016.Subspectral Law1685 := (show Law3016.Subspectral Law2 from (ImplicationTransfer.singleton_3016 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3017_2 : Law3017.Subspectral Law1685 := (show Law3017.Subspectral Law2 from (ImplicationTransfer.singleton_3017 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3018_2 : Law3018.Subspectral Law1685 := (show Law3018.Subspectral Law2 from (ImplicationTransfer.singleton_3018 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3020_2 : Law3020.Subspectral Law1685 := (show Law3020.Subspectral Law2 from (ImplicationTransfer.singleton_3020 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3021_2 : Law3021.Subspectral Law1685 := (show Law3021.Subspectral Law2 from (ImplicationTransfer.singleton_3021 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3022_2 : Law3022.Subspectral Law1685 := (show Law3022.Subspectral Law2 from (ImplicationTransfer.singleton_3022 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3023_2 : Law3023.Subspectral Law1685 := (show Law3023.Subspectral Law2 from (ImplicationTransfer.singleton_3023 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3025_2 : Law3025.Subspectral Law1685 := (show Law3025.Subspectral Law2 from (ImplicationTransfer.singleton_3025 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3026_2 : Law3026.Subspectral Law1685 := (show Law3026.Subspectral Law2 from (ImplicationTransfer.singleton_3026 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3027_2 : Law3027.Subspectral Law1685 := (show Law3027.Subspectral Law2 from (ImplicationTransfer.singleton_3027 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3028_2 : Law3028.Subspectral Law1685 := (show Law3028.Subspectral Law2 from (ImplicationTransfer.singleton_3028 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3030_2 : Law3030.Subspectral Law1685 := (show Law3030.Subspectral Law2 from (ImplicationTransfer.singleton_3030 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3031_2 : Law3031.Subspectral Law1685 := (show Law3031.Subspectral Law2 from (ImplicationTransfer.singleton_3031 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3032_2 : Law3032.Subspectral Law1685 := (show Law3032.Subspectral Law2 from (ImplicationTransfer.singleton_3032 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3033_2 : Law3033.Subspectral Law1685 := (show Law3033.Subspectral Law2 from (ImplicationTransfer.singleton_3033 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3035_2 : Law3035.Subspectral Law1685 := (show Law3035.Subspectral Law2 from (ImplicationTransfer.singleton_3035 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3036_2 : Law3036.Subspectral Law1685 := (show Law3036.Subspectral Law2 from (ImplicationTransfer.singleton_3036 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3037_2 : Law3037.Subspectral Law1685 := (show Law3037.Subspectral Law2 from (ImplicationTransfer.singleton_3037 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3038_2 : Law3038.Subspectral Law1685 := (show Law3038.Subspectral Law2 from (ImplicationTransfer.singleton_3038 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3040_2 : Law3040.Subspectral Law1685 := (show Law3040.Subspectral Law2 from (ImplicationTransfer.singleton_3040 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3041_2 : Law3041.Subspectral Law1685 := (show Law3041.Subspectral Law2 from (ImplicationTransfer.singleton_3041 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3042_2 : Law3042.Subspectral Law1685 := (show Law3042.Subspectral Law2 from (ImplicationTransfer.singleton_3042 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3043_2 : Law3043.Subspectral Law1685 := (show Law3043.Subspectral Law2 from (ImplicationTransfer.singleton_3043 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3045_2 : Law3045.Subspectral Law1685 := (show Law3045.Subspectral Law2 from (ImplicationTransfer.singleton_3045 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3046_2 : Law3046.Subspectral Law1685 := (show Law3046.Subspectral Law2 from (ImplicationTransfer.singleton_3046 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3047_2 : Law3047.Subspectral Law1685 := (show Law3047.Subspectral Law2 from (ImplicationTransfer.singleton_3047 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3048_2 : Law3048.Subspectral Law1685 := (show Law3048.Subspectral Law2 from (ImplicationTransfer.singleton_3048 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3049_2 : Law3049.Subspectral Law1685 := (show Law3049.Subspectral Law2 from (ImplicationTransfer.singleton_3049 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3104_2 : Law3104.Subspectral Law1685 := (show Law3104.Subspectral Law2 from (ImplicationTransfer.singleton_3104 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3106_2 : Law3106.Subspectral Law501 := (show Law3106.Subspectral Law501 from (ImplicationTransfer.spectrum_3106_eq_501).subset).trans basis_route_501_2

theorem route_3107_2 : Law3107.Subspectral Law1685 := (show Law3107.Subspectral Law2 from (ImplicationTransfer.singleton_3107 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3109_2 : Law3109.Subspectral Law1685 := (show Law3109.Subspectral Law2 from (ImplicationTransfer.singleton_3109 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3110_2 : Law3110.Subspectral Law1685 := (show Law3110.Subspectral Law2 from (ImplicationTransfer.singleton_3110 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3111_2 : Law3111.Subspectral Law1685 := (show Law3111.Subspectral Law2 from (ImplicationTransfer.singleton_3111 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3113_2 : Law3113.Subspectral Law474 := (show Law3113.Subspectral Law474 from (ImplicationTransfer.spectrum_3113_eq_474).subset).trans basis_route_474_2

theorem route_3114_2 : Law3114.Subspectral Law1685 := (show Law3114.Subspectral Law2 from (ImplicationTransfer.singleton_3114 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3117_2 : Law3117.Subspectral Law1685 := (show Law3117.Subspectral Law2 from (ImplicationTransfer.singleton_3117 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3119_2 : Law3119.Subspectral Law1685 := (show Law3119.Subspectral Law2 from (ImplicationTransfer.singleton_3119 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3121_2 : Law3121.Subspectral Law1685 := (show Law3121.Subspectral Law2 from (ImplicationTransfer.singleton_3121 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3123_2 : Law3123.Subspectral Law1685 := (show Law3123.Subspectral Law2 from (ImplicationTransfer.singleton_3123 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3124_2 : Law3124.Subspectral Law1685 := (show Law3124.Subspectral Law2 from (ImplicationTransfer.singleton_3124 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3125_2 : Law3125.Subspectral Law1685 := (show Law3125.Subspectral Law2 from (ImplicationTransfer.singleton_3125 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3127_2 : Law3127.Subspectral Law1685 := (show Law3127.Subspectral Law2 from (ImplicationTransfer.singleton_3127 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3128_3 : Law3128.Subspectral Law667 := (show Law3128.Subspectral Law556 from (ImplicationTransfer.spectrum_3128_eq_556).subset).trans basis_route_556_3

theorem route_3129_2 : Law3129.Subspectral Law1685 := (show Law3129.Subspectral Law2 from (ImplicationTransfer.singleton_3129 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3132_2 : Law3132.Subspectral Law1685 := (show Law3132.Subspectral Law2 from (ImplicationTransfer.singleton_3132 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3133_2 : Law3133.Subspectral Law1685 := (show Law3133.Subspectral Law2 from (ImplicationTransfer.singleton_3133 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3135_2 : Law3135.Subspectral Law1685 := (show Law3135.Subspectral Law2 from (ImplicationTransfer.singleton_3135 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3136_2 : Law3136.Subspectral Law1685 := (show Law3136.Subspectral Law2 from (ImplicationTransfer.singleton_3136 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3137_2 : Law3137.Subspectral Law1685 := (show Law3137.Subspectral Law2 from (ImplicationTransfer.singleton_3137 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3138_2 : Law3138.Subspectral Law1685 := (show Law3138.Subspectral Law2 from (ImplicationTransfer.singleton_3138 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3140_2 : Law3140.Subspectral Law467 := (show Law3140.Subspectral Law467 from (ImplicationTransfer.spectrum_3140_eq_467).subset).trans basis_route_467_2

theorem route_3141_2 : Law3141.Subspectral Law1685 := (show Law3141.Subspectral Law2 from (ImplicationTransfer.singleton_3141 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3144_2 : Law3144.Subspectral Law1685 := (show Law3144.Subspectral Law2 from (ImplicationTransfer.singleton_3144 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3146_2 : Law3146.Subspectral Law1685 := (show Law3146.Subspectral Law2 from (ImplicationTransfer.singleton_3146 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3148_2 : Law3148.Subspectral Law1685 := (show Law3148.Subspectral Law2 from (ImplicationTransfer.singleton_3148 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3151_2 : Law3151.Subspectral Law1685 := (show Law3151.Subspectral Law2 from (ImplicationTransfer.singleton_3151 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3153_2 : Law3153.Subspectral Law1685 := (show Law3153.Subspectral Law2 from (ImplicationTransfer.singleton_3153 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3154_2 : Law3154.Subspectral Law1685 := (show Law3154.Subspectral Law2 from (ImplicationTransfer.singleton_3154 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3156_2 : Law3156.Subspectral Law1685 := (show Law3156.Subspectral Law2 from (ImplicationTransfer.singleton_3156 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3157_2 : Law3157.Subspectral Law1685 := (show Law3157.Subspectral Law2 from (ImplicationTransfer.singleton_3157 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3158_2 : Law3158.Subspectral Law1685 := (show Law3158.Subspectral Law2 from (ImplicationTransfer.singleton_3158 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3160_2 : Law3160.Subspectral Law1685 := (show Law3160.Subspectral Law2 from (ImplicationTransfer.singleton_3160 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3161_3 : Law3161.Subspectral Law481 := (show Law3161.Subspectral Law481 from (ImplicationTransfer.spectrum_3161_eq_481).subset).trans basis_route_481_3

theorem route_3162_2 : Law3162.Subspectral Law1685 := (show Law3162.Subspectral Law2 from (ImplicationTransfer.singleton_3162 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3164_2 : Law3164.Subspectral Law1685 := (show Law3164.Subspectral Law2 from (ImplicationTransfer.singleton_3164 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3165_2 : Law3165.Subspectral Law1685 := (show Law3165.Subspectral Law2 from (ImplicationTransfer.singleton_3165 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3166_2 : Law3166.Subspectral Law1685 := (show Law3166.Subspectral Law2 from (ImplicationTransfer.singleton_3166 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3168_2 : Law3168.Subspectral Law1685 := (show Law3168.Subspectral Law2 from (ImplicationTransfer.singleton_3168 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3169_2 : Law3169.Subspectral Law1685 := (show Law3169.Subspectral Law2 from (ImplicationTransfer.singleton_3169 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3170_2 : Law3170.Subspectral Law1685 := (show Law3170.Subspectral Law2 from (ImplicationTransfer.singleton_3170 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3172_2 : Law3172.Subspectral Law1685 := (show Law3172.Subspectral Law2 from (ImplicationTransfer.singleton_3172 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3173_2 : Law3173.Subspectral Law1685 := (show Law3173.Subspectral Law2 from (ImplicationTransfer.singleton_3173 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3174_2 : Law3174.Subspectral Law1685 := (show Law3174.Subspectral Law2 from (ImplicationTransfer.singleton_3174 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3175_2 : Law3175.Subspectral Law1685 := (show Law3175.Subspectral Law2 from (ImplicationTransfer.singleton_3175 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3177_2 : Law3177.Subspectral Law1685 := (show Law3177.Subspectral Law2 from (ImplicationTransfer.singleton_3177 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3178_2 : Law3178.Subspectral Law1685 := (show Law3178.Subspectral Law2 from (ImplicationTransfer.singleton_3178 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3179_2 : Law3179.Subspectral Law1685 := (show Law3179.Subspectral Law2 from (ImplicationTransfer.singleton_3179 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3181_2 : Law3181.Subspectral Law1685 := (show Law3181.Subspectral Law2 from (ImplicationTransfer.singleton_3181 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3183_2 : Law3183.Subspectral Law1685 := (show Law3183.Subspectral Law2 from (ImplicationTransfer.singleton_3183 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3185_3 : Law3185.Subspectral Law667 := (show Law3185.Subspectral Law546 from (ImplicationTransfer.spectrum_3185_eq_546).subset).trans basis_route_546_3

theorem route_3186_2 : Law3186.Subspectral Law1685 := (show Law3186.Subspectral Law2 from (ImplicationTransfer.singleton_3186 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3187_2 : Law3187.Subspectral Law1685 := (show Law3187.Subspectral Law2 from (ImplicationTransfer.singleton_3187 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3189_2 : Law3189.Subspectral Law1685 := (show Law3189.Subspectral Law2 from (ImplicationTransfer.singleton_3189 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3190_2 : Law3190.Subspectral Law1685 := (show Law3190.Subspectral Law2 from (ImplicationTransfer.singleton_3190 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3191_2 : Law3191.Subspectral Law1685 := (show Law3191.Subspectral Law2 from (ImplicationTransfer.singleton_3191 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3192_2 : Law3192.Subspectral Law1685 := (show Law3192.Subspectral Law2 from (ImplicationTransfer.singleton_3192 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3194_2 : Law3194.Subspectral Law1685 := (show Law3194.Subspectral Law2 from (ImplicationTransfer.singleton_3194 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3196_2 : Law3196.Subspectral Law1685 := (show Law3196.Subspectral Law2 from (ImplicationTransfer.singleton_3196 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3198_2 : Law3198.Subspectral Law1685 := (show Law3198.Subspectral Law2 from (ImplicationTransfer.singleton_3198 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3199_2 : Law3199.Subspectral Law1685 := (show Law3199.Subspectral Law2 from (ImplicationTransfer.singleton_3199 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3200_2 : Law3200.Subspectral Law1685 := (show Law3200.Subspectral Law2 from (ImplicationTransfer.singleton_3200 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3202_2 : Law3202.Subspectral Law1685 := (show Law3202.Subspectral Law2 from (ImplicationTransfer.singleton_3202 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3203_2 : Law3203.Subspectral Law1685 := (show Law3203.Subspectral Law2 from (ImplicationTransfer.singleton_3203 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3204_2 : Law3204.Subspectral Law1685 := (show Law3204.Subspectral Law2 from (ImplicationTransfer.singleton_3204 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3206_2 : Law3206.Subspectral Law1685 := (show Law3206.Subspectral Law2 from (ImplicationTransfer.singleton_3206 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3207_2 : Law3207.Subspectral Law1685 := (show Law3207.Subspectral Law2 from (ImplicationTransfer.singleton_3207 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3208_2 : Law3208.Subspectral Law1685 := (show Law3208.Subspectral Law2 from (ImplicationTransfer.singleton_3208 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3209_2 : Law3209.Subspectral Law1685 := (show Law3209.Subspectral Law2 from (ImplicationTransfer.singleton_3209 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3212_2 : Law3212.Subspectral Law1685 := (show Law3212.Subspectral Law2 from (ImplicationTransfer.singleton_3212 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3213_2 : Law3213.Subspectral Law1685 := (show Law3213.Subspectral Law2 from (ImplicationTransfer.singleton_3213 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3215_2 : Law3215.Subspectral Law1685 := (show Law3215.Subspectral Law2 from (ImplicationTransfer.singleton_3215 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3216_2 : Law3216.Subspectral Law1685 := (show Law3216.Subspectral Law2 from (ImplicationTransfer.singleton_3216 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3217_2 : Law3217.Subspectral Law1685 := (show Law3217.Subspectral Law2 from (ImplicationTransfer.singleton_3217 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3219_2 : Law3219.Subspectral Law1685 := (show Law3219.Subspectral Law2 from (ImplicationTransfer.singleton_3219 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3220_2 : Law3220.Subspectral Law1685 := (show Law3220.Subspectral Law2 from (ImplicationTransfer.singleton_3220 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3221_2 : Law3221.Subspectral Law1685 := (show Law3221.Subspectral Law2 from (ImplicationTransfer.singleton_3221 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3223_2 : Law3223.Subspectral Law1685 := (show Law3223.Subspectral Law2 from (ImplicationTransfer.singleton_3223 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3224_2 : Law3224.Subspectral Law1685 := (show Law3224.Subspectral Law2 from (ImplicationTransfer.singleton_3224 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3225_2 : Law3225.Subspectral Law1685 := (show Law3225.Subspectral Law2 from (ImplicationTransfer.singleton_3225 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3226_2 : Law3226.Subspectral Law1685 := (show Law3226.Subspectral Law2 from (ImplicationTransfer.singleton_3226 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3228_2 : Law3228.Subspectral Law1685 := (show Law3228.Subspectral Law2 from (ImplicationTransfer.singleton_3228 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3229_2 : Law3229.Subspectral Law1685 := (show Law3229.Subspectral Law2 from (ImplicationTransfer.singleton_3229 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3230_2 : Law3230.Subspectral Law1685 := (show Law3230.Subspectral Law2 from (ImplicationTransfer.singleton_3230 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3231_2 : Law3231.Subspectral Law1685 := (show Law3231.Subspectral Law2 from (ImplicationTransfer.singleton_3231 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3233_2 : Law3233.Subspectral Law1685 := (show Law3233.Subspectral Law2 from (ImplicationTransfer.singleton_3233 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3234_2 : Law3234.Subspectral Law1685 := (show Law3234.Subspectral Law2 from (ImplicationTransfer.singleton_3234 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3235_2 : Law3235.Subspectral Law1685 := (show Law3235.Subspectral Law2 from (ImplicationTransfer.singleton_3235 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3236_2 : Law3236.Subspectral Law1685 := (show Law3236.Subspectral Law2 from (ImplicationTransfer.singleton_3236 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3238_2 : Law3238.Subspectral Law1685 := (show Law3238.Subspectral Law2 from (ImplicationTransfer.singleton_3238 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3239_2 : Law3239.Subspectral Law1685 := (show Law3239.Subspectral Law2 from (ImplicationTransfer.singleton_3239 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3240_2 : Law3240.Subspectral Law1685 := (show Law3240.Subspectral Law2 from (ImplicationTransfer.singleton_3240 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3241_2 : Law3241.Subspectral Law1685 := (show Law3241.Subspectral Law2 from (ImplicationTransfer.singleton_3241 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3243_2 : Law3243.Subspectral Law1685 := (show Law3243.Subspectral Law2 from (ImplicationTransfer.singleton_3243 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3244_2 : Law3244.Subspectral Law1685 := (show Law3244.Subspectral Law2 from (ImplicationTransfer.singleton_3244 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3245_2 : Law3245.Subspectral Law1685 := (show Law3245.Subspectral Law2 from (ImplicationTransfer.singleton_3245 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3246_2 : Law3246.Subspectral Law1685 := (show Law3246.Subspectral Law2 from (ImplicationTransfer.singleton_3246 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3248_2 : Law3248.Subspectral Law1685 := (show Law3248.Subspectral Law2 from (ImplicationTransfer.singleton_3248 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3249_2 : Law3249.Subspectral Law1685 := (show Law3249.Subspectral Law2 from (ImplicationTransfer.singleton_3249 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3250_2 : Law3250.Subspectral Law1685 := (show Law3250.Subspectral Law2 from (ImplicationTransfer.singleton_3250 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3251_2 : Law3251.Subspectral Law1685 := (show Law3251.Subspectral Law2 from (ImplicationTransfer.singleton_3251 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

theorem route_3252_2 : Law3252.Subspectral Law1685 := (show Law3252.Subspectral Law2 from (ImplicationTransfer.singleton_3252 |>.trans spectrum_two.symm).subset).trans basis_route_2_2

end Spectrum.NegativeTransfer

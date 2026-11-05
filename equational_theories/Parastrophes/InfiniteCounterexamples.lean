import equational_theories.ManuallyProved.Equation73
import equational_theories.Generated.Greedy.Eq707
import equational_theories.Generated.Greedy.Eq883
import equational_theories.Generated.Greedy.Eq1113
import equational_theories.Generated.VampireProven.Proofs1
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx
import equational_theories.Confluence1
import equational_theories.Confluence2
import equational_theories.Confluence3
import equational_theories.Generated.MagmaEgg.small._006
import equational_theories.Generated.MagmaEgg.small._004
import equational_theories.Parastrophes.Attributes
import equational_theories.Definability.E63Family
import equational_theories.ManuallyProved.Equation63
import equational_theories.ManuallyProved.Equation1516
import equational_theories.Generated.Greedy.Eq118

/-! Existing infinite countermodels distinguish finite quasigroup statements
from unrestricted ones. No finite counterexample is asserted here. -/
namespace Parastrophes.Catalogue

/-- A quasigroup satisfying E63 satisfies E1692, contradicting the existing model. -/
@[parastrophe_result] theorem not_leftQuasigroup63_all : ¬ SideQuasigroupLaw .all Law63 .left := by
  intro h
  obtain ⟨G, M, h63, hn⟩ := Eq63.Equation63_not_implies_Equation1692
  letI : Magma G := M
  have hQ := h G M trivial ((@Law63.models_iff G M).mpr h63)
  exact hn ((E63Family.equation1692_iff_left_injective h63).mpr (fun y => (hQ y).1))

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup63_all : ¬ QuasigroupLaw .all Law63 :=
  fun h => not_leftQuasigroup63_all (quasigroup_side h .left)

/-- The existing E118 countermodel lacks a surjective right translation. -/
@[parastrophe_result] theorem not_rightQuasigroup118_all : ¬ SideQuasigroupLaw .all Law118 .right := by
  intro h
  obtain ⟨G, M, h118, hn⟩ := Equation118_not_implies_Equation222
  letI : Magma G := M
  have hQ := h G M trivial ((@Law118.models_iff G M).mpr h118)
  exact hn ((E63Family.equation222_iff_right_surjective h118).mpr (fun y => (hQ y).2))

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup118_all : ¬ QuasigroupLaw .all Law118 :=
  fun h => not_rightQuasigroup118_all (quasigroup_side h .right)

/-- In E118, `L_y R_y² = 1`. Injective left translations would make `R_y²`
onto, and hence make E222 hold. The same saved model therefore refutes left
bijectivity as well as right bijectivity. -/
@[parastrophe_result] theorem not_leftQuasigroup118_all : ¬ SideQuasigroupLaw .all Law118 .left := by
  intro h
  obtain ⟨G, M, h118, hn⟩ := Equation118_not_implies_Equation222
  letI : Magma G := M
  have hQ := h G M trivial ((@Law118.models_iff G M).mpr h118)
  apply hn
  apply (E63Family.equation222_iff_right_surjective h118).mpr
  intro y x
  have he := (hQ y).1 (h118 (M.op y x) y)
  exact ⟨M.op (M.op y x) y, he.symm⟩

/-- The existing infinite E1516 model fails right cancellation. -/
@[parastrophe_result] theorem not_rightQuasigroup1516_all : ¬ SideQuasigroupLaw .all Law1516 .right := by
  intro h
  obtain ⟨G, M, h1516, hn⟩ := Equation1516_not_implies_cancelRight
  have hQ := h G M trivial ((@Law1516.models_iff G M).mpr h1516)
  exact hn (fun a b c he => (hQ c).1 he)

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup1516_all : ¬ QuasigroupLaw .all Law1516 :=
  fun h => not_rightQuasigroup1516_all (quasigroup_side h .right)

/-- E115's known normal-form model fails the cyclic rotation forced by row cancellation. -/
@[parastrophe_result] theorem not_leftQuasigroup115_all : ¬ SideQuasigroupLaw .all Law115 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw115.Facts
  letI : Magma G := M
  have hE : Equation115 G := hf.1
  have hn : ¬ Equation2707 G := by tauto
  have hQ := h G M trivial ((@Law115.models_iff G M).mpr hE)
  apply hn
  intro x y
  exact (hQ y).1 (hE (M.op y x) y)

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup115_all : ¬ QuasigroupLaw .all Law115 :=
  fun h => not_leftQuasigroup115_all (quasigroup_side h .left)

/-- E477's established countermodel cannot have all its rows injective. -/
@[parastrophe_result] theorem not_leftQuasigroup477_all : ¬ SideQuasigroupLaw .all Law477 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw477.Facts
  letI : Magma G := M
  have hE : Equation477 G := hf.1
  have hn : ¬ Equation3150 G := by tauto
  have hQ := h G M trivial ((@Law477.models_iff G M).mpr hE)
  have hr : Equation1492 G := fun x y => (hQ y).1 (hE (M.op y x) y)
  exact hn (Equation2135_implies_Equation3150 G (Equation1492_implies_Equation2135 G hr))

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup477_all : ¬ QuasigroupLaw .all Law477 :=
  fun h => not_leftQuasigroup477_all (quasigroup_side h .left)

/-- The same missing cyclic rotation refutes quasigroupness for E680. -/
@[parastrophe_result] theorem not_leftQuasigroup680_all : ¬ SideQuasigroupLaw .all Law680 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw680.Facts
  letI : Magma G := M
  have hE : Equation680 G := hf.1
  have hn : ¬ Equation1695 G := by tauto
  have hQ := h G M trivial ((@Law680.models_iff G M).mpr hE)
  exact hn (fun x y => (hQ y).1 (hE (M.op y x) y))

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup680_all : ¬ QuasigroupLaw .all Law680 :=
  fun h => not_leftQuasigroup680_all (quasigroup_side h .left)

/-- The E481 normal-form model also separates finite and arbitrary quasigroupness. -/
@[parastrophe_result] theorem not_leftQuasigroup481_all : ¬ SideQuasigroupLaw .all Law481 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw481.Facts
  letI : Magma G := M
  have hE : Equation481 G := hf.1
  have hn : ¬ Equation1496 G := by tauto
  have hQ := h G M trivial ((@Law481.models_iff G M).mpr hE)
  exact hn (fun x y z => (hQ y).1 (hE (M.op y x) y z))

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup481_all : ¬ QuasigroupLaw .all Law481 :=
  fun h => not_leftQuasigroup481_all (quasigroup_side h .left)

/-- The existing E73 countermodel fails E203, which follows from E125.
Quasigroupness would supply the missing E73-to-E125 cyclic rotation. -/
@[parastrophe_result] theorem not_leftQuasigroup73_all : ¬ SideQuasigroupLaw .all Law73 .left := by
  intro h
  obtain ⟨G, M, h73, hn⟩ := Eq73.not_203
  letI : Magma G := M
  have hQ := h G M trivial ((@Law73.models_iff G M).mpr h73)
  have h125 := (E63Family.equation125_iff_left_injective h73).mpr (fun y => (hQ y).1)
  exact hn (SimpleRewrites.Equation229_implies_Equation203 G (Equation125_implies_Equation229 G h125))

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup73_all : ¬ QuasigroupLaw .all Law73 :=
  fun h => not_leftQuasigroup73_all (quasigroup_side h .left)

/-- The existing E707 countermodel fails the E1316 rotation forced by a quasigroup. -/
@[parastrophe_result] theorem not_leftQuasigroup707_all : ¬ SideQuasigroupLaw .all Law707 .left := by
  intro h
  obtain ⟨G, M, hE, hn⟩ := Equation707_not_implies_Equation1316
  letI : Magma G := M
  have hQ := h G M trivial ((@Law707.models_iff G M).mpr hE)
  exact hn (fun x y => (hQ y).1 (hE (M.op y x) y))

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup707_all : ¬ QuasigroupLaw .all Law707 :=
  fun h => not_leftQuasigroup707_all (quasigroup_side h .left)

/-- The existing E883 countermodel fails the E2101 rotation forced by a quasigroup. -/
@[parastrophe_result] theorem not_leftQuasigroup883_all : ¬ SideQuasigroupLaw .all Law883 .left := by
  intro h
  obtain ⟨G, M, hE, hn⟩ := Equation883_not_implies_Equation2101
  letI : Magma G := M
  have hQ := h G M trivial ((@Law883.models_iff G M).mpr hE)
  exact hn (fun x y => (hQ y).1 (hE (M.op y x) y))

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup883_all : ¬ QuasigroupLaw .all Law883 :=
  fun h => not_leftQuasigroup883_all (quasigroup_side h .left)

/-- The existing E1113 countermodel fails the E2534 rotation forced by a quasigroup. -/
@[parastrophe_result] theorem not_leftQuasigroup1113_all : ¬ SideQuasigroupLaw .all Law1113 .left := by
  intro h
  obtain ⟨G, M, hE, hn⟩ := Equation1113_not_implies_Equation2534
  letI : Magma G := M
  have hQ := h G M trivial ((@Law1113.models_iff G M).mpr hE)
  exact hn (fun x y => (hQ y).1 (hE (M.op y x) y))

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup1113_all : ¬ QuasigroupLaw .all Law1113 :=
  fun h => not_leftQuasigroup1113_all (quasigroup_side h .left)

/-- The existing E1086 countermodel fails the E2710 rotation forced by a quasigroup. -/
@[parastrophe_result] theorem not_leftQuasigroup1086_all : ¬ SideQuasigroupLaw .all Law1086 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw1086.Facts
  have hE : @Equation1086 G M := hf.1
  have hn : ¬ @Equation2710 G M := by tauto
  letI : Magma G := M
  have hQ := h G M trivial ((@Law1086.models_iff G M).mpr hE)
  exact hn (fun x y => (hQ y).1 (hE (M.op y x) y))

/-- The one-sided obstruction also refutes the two-sided assertion. -/
@[parastrophe_result] theorem not_quasigroup1086_all : ¬ QuasigroupLaw .all Law1086 :=
  fun h => not_leftQuasigroup1086_all (quasigroup_side h .left)

end Parastrophes.Catalogue

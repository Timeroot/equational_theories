import equational_theories.Confluence1
import equational_theories.Confluence2
import equational_theories.Confluence3
import equational_theories.Generated.Greedy.Eq124
import equational_theories.Generated.Greedy.Eq511
import equational_theories.Generated.Greedy.Eq707
import equational_theories.Generated.Greedy.Eq883
import equational_theories.ManuallyProved.Equation1076
import equational_theories.ManuallyProved.Equation1289
import equational_theories.ManuallyProved.Equation1323
import equational_theories.ManuallyProved.Equation1516
import equational_theories.ManuallyProved.Equation1526
import equational_theories.ManuallyProved.Equation1648
import equational_theories.ManuallyProved.Equation1692
import equational_theories.ManuallyProved.Equation1722
import equational_theories.ManuallyProved.Equation1729
import equational_theories.ManuallyProved.Equation63
import equational_theories.ManuallyProved.Equation73
import equational_theories.ManuallyProved.Equation917
import equational_theories.Parastrophes.Attributes
import equational_theories.Superposition

/-! Bijectivity would force an extra identity in each of these established
infinite countermodels. These small equational derivations are replayed in Lean;
no ATP certificate or new infinite model is trusted. -/
namespace Parastrophes.Catalogue

private theorem leftBijective219_forces880 {G : Type} (M : Magma G)
    (h : @Equation219 G M) (hQ : IsSideQuasigroup .left M) : @Equation880 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 (M.op X0 X0)) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : sK0 ≠ (M.op sK1 (M.op (M.op sK0 sK1) (M.op sK0 sK1))) := mod_symm hn
  have e13 (X0 X1 : G) : (D.op (M.op X1 (M.op X0 X0)) X0) = X1 := superpose e8 e10
  have e14 (X0 X1 : G) : (D.op X0 X1) = (M.op (M.op X1 X1) (M.op X0 X0)) := superpose e8 e13
  have e25 (X0 X1 : G) : (M.op X1 X1) = (D.op (D.op X0 X1) X0) := superpose e14 e13
  have e35 (X0 X1 : G) : (D.op X0 X1) = (M.op (M.op X1 X0) (M.op X1 X0)) := superpose e10 e25
  have e207 : sK0 ≠ (M.op sK1 (D.op sK1 sK0)) := superpose e35 e11
  subsumption e207 e9

/-- Left bijectivity in E219 would imply E880, contradicted by
`rw115.Facts`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup219_all_countermodel :
    ¬ SideQuasigroupLaw .all Law219 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw115.Facts
  have hE : @Equation219 G (opposite M) := hf.1
  have hn : ¬ @Equation2707 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law219.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective219_forces880 (opposite M) hE hQ)

private theorem leftBijective271_forces1895 {G : Type} (M : Magma G)
    (h : @Equation271 G M) (hQ : IsSideQuasigroup .left M) : @Equation1895 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op (M.op X1 X0) X0) X1) = X0 := mod_symm (h ..)
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : sK0 ≠ (M.op (M.op sK1 (M.op sK0 sK1)) (M.op sK0 sK1)) := mod_symm hn
  have e15 (X0 X1 : G) : (D.op (M.op (M.op X1 X0) X0) X0) = X1 := superpose e8 e10
  have e20 (X0 X1 : G) : (M.op (M.op X1 X0) X0) = (D.op (M.op X0 X1) X1) := superpose e8 e15
  have e79 : sK0 ≠ (D.op (M.op (M.op sK0 sK1) sK1) sK1) := superpose e20 e11
  subsumption e79 e15

/-- Left bijectivity in E271 would imply E1895, contradicted by
`Eq63.Equation63_not_implies_Equation1692`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup271_all_countermodel :
    ¬ SideQuasigroupLaw .all Law271 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Eq63.Equation63_not_implies_Equation1692
  have hE : @Equation271 G (opposite M) := hf.1
  have hn : ¬ @Equation1692 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law271.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective271_forces1895 (opposite M) hE hQ)

private theorem leftBijective1895_forces8 {G : Type} (M : Magma G)
    (h : @Equation1895 G M) (hQ : IsSideQuasigroup .left M) : @Equation8 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 (M.op X0 X1)) (M.op X0 X1)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op sK0 (M.op sK0 sK0)) := mod_symm hn
  have e12 (X0 X1 : G) : (M.op (M.op (D.op X1 X0) X0) X0) = X1 := superpose e9 e8
  have e13 (X0 X1 : G) : (M.op X1 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X0) X0) := superpose e8 e8
  have e16 (X0 X1 : G) : (M.op (D.op X0 X1) X1) = (M.op (M.op X1 X0) X0) := superpose e12 e8
  have e50 (X0 X1 : G) : (M.op (M.op (M.op X0 X1) X1) X0) = X1 := superpose e16 e12
  have e135 (X0 : G) : (M.op X0 (M.op X0 X0)) = X0 := superpose e50 e13
  have e196 : sK0 ≠ sK0 := superpose e135 e11
  subsumption e196 rfl

/-- Left bijectivity in E1895 would imply E8, contradicted by
`Equation1692_not_implies_Equation23`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup1895_all_countermodel :
    ¬ SideQuasigroupLaw .all Law1895 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Equation1692_not_implies_Equation23
  have hE : @Equation1895 G (opposite M) := hf.1
  have hn : ¬ @Equation23 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law1895.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective1895_forces8 (opposite M) hE hQ)

private theorem leftBijective1898_forces2644 {G : Type} (M : Magma G)
    (h : @Equation1898 G M) (hQ : IsSideQuasigroup .left M) : @Equation2644 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 (M.op X0 X1)) (M.op X1 X1)) = X0 := mod_symm (h ..)
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : sK0 ≠ (M.op (M.op (M.op sK0 sK0) (M.op sK0 sK0)) sK0) := mod_symm hn
  have e13 (X0 X1 : G) : (M.op X1 (M.op X0 X1)) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) (M.op X1 X1))) := superpose e8 e8
  have e35 (X0 X1 : G) : (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X0)) = X1 := superpose e13 e8
  have e49 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := superpose e35 e10
  have e88 : sK0 ≠ (D.op sK0 (M.op sK0 sK0)) := superpose e49 e11
  subsumption e88 e10

/-- Left bijectivity in E1898 would imply E2644, contradicted by
`Eq1729.not_817`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup1898_all_countermodel :
    ¬ SideQuasigroupLaw .all Law1898 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Eq1729.not_817
  have hE : @Equation1898 G (opposite M) := hf.1
  have hn : ¬ @Equation817 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law1898.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective1898_forces2644 (opposite M) hE hQ)

private theorem leftBijective2291_forces4588 {G : Type} (M : Magma G)
    (h : @Equation2291 G M) (hQ : IsSideQuasigroup .left M) : @Equation4588 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X1) = X0 := mod_symm (h ..)
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : (M.op (M.op sK0 sK0) sK0) ≠ (M.op (M.op sK1 sK0) sK1) := mod_symm hn
  have e13 (X0 X1 : G) : (D.op (M.op X1 (M.op X0 (M.op X0 X0))) X0) = X1 := superpose e8 e10
  have e14 (X0 X1 : G) : (D.op X0 X1) = (M.op (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0))) := superpose e8 e13
  have e20 (X0 X1 : G) : (M.op X1 (M.op X1 X1)) = (D.op (D.op X0 X1) X0) := superpose e14 e13
  have e31 (X0 X1 X2 : G) : (M.op (M.op X2 (D.op (D.op X0 X1) X0)) X2) = X1 := superpose e20 e8
  have e119 (X0 X1 X2 : G) : (M.op X2 X0) = (M.op (M.op X1 (D.op X0 X2)) X1) := superpose e10 e31
  have e404 (X0 X1 X2 : G) : (M.op (M.op X1 X0) X1) = (M.op (M.op X2 X0) X2) := superpose e10 e119
  have e823 (X0 : G) : (M.op (M.op sK0 sK0) sK0) ≠ (M.op (M.op X0 sK0) X0) := superpose e404 e11
  subsumption e823 e404

/-- Left bijectivity in E2291 would imply E4588, contradicted by
`rw1276.Facts`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup2291_all_countermodel :
    ¬ SideQuasigroupLaw .all Law2291 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw1276.Facts
  have hE : @Equation2291 G (opposite M) := hf.1
  have hn : ¬ @Equation4273 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law2291.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective2291_forces4588 (opposite M) hE hQ)

private theorem leftBijective2304_forces883 {G : Type} (M : Magma G)
    (h : @Equation2304 G M) (hQ : IsSideQuasigroup .left M) : @Equation883 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 (M.op X0 (M.op X1 X1))) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op sK1 (M.op (M.op sK0 sK1) (M.op sK1 sK1))) := mod_symm hn
  have e12 (X0 X1 : G) : (M.op (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) = (M.op (M.op X1 X0) X1) := superpose e8 e8
  have e20 (X0 X1 : G) : (M.op (M.op (M.op X0 X1) X0) (M.op X0 X0)) = X1 := superpose e12 e8
  have e33 (X0 X1 : G) : (M.op (M.op X0 X1) (M.op X1 X1)) = (D.op X1 X0) := superpose e9 e20
  have e87 : sK0 ≠ (M.op sK1 (D.op sK1 sK0)) := superpose e33 e11
  subsumption e87 e9

/-- Left bijectivity in E2304 would imply E883, contradicted by
`Eq1323.Equation1323_not_implies_Equation2744`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup2304_all_countermodel :
    ¬ SideQuasigroupLaw .all Law2304 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Eq1323.Equation1323_not_implies_Equation2744
  have hE : @Equation2304 G (opposite M) := hf.1
  have hn : ¬ @Equation2744 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law2304.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective2304_forces883 (opposite M) hE hQ)

private theorem leftBijective2531_forces3 {G : Type} (M : Magma G)
    (h : @Equation2531 G M) (hQ : IsSideQuasigroup .left M) : @Equation3 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 (M.op (M.op X1 X0) X0)) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op sK0 sK0) := mod_symm hn
  have e12 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op X1 (M.op X0 (D.op X1 X0))) X1) := superpose e9 e8
  have e20 (X0 : G) : (D.op X0 X0) = (M.op (M.op X0 X0) X0) := superpose e9 e12
  have e25 (X0 : G) : (M.op (M.op X0 (D.op X0 X0)) X0) = X0 := superpose e20 e8
  have e29 (X0 : G) : (M.op X0 X0) = X0 := superpose e9 e25
  have e57 : sK0 ≠ sK0 := superpose e29 e11
  subsumption e57 rfl

/-- Left bijectivity in E2531 would imply E3, contradicted by
`Eq1076.refute_seed1`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup2531_all_countermodel :
    ¬ SideQuasigroupLaw .all Law2531 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Eq1076.refute_seed1
  have hE : @Equation2531 G (opposite M) := hf.1
  have hn : ¬ @Equation3 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law2531.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective2531_forces3 (opposite M) hE hQ)

private theorem leftBijective124_forces1924 {G : Type} (M : Magma G)
    (h : @Equation124 G M) (hQ : IsSideQuasigroup .left M) : @Equation1924 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op X1 (M.op (M.op X1 X0) X0)) = X0 := mod_symm (h ..)
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : sK0 ≠ (M.op (M.op sK1 (M.op sK1 sK0)) (M.op sK1 sK0)) := mod_symm hn
  have e14 (X0 X1 : G) : (M.op (M.op X1 X0) X0) = (D.op X1 X0) := superpose e8 e10
  have e19 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) := superpose e14 e11
  subsumption e19 e10

/-- Left bijectivity in E124 would imply E1924, contradicted by
`Equation124_not_implies_Equation1924`. -/
@[parastrophe_result] theorem not_leftQuasigroup124_all_countermodel :
    ¬ SideQuasigroupLaw .all Law124 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Equation124_not_implies_Equation1924
  have hE : @Equation124 G M := hf.1
  have hn : ¬ @Equation1924 G M := by tauto
  have hQ := h G M trivial ((@Law124.models_iff G M).mpr hE)
  exact hn (leftBijective124_forces1924 M hE hQ)

private theorem leftBijective274_forces203 {G : Type} (M : Magma G)
    (h : @Equation274 G M) (hQ : IsSideQuasigroup .left M) : @Equation203 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op (M.op X1 X0) X1) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op (M.op sK0 (M.op sK0 sK0)) sK0) := mod_symm hn
  have e12 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op X0 X1) X1) := superpose e9 e8
  have e19 (X0 : G) : (M.op (D.op X0 X0) X0) = X0 := superpose e12 e8
  have e32 (X0 : G) : (M.op X0 X0) = (D.op X0 (D.op X0 X0)) := superpose e19 e12
  have e92 (X0 : G) : (M.op X0 (M.op X0 X0)) = (D.op X0 X0) := superpose e32 e9
  have e119 : sK0 ≠ (M.op (D.op sK0 sK0) sK0) := superpose e92 e11
  subsumption e119 e19

/-- Left bijectivity in E274 would imply E203, contradicted by
`Eq73.not_99_4380`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup274_all_countermodel :
    ¬ SideQuasigroupLaw .all Law274 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Eq73.not_99_4380
  have hE : @Equation274 G (opposite M) := hf.1
  have hn : ¬ @Equation99 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law274.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective274_forces203 (opposite M) hE hQ)

private theorem leftBijective1076_forces3 {G : Type} (M : Magma G)
    (h : @Equation1076 G M) (hQ : IsSideQuasigroup .left M) : @Equation3 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : sK0 ≠ (M.op sK0 sK0) := mod_symm hn
  have e12 (X0 X1 : G) : (M.op (D.op X1 X0) (M.op (M.op X1 X0) (D.op X1 X0))) = X1 := superpose e9 e8
  have e14 (X0 X1 : G) : (M.op (M.op X0 (M.op X0 X1)) X1) = (D.op X1 X0) := superpose e8 e10
  have e21 (X0 X1 : G) : (D.op (M.op X1 (M.op X1 X0)) (D.op X0 X1)) = X0 := superpose e14 e10
  have e25 (X0 X1 : G) : (M.op X1 (M.op X1 X0)) = (M.op (D.op (M.op X1 (M.op X1 X0)) X0) (M.op (D.op X0 X1) (D.op (M.op X1 (M.op X1 X0)) X0))) := superpose e14 e12
  have e39 (X0 X1 : G) : (D.op (M.op (M.op X1 X0) (M.op (M.op X1 X0) X1)) X0) = X1 := superpose e10 e21
  have e234 (X0 : G) : (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0)) = (M.op X0 (M.op (D.op X0 (M.op X0 X0)) X0)) := superpose e39 e25
  have e247 (X0 : G) : (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0)) := superpose e10 e234
  have e372 (X0 : G) : (M.op X0 X0) = (M.op X0 (M.op (M.op X0 (M.op X0 X0)) X0)) := superpose e247 e8
  have e404 (X0 : G) : (M.op X0 X0) = X0 := superpose e8 e372
  have e499 : sK0 ≠ sK0 := superpose e404 e11
  subsumption e499 rfl

/-- Left bijectivity in E1076 would imply E3, contradicted by
`Eq1076.refute_seed1`. -/
@[parastrophe_result] theorem not_leftQuasigroup1076_all_countermodel :
    ¬ SideQuasigroupLaw .all Law1076 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Eq1076.refute_seed1
  have hE : @Equation1076 G M := hf.1
  have hn : ¬ @Equation3 G M := by tauto
  have hQ := h G M trivial ((@Law1076.models_iff G M).mpr hE)
  exact hn (leftBijective1076_forces3 M hE hQ)

private theorem leftBijective1110_forces8 {G : Type} (M : Magma G)
    (h : @Equation1110 G M) (hQ : IsSideQuasigroup .left M) : @Equation8 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op X1 (M.op (M.op X1 (M.op X0 X0)) X1)) = X0 := mod_symm (h ..)
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : sK0 ≠ (M.op sK0 (M.op sK0 sK0)) := mod_symm hn
  have e12 (X0 X1 : G) : (M.op (M.op X1 (M.op X0 X0)) X1) = (D.op X1 X0) := superpose e8 e10
  have e15 (X0 X1 : G) : (D.op (M.op X0 (M.op X1 X1)) (D.op X0 X1)) = X0 := superpose e12 e10
  have e17 (X0 X1 : G) : (M.op (M.op X0 X0) (M.op X1 X1)) = (D.op (D.op (M.op X0 X0) X1) (D.op (M.op (M.op X0 X0) (M.op X1 X1)) X0)) := superpose e12 e15
  have e18 (X0 X1 : G) : (D.op (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) X0) = X1 := superpose e10 e15
  have e58 (X0 : G) : (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) = (D.op (D.op (M.op X0 X0) (M.op (M.op X0 X0) X0)) (M.op X0 X0)) := superpose e18 e17
  have e62 (X0 : G) : (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) = (D.op X0 (M.op X0 X0)) := superpose e10 e58
  have e65 (X0 : G) : (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) = X0 := superpose e10 e62
  have e78 (X0 : G) : (M.op X0 (M.op X0 X0)) = (D.op (M.op X0 X0) (M.op (M.op X0 X0) X0)) := superpose e65 e12
  have e83 (X0 : G) : (M.op X0 (M.op X0 X0)) = X0 := superpose e10 e78
  have e120 : sK0 ≠ sK0 := superpose e83 e11
  subsumption e120 rfl

/-- Left bijectivity in E1110 would imply E8, contradicted by
`rw1110.Facts`. -/
@[parastrophe_result] theorem not_leftQuasigroup1110_all_countermodel :
    ¬ SideQuasigroupLaw .all Law1110 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw1110.Facts
  have hE : @Equation1110 G M := hf.1
  have hn : ¬ @Equation8 G M := by tauto
  have hQ := h G M trivial ((@Law1110.models_iff G M).mpr hE)
  exact hn (leftBijective1110_forces8 M hE hQ)

private theorem leftBijective1276_forces4273 {G : Type} (M : Magma G)
    (h : @Equation1276 G M) (hQ : IsSideQuasigroup .left M) : @Equation4273 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op X1 (M.op (M.op (M.op X0 X0) X0) X1)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : (M.op sK0 (M.op sK0 sK0)) ≠ (M.op sK1 (M.op sK0 sK1)) := mod_symm hn
  have e12 (X0 X1 : G) : (M.op (D.op (M.op (M.op X1 X1) X1) X0) X0) = X1 := superpose e9 e8
  have e14 (X0 X1 : G) : (M.op (M.op (M.op X0 X0) X0) X1) = (D.op X1 X0) := superpose e8 e10
  have e24 (X0 X1 : G) : (D.op (M.op (M.op X1 X1) X1) (D.op X0 X1)) = X0 := superpose e14 e10
  have e33 (X0 X1 : G) : (D.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)) X0) = X1 := superpose e10 e24
  have e42 (X0 X1 : G) : (D.op (M.op (M.op X1 X1) X1) X0) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) := superpose e33 e24
  have e124 (X0 X1 X2 : G) : (M.op X1 X0) = (M.op (D.op (D.op (M.op (M.op X0 X0) X0) X1) X2) X2) := superpose e42 e12
  have e163 (X0 X1 X2 : G) : (M.op X1 (M.op X0 X1)) = (M.op (D.op X0 X2) X2) := superpose e33 e124
  have e334 (X0 X1 X2 : G) : (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := superpose e163 e163
  have e649 (X0 : G) : (M.op sK0 (M.op sK0 sK0)) ≠ (M.op X0 (M.op sK0 X0)) := superpose e334 e11
  subsumption e649 e334

/-- Left bijectivity in E1276 would imply E4273, contradicted by
`rw1276.Facts`. -/
@[parastrophe_result] theorem not_leftQuasigroup1276_all_countermodel :
    ¬ SideQuasigroupLaw .all Law1276 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw1276.Facts
  have hE : @Equation1276 G M := hf.1
  have hn : ¬ @Equation4273 G M := by tauto
  have hQ := h G M trivial ((@Law1276.models_iff G M).mpr hE)
  exact hn (leftBijective1276_forces4273 M hE hQ)

private theorem leftBijective1516_forces255 {G : Type} (M : Magma G)
    (h : @Equation1516 G M) (hQ : IsSideQuasigroup .left M) : @Equation255 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op (M.op (M.op sK0 sK0) sK0) sK0) := mod_symm hn
  have e12 (X0 X1 : G) : (M.op (M.op (D.op X1 X0) (D.op X1 X0)) (M.op X1 X0)) = X1 := superpose e9 e8
  have e23 (X0 X1 : G) : (M.op (M.op (D.op X1 (D.op X1 X0)) (D.op X1 (D.op X1 X0))) X0) = X1 := superpose e9 e12
  have e28 (X0 X1 : G) : (M.op (D.op X0 X1) (D.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (D.op X0 X1) (D.op X0 X1)) X0)) := superpose e12 e8
  have e523 (X0 : G) : (M.op (D.op X0 (D.op X0 X0)) (D.op X0 (D.op X0 X0))) = (M.op (M.op (M.op X0 (D.op X0 X0)) (M.op X0 (D.op X0 X0))) X0) := superpose e23 e28
  have e543 (X0 : G) : (M.op (M.op X0 X0) X0) = (M.op (D.op X0 (D.op X0 X0)) (D.op X0 (D.op X0 X0))) := superpose e9 e523
  have e570 (X0 : G) : (M.op (M.op (M.op X0 X0) X0) X0) = X0 := superpose e543 e23
  have e728 : sK0 ≠ sK0 := superpose e570 e11
  subsumption e728 rfl

/-- Left bijectivity in E1516 would imply E255, contradicted by
`Equation1516_not_implies_Equation255`. -/
@[parastrophe_result] theorem not_leftQuasigroup1516_all_countermodel :
    ¬ SideQuasigroupLaw .all Law1516 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Equation1516_not_implies_Equation255
  have hE : @Equation1516 G M := hf.1
  have hn : ¬ @Equation255 G M := by tauto
  have hQ := h G M trivial ((@Law1516.models_iff G M).mpr hE)
  exact hn (leftBijective1516_forces255 M hE hQ)

private theorem leftBijective1924_forces99 {G : Type} (M : Magma G)
    (h : @Equation1924 G M) (hQ : IsSideQuasigroup .left M) : @Equation99 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 (M.op X1 X0)) (M.op X1 X0)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op sK0 (M.op (M.op sK0 sK0) sK0)) := mod_symm hn
  have e12 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op X1 X0) X0) := superpose e9 e8
  have e22 : sK0 ≠ (M.op sK0 (D.op sK0 sK0)) := superpose e12 e11
  subsumption e22 e9

/-- Left bijectivity in E1924 would imply E99, contradicted by
`Equation1648_facts`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup1924_all_countermodel :
    ¬ SideQuasigroupLaw .all Law1924 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Equation1648_facts
  have hE : @Equation1924 G (opposite M) := hf.1
  have hn : ¬ @Equation203 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law1924.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective1924_forces99 (opposite M) hE hQ)

private theorem leftBijective1925_forces817 {G : Type} (M : Magma G)
    (h : @Equation1925 G M) (hQ : IsSideQuasigroup .left M) : @Equation817 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 (M.op X1 X0)) (M.op X1 X1)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op sK0 (M.op (M.op sK0 sK0) (M.op sK0 sK0))) := mod_symm hn
  have e12 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X1)) := superpose e9 e8
  have e20 : sK0 ≠ (M.op sK0 (D.op sK0 sK0)) := superpose e12 e11
  subsumption e20 e9

/-- Left bijectivity in E1925 would imply E817, contradicted by
`Eq1722.not_1832_2644_3050`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup1925_all_countermodel :
    ¬ SideQuasigroupLaw .all Law1925 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Eq1722.not_1832_2644_3050
  have hE : @Equation1925 G (opposite M) := hf.1
  have hn : ¬ @Equation2644 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law1925.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective1925_forces817 (opposite M) hE hQ)

private theorem leftBijective2101_forces2238 {G : Type} (M : Magma G)
    (h : @Equation2101 G M) (hQ : IsSideQuasigroup .left M) : @Equation2238 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op (M.op X1 X0) X1) (M.op X1 X1)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : sK0 ≠ (M.op (M.op sK0 (M.op sK0 (M.op sK0 sK0))) sK0) := mod_symm hn
  have e12 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op X0 X1) (M.op X1 X1)) := superpose e9 e8
  have e18 (X0 X1 : G) : (D.op (M.op X0 X0) (M.op X1 X0)) = (M.op (D.op X0 X1) (M.op (M.op X0 X0) (M.op X0 X0))) := superpose e12 e12
  have e19 (X0 X1 : G) : (D.op (M.op X0 X0) X1) = (M.op (M.op X1 (M.op X0 X0)) (D.op X0 X0)) := superpose e12 e12
  have e28 (X0 X1 : G) : (D.op (M.op X0 X0) (M.op X1 X0)) = (M.op (D.op X0 X1) (D.op X0 X0)) := superpose e12 e18
  have e170 (X0 X1 : G) : (M.op X1 X0) = (M.op (M.op X0 X0) (M.op (D.op X0 X1) (D.op X0 X0))) := superpose e28 e9
  have e281 (X0 X1 : G) : (M.op (M.op X1 X0) X1) = (M.op (M.op X1 X1) (M.op X0 (D.op X1 X1))) := superpose e10 e170
  have e352 (X0 X1 : G) : (M.op (M.op X0 (M.op X1 (M.op X0 X0))) X0) = (M.op (M.op X0 X0) (D.op (M.op X0 X0) X1)) := superpose e19 e281
  have e380 (X0 X1 : G) : (M.op (M.op X0 (M.op X1 (M.op X0 X0))) X0) = X1 := superpose e9 e352
  have e451 : sK0 ≠ sK0 := superpose e380 e11
  subsumption e451 rfl

/-- Left bijectivity in E2101 would imply E2238, contradicted by
`Eq1526.not_1223`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup2101_all_countermodel :
    ¬ SideQuasigroupLaw .all Law2101 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Eq1526.not_1223
  have hE : @Equation2101 G (opposite M) := hf.1
  have hn : ¬ @Equation1223 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law2101.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective2101_forces2238 (opposite M) hE hQ)

private theorem leftBijective2338_forces511 {G : Type} (M : Magma G)
    (h : @Equation2338 G M) (hQ : IsSideQuasigroup .left M) : @Equation511 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 (M.op X1 (M.op X1 X0))) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op sK1 (M.op sK1 (M.op sK1 (M.op sK0 sK1)))) := mod_symm hn
  have e12 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := superpose e9 e8
  have e15 (X0 X1 : G) : (D.op X1 (D.op X1 X0)) = (M.op (M.op X1 X0) X1) := superpose e9 e12
  have e30 (X0 X1 : G) : (D.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := superpose e15 e9
  have e82 (X0 X1 : G) : (M.op X1 (M.op X0 X1)) = (D.op X1 (D.op X1 X0)) := superpose e9 e30
  have e281 (X0 X1 : G) : (D.op X0 X1) = (M.op X0 (M.op X0 (M.op X1 X0))) := superpose e82 e9
  have e1218 : sK0 ≠ (M.op sK1 (D.op sK1 sK0)) := superpose e281 e11
  subsumption e1218 e9

/-- Left bijectivity in E2338 would imply E511, contradicted by
`Eq1289.not_3116_4435`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup2338_all_countermodel :
    ¬ SideQuasigroupLaw .all Law2338 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Eq1289.not_3116_4435
  have hE : @Equation2338 G (opposite M) := hf.1
  have hn : ¬ @Equation3116 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law2338.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective2338_forces511 (opposite M) hE hQ)

private theorem leftBijective2541_forces817 {G : Type} (M : Magma G)
    (h : @Equation2541 G M) (hQ : IsSideQuasigroup .left M) : @Equation817 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 (M.op (M.op X1 X1) X0)) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op sK0 (M.op (M.op sK0 sK0) (M.op sK0 sK0))) := mod_symm hn
  have e12 (X0 X1 : G) : (D.op (M.op X1 X1) X0) = (M.op (M.op X1 X0) X1) := superpose e9 e8
  have e15 (X0 X1 : G) : (M.op (M.op X0 X0) (M.op (M.op X0 X1) X0)) = X1 := superpose e12 e9
  have e20 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op X1 X1) (M.op X0 X1)) := superpose e9 e15
  have e31 : sK0 ≠ (M.op sK0 (D.op sK0 sK0)) := superpose e20 e11
  subsumption e31 e9

/-- Left bijectivity in E2541 would imply E817, contradicted by
`rw2541.Facts`. -/
@[parastrophe_result] theorem not_leftQuasigroup2541_all_countermodel :
    ¬ SideQuasigroupLaw .all Law2541 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw2541.Facts
  have hE : @Equation2541 G M := hf.1
  have hn : ¬ @Equation817 G M := by tauto
  have hQ := h G M trivial ((@Law2541.models_iff G M).mpr hE)
  exact hn (leftBijective2541_forces817 M hE hQ)

private theorem leftBijective2710_forces1832 {G : Type} (M : Magma G)
    (h : @Equation2710 G M) (hQ : IsSideQuasigroup .left M) : @Equation1832 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op (M.op X1 X0) (M.op X1 X1)) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : sK0 ≠ (M.op (M.op sK0 (M.op sK0 sK0)) (M.op sK0 sK0)) := mod_symm hn
  have e12 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := superpose e9 e8
  have e16 (X0 X1 : G) : (D.op X0 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (D.op (M.op X0 X0) X1) X0) := superpose e12 e12
  have e76 (X0 X1 : G) : (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (D.op (M.op X0 X0) X1) X0)) := superpose e16 e9
  have e139 (X0 X1 : G) : (M.op (M.op X0 (M.op (D.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) X0)) (M.op X0 X0)) = X1 := superpose e76 e8
  have e165 (X0 X1 : G) : (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0)) = X1 := superpose e10 e139
  have e254 : sK0 ≠ sK0 := superpose e165 e11
  subsumption e254 rfl

/-- Left bijectivity in E2710 would imply E1832, contradicted by
`Eq917.not_1629`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup2710_all_countermodel :
    ¬ SideQuasigroupLaw .all Law2710 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Eq917.not_1629
  have hE : @Equation2710 G (opposite M) := hf.1
  have hn : ¬ @Equation1629 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law2710.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective2710_forces1832 (opposite M) hE hQ)

private theorem leftBijective2744_forces1223 {G : Type} (M : Magma G)
    (h : @Equation2744 G M) (hQ : IsSideQuasigroup .left M) : @Equation1223 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op (M.op X1 X1) (M.op X1 X0)) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op sK0 (M.op (M.op (M.op sK0 sK0) sK0) sK0)) := mod_symm hn
  have e12 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op (M.op X1 X1) X0) X1) := superpose e9 e8
  have e22 : sK0 ≠ (M.op sK0 (D.op sK0 sK0)) := superpose e12 e11
  subsumption e22 e9

/-- Left bijectivity in E2744 would imply E1223, contradicted by
`Equation883_not_implies_Equation2238`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup2744_all_countermodel :
    ¬ SideQuasigroupLaw .all Law2744 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Equation883_not_implies_Equation2238
  have hE : @Equation2744 G (opposite M) := hf.1
  have hn : ¬ @Equation2238 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law2744.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective2744_forces1223 (opposite M) hE hQ)

private theorem leftBijective2940_forces2238 {G : Type} (M : Magma G)
    (h : @Equation2940 G M) (hQ : IsSideQuasigroup .left M) : @Equation2238 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op (M.op X1 (M.op X1 X0)) X1) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : sK0 ≠ (M.op (M.op sK0 (M.op sK0 (M.op sK0 sK0))) sK0) := mod_symm hn
  have e12 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op (M.op X1 X0) X1) X1) := superpose e9 e8
  have e15 (X0 X1 : G) : (D.op X1 (D.op X1 X0)) = (M.op (M.op X0 X1) X1) := superpose e9 e12
  have e30 (X0 X1 : G) : (D.op X1 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := superpose e15 e9
  have e84 (X0 X1 : G) : (D.op X0 (M.op (M.op X0 X1) X0)) = (M.op X0 (M.op (D.op X0 X1) X0)) := superpose e12 e30
  have e349 (X0 X1 : G) : (M.op (M.op X0 X1) X0) = (M.op X0 (M.op X0 (M.op (D.op X0 X1) X0))) := superpose e84 e9
  have e432 (X0 X1 : G) : (M.op (M.op X1 (M.op X1 X0)) X1) = (M.op X1 (M.op X1 (M.op X0 X1))) := superpose e10 e349
  have e584 : sK0 ≠ (M.op sK0 (M.op sK0 (M.op (M.op sK0 sK0) sK0))) := superpose e432 e11
  have e631 : sK0 ≠ (M.op sK0 (D.op sK0 sK0)) := superpose e30 e584
  subsumption e631 e9

/-- Left bijectivity in E2940 would imply E2238, contradicted by
`Equation707_not_implies_Equation1223`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup2940_all_countermodel :
    ¬ SideQuasigroupLaw .all Law2940 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Equation707_not_implies_Equation1223
  have hE : @Equation2940 G (opposite M) := hf.1
  have hn : ¬ @Equation1223 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law2940.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective2940_forces2238 (opposite M) hE hQ)

private theorem leftBijective2947_forces614 {G : Type} (M : Magma G)
    (h : @Equation2947 G M) (hQ : IsSideQuasigroup .left M) : @Equation614 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op (M.op X1 (M.op X1 X1)) X0) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op sK0 (M.op sK0 (M.op (M.op sK0 sK0) sK0))) := mod_symm hn
  have e13 (X0 X1 : G) : (M.op X0 X1) = (D.op (M.op X1 (M.op X1 X1)) X0) := superpose e9 e8
  have e16 (X0 X1 : G) : (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X1)) = X0 := superpose e13 e9
  have e24 (X0 X1 : G) : (M.op (M.op (D.op X1 X0) (M.op (D.op X1 X0) (D.op X1 X0))) X0) = X1 := superpose e9 e16
  have e33 (X0 X1 : G) : (M.op (M.op X1 (M.op X1 X1)) X0) = (M.op (D.op X0 X1) (M.op (D.op X0 X1) (D.op X0 X1))) := superpose e24 e16
  have e58 (X0 X1 X2 : G) : (M.op (M.op (M.op X0 (M.op X0 X0)) X1) (M.op X2 (D.op X1 X0))) = X2 := superpose e33 e16
  have e68 (X0 X1 X2 : G) : (M.op X0 (M.op X2 (D.op (M.op X0 X1) X1))) = X2 := superpose e16 e58
  have e184 (X0 X1 : G) : (M.op X0 (M.op X1 (M.op (M.op X0 X0) X0))) = X1 := superpose e13 e68
  have e761 : sK0 ≠ sK0 := superpose e184 e11
  subsumption e761 rfl

/-- Left bijectivity in E2947 would imply E614, contradicted by
`rw680.Facts`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup2947_all_countermodel :
    ¬ SideQuasigroupLaw .all Law2947 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw680.Facts
  have hE : @Equation2947 G (opposite M) := hf.1
  have hn : ¬ @Equation2847 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law2947.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective2947_forces614 (opposite M) hE hQ)

private theorem leftBijective3116_forces2847 {G : Type} (M : Magma G)
    (h : @Equation3116 G M) (hQ : IsSideQuasigroup .left M) : @Equation2847 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op (M.op (M.op X1 X0) X1) X1) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd2 ..
  have e11 : sK0 ≠ (M.op (M.op (M.op sK0 (M.op sK0 sK0)) sK0) sK0) := mod_symm hn
  have e12 (X0 X1 : G) : (D.op X1 X0) = (M.op (M.op (M.op X0 X1) X1) X1) := superpose e9 e8
  have e19 (X0 X1 : G) : (M.op (D.op X0 X1) X0) = (D.op X0 (M.op X1 X0)) := superpose e12 e12
  have e73 (X0 X1 : G) : (M.op X1 X0) = (M.op X0 (M.op (D.op X0 X1) X0)) := superpose e19 e9
  have e187 (X0 X1 : G) : (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 X1)) := superpose e10 e73
  have e319 : sK0 ≠ (M.op (M.op sK0 (M.op (M.op sK0 sK0) sK0)) sK0) := superpose e187 e11
  have e336 : sK0 ≠ (M.op sK0 (M.op (M.op (M.op sK0 sK0) sK0) sK0)) := superpose e187 e319
  have e350 : sK0 ≠ (M.op sK0 (D.op sK0 sK0)) := superpose e12 e336
  subsumption e350 e9

/-- Left bijectivity in E3116 would imply E2847, contradicted by
`Equation511_not_implies_Equation614`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup3116_all_countermodel :
    ¬ SideQuasigroupLaw .all Law3116 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := Equation511_not_implies_Equation614
  have hE : @Equation3116 G (opposite M) := hf.1
  have hn : ¬ @Equation614 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law3116.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective3116_forces2847 (opposite M) hE hQ)

private theorem leftBijective3150_forces411 {G : Type} (M : Magma G)
    (h : @Equation3150 G M) (hQ : IsSideQuasigroup .left M) : @Equation411 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op (M.op (M.op (M.op X1 X1) X1) X0) X1) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op sK0 (M.op sK0 (M.op sK0 (M.op sK0 sK0)))) := mod_symm hn
  have e12 (X0 X1 : G) : (M.op X0 X1) = (D.op (M.op (M.op X1 X1) X1) X0) := superpose e9 e8
  have e15 (X0 X1 : G) : (M.op (M.op (M.op X1 X1) X1) (M.op X0 X1)) = X0 := superpose e12 e9
  have e21 (X0 X1 : G) : (M.op (M.op (M.op (D.op X1 X0) (D.op X1 X0)) (D.op X1 X0)) X0) = X1 := superpose e9 e15
  have e31 (X0 X1 : G) : (M.op (M.op (M.op X1 X1) X1) X0) = (M.op (M.op (D.op X0 X1) (D.op X0 X1)) (D.op X0 X1)) := superpose e21 e15
  have e93 (X0 X1 X2 : G) : (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X2) (D.op X1 X0)) = X2 := superpose e31 e8
  have e109 (X0 X1 X2 : G) : (M.op (M.op X0 X2) (D.op (M.op X0 X1) X1)) = X2 := superpose e15 e93
  have e154 (X0 X1 X2 : G) : (D.op X1 X0) = (M.op X0 (D.op (M.op X1 X2) X2)) := superpose e9 e109
  have e422 (X0 X1 : G) : (D.op (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := superpose e12 e154
  have e1938 (X0 X1 : G) : (D.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X0))) := superpose e422 e154
  have e4876 : sK0 ≠ (M.op sK0 (D.op sK0 sK0)) := superpose e1938 e11
  subsumption e4876 e9

/-- Left bijectivity in E3150 would imply E411, contradicted by
`rw477.Facts`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup3150_all_countermodel :
    ¬ SideQuasigroupLaw .all Law3150 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw477.Facts
  have hE : @Equation3150 G (opposite M) := hf.1
  have hn : ¬ @Equation3050 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law3150.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective3150_forces411 (opposite M) hE hQ)

private theorem leftBijective3161_forces411 {G : Type} (M : Magma G)
    (h : @Equation3161 G M) (hQ : IsSideQuasigroup .left M) : @Equation411 G M := by
  classical
  let D : Magma G := ⟨fun x y => (Equiv.ofBijective (M.op x) (hQ x)).symm y⟩
  have hd1 (x y : G) : M.op x (D.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).apply_symm_apply y
  have hd2 (x y : G) : D.op x (M.op x y) = y :=
    (Equiv.ofBijective (M.op x) (hQ x)).symm_apply_apply y
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op (M.op (M.op (M.op X1 X1) X2) X0) X2) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd1 ..
  have e11 : sK0 ≠ (M.op sK0 (M.op sK0 (M.op sK0 (M.op sK0 sK0)))) := mod_symm hn
  have e13 (X0 X1 X2 : G) : (M.op (M.op X0 X2) (D.op (M.op X1 X1) X0)) = X2 := superpose e9 e8
  have e14 (X0 X1 : G) : (M.op X1 X1) = (M.op X0 X0) := superpose e8 e8
  have e26 (X0 : G) : sK0 ≠ (M.op sK0 (M.op sK0 (M.op sK0 (M.op X0 X0)))) := superpose e14 e11
  have e31 (X0 X1 X2 : G) : (D.op X1 X0) = (M.op X0 (D.op (M.op X2 X2) X1)) := superpose e9 e13
  have e237 (X0 X1 : G) : sK0 ≠ (M.op sK0 (M.op sK0 (M.op sK0 (D.op X0 (D.op (M.op X1 X1) X0))))) := superpose e31 e26
  have e284 (X0 : G) : sK0 ≠ (M.op sK0 (M.op sK0 (D.op (M.op X0 X0) sK0))) := superpose e9 e237
  have e287 : sK0 ≠ (M.op sK0 (D.op sK0 sK0)) := superpose e31 e284
  subsumption e287 e9

/-- Left bijectivity in E3161 would imply E411, contradicted by
`rw481.Facts`, applied to the opposite operation. -/
@[parastrophe_result] theorem not_leftQuasigroup3161_all_countermodel :
    ¬ SideQuasigroupLaw .all Law3161 .left := by
  intro h
  obtain ⟨G, M, hf⟩ := rw481.Facts
  have hE : @Equation3161 G (opposite M) := fun x y z => hf.1 x z y
  have hn : ¬ @Equation3050 G M := by tauto
  have hQ := h G (opposite M) trivial ((@Law3161.models_iff G (opposite M)).mpr hE)
  exact hn (leftBijective3161_forces411 (opposite M) hE hQ)

end Parastrophes.Catalogue

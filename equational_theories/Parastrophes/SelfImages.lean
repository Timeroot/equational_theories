import equational_theories.Parastrophes.InverseIdentities
import equational_theories.Parastrophes.CancellationIdentities
import equational_theories.Parastrophes.TranslationLoops
import equational_theories.Parastrophes.DivisionTerms

/-! More exact left-division self-images. Each transfer is a finite sequence
of equational substitutions, originally found by Vampire and checked here by
Lean's kernel. The final theorems also prove that every target model has the
required division; this is essential to an exact characterization.

Most statements hold on arbitrary carriers. E669 and E1075 use finiteness
only to turn the target law's surjective rows into bijections. No external
prover or proof certificate is invoked by the Lean build. -/

namespace Parastrophes.Catalogue

private theorem transfer72_72 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation72 G M) : @Equation72 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := mod_symm (h ..)
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op sK1 (D.op sK0 sK0))) := mod_symm hn
  have e12 (X0 : G) : (M.op X0 X0) = (M.op (M.op X0 X0) X0) := superpose e8 e8
  have e13 (X0 X1 : G) : (M.op X1 (M.op X0 X0)) = (D.op X1 X0) := superpose e8 e10
  have e14 (X0 : G) : (D.op (M.op X0 X0) (M.op X0 X0)) = X0 := superpose e12 e10
  have e15 (X0 : G) : (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := superpose e12 e8
  have e16 (X0 : G) : (D.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := superpose e13 e15
  have e17 (X0 : G) : (D.op (D.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := superpose e13 e16
  have e18 (X0 X1 : G) : (D.op X1 (M.op X0 X0)) = (M.op X1 (D.op (M.op X0 X0) X0)) := superpose e13 e13
  have e76 (X0 X1 : G) : (D.op X1 (D.op (M.op X0 X0) X0)) = (M.op X1 (D.op (D.op (M.op X0 X0) X0) (M.op X0 X0))) := superpose e18 e13
  have e77 (X0 : G) : (D.op (M.op X0 X0) X0) = (D.op (D.op (D.op (M.op X0 X0) X0) (M.op X0 X0)) (D.op (D.op (M.op X0 X0) X0) (M.op X0 X0))) := superpose e18 e14
  have e85 (X0 : G) : (D.op X0 X0) = (D.op (M.op X0 X0) X0) := superpose e17 e77
  have e86 (X0 X1 : G) : (M.op X1 X0) = (D.op X1 (D.op (M.op X0 X0) X0)) := superpose e17 e76
  have e95 (X0 X1 : G) : (D.op X1 (D.op X0 X0)) = (M.op X1 X0) := superpose e85 e86
  have e155 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) := superpose e95 e11
  subsumption e155 e10

private theorem transfer117_117 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation117 G M) : @Equation117 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op X1 (M.op (M.op X0 X1) X0)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op (D.op sK0 sK1) sK0)) := mod_symm hn
  have e12 (X0 X1 : G) : (M.op (D.op X1 X0) (M.op X0 X1)) = X1 := superpose e9 e8
  have e21 (X0 X1 : G) : (D.op (D.op X0 X1) X0) = (M.op X1 X0) := superpose e12 e10
  have e40 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) := superpose e21 e11
  subsumption e40 e10

private theorem transfer501_501 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation501 G M) : @Equation501 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op X1 (M.op X1 (M.op X0 (M.op X0 X1)))) = X0 := mod_symm (h ..)
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op sK1 (D.op sK0 (D.op sK0 sK1)))) := mod_symm hn
  have e15 (X0 X1 : G) : (M.op X1 (M.op X0 (M.op X0 X1))) = (D.op X1 X0) := superpose e8 e10
  have e25 (X0 X1 : G) : (D.op X0 (D.op X0 X1)) = (M.op X1 (M.op X1 X0)) := superpose e15 e10
  have e51 : sK0 ≠ (D.op sK1 (D.op sK1 (M.op sK1 (M.op sK1 sK0)))) := superpose e25 e11
  have e63 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) := superpose e10 e51
  subsumption e63 e10

private theorem transfer669_669 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation669 G M) : @Equation669 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op X1 (M.op X0 (M.op (M.op X0 X1) X0))) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op sK0 (D.op (D.op sK0 sK1) sK0))) := mod_symm hn
  have e12 (X0 X1 : G) : (M.op (D.op X1 X0) (M.op X1 (M.op X0 X1))) = X1 := superpose e9 e8
  have e21 (X0 X1 : G) : (D.op (D.op X0 X1) X0) = (M.op X0 (M.op X1 X0)) := superpose e12 e10
  have e40 : sK0 ≠ (D.op sK1 (D.op sK0 (M.op sK0 (M.op sK1 sK0)))) := superpose e21 e11
  have e44 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) := superpose e10 e40
  subsumption e44 e10

private theorem transfer690_690 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation690 G M) : @Equation690 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op X0 (M.op (M.op X2 X1) X0))) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op sK0 (D.op (D.op sK2 sK1) sK0))) := mod_symm hn
  have e12 (X0 X1 X2 : G) : (M.op (D.op X1 X0) (M.op X2 (M.op X0 X2))) = X2 := superpose e9 e8
  have e24 (X0 X1 X2 : G) : (M.op X0 (M.op X2 X0)) = (D.op (D.op X1 X2) X0) := superpose e12 e10
  have e58 : sK0 ≠ (D.op sK1 (D.op sK0 (M.op sK0 (M.op sK1 sK0)))) := superpose e24 e11
  have e61 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) := superpose e10 e58
  subsumption e61 e10

private theorem transfer723_723 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation723 G M) : @Equation723 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op sK1 (D.op (D.op sK2 sK0) sK0))) := mod_symm hn
  have e12 (X0 X1 X2 : G) : (D.op X2 X0) = (M.op X1 (M.op X1 (M.op X0 (D.op X2 X0)))) := superpose e9 e8
  have e14 (X0 X1 X2 : G) : (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := superpose e8 e8
  have e15 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X2 X0) X0)) = (D.op X1 X0) := superpose e8 e10
  have e16 (X0 X1 X2 : G) : (M.op (M.op X2 X0) X0) = (M.op (D.op X1 X0) X0) := superpose e15 e14
  have e26 (X0 X1 X2 : G) : (M.op (M.op X2 X1) X1) = (D.op X0 (D.op X0 X1)) := superpose e15 e10
  have e71 (X0 X1 X2 : G) : (M.op X0 (D.op X1 X0)) = (D.op X2 (D.op X2 (D.op X1 X0))) := superpose e9 e26
  have e102 (X0 X1 : G) : (D.op X0 X0) = (M.op X1 (M.op X1 X0)) := superpose e9 e12
  have e135 (X0 X1 X2 : G) : (M.op (D.op X2 X1) (M.op (M.op X0 X1) X1)) = (D.op X1 X1) := superpose e16 e102
  have e154 (X1 X2 : G) : (D.op X1 X1) = (D.op (D.op X2 X1) X1) := superpose e15 e135
  have e849 : sK0 ≠ (D.op sK1 (D.op sK1 (D.op sK0 sK0))) := superpose e154 e11
  have e850 : sK0 ≠ (M.op sK0 (D.op sK0 sK0)) := superpose e71 e849
  subsumption e850 e9

private theorem transfer731_731 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation731 G M) : @Equation731 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op sK1 (D.op (D.op sK2 sK2) sK0))) := mod_symm hn
  have e12 (X0 X1 X2 : G) : (D.op (M.op X2 X2) X0) = (M.op X1 (M.op X1 X0)) := superpose e9 e8
  have e14 (X0 X1 X2 : G) : (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := superpose e8 e8
  have e15 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X2 X2) X0)) = (D.op X1 X0) := superpose e8 e10
  have e19 (X0 X1 X2 : G) : (D.op (M.op X1 X1) (D.op X2 X0)) = (M.op X2 X0) := superpose e9 e12
  have e26 (X0 X1 X2 : G) : (M.op (M.op X2 X2) (D.op (M.op X0 X0) X1)) = X1 := superpose e12 e8
  have e96 (X0 X1 X2 : G) : (M.op (M.op X2 X2) X1) = (D.op X0 (D.op X0 X1)) := superpose e15 e10
  have e180 (X0 X1 X2 : G) : (D.op X0 X1) = (M.op (M.op X2 X2) (M.op X0 X1)) := superpose e19 e9
  have e273 (X0 X1 X2 X3 : G) : (M.op (M.op X2 X2) (D.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)) = X3 := superpose e14 e26
  have e292 (X1 X2 X3 : G) : (M.op (M.op X2 X2) (D.op (D.op X1 X1) X3)) = X3 := superpose e180 e273
  have e431 (X0 : G) : sK0 ≠ (M.op (M.op X0 X0) (D.op (D.op sK2 sK2) sK0)) := superpose e96 e11
  subsumption e431 e292

private theorem transfer916_916 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation916 G M) : @Equation916 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := mod_symm (h ..)
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op (D.op sK1 sK1) (D.op sK0 sK0))) := mod_symm hn
  have e12 (X0 : G) : (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := superpose e8 e8
  have e13 (X0 X1 : G) : (M.op (M.op X1 X1) (M.op X0 X0)) = (D.op X1 X0) := superpose e8 e10
  have e14 (X0 : G) : (D.op X0 X0) = (M.op X0 (M.op X0 X0)) := superpose e13 e12
  have e15 (X0 : G) : (M.op X0 X0) = (D.op X0 (D.op X0 X0)) := superpose e14 e10
  have e18 (X0 X1 : G) : (D.op X1 (M.op X0 X0)) = (M.op (M.op X1 X1) (D.op X0 X0)) := superpose e13 e13
  have e24 (X0 : G) : (D.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (D.op X0 X0)) := superpose e13 e14
  have e27 (X0 X1 : G) : (M.op X1 X1) = (D.op (M.op X0 X0) (D.op X0 X1)) := superpose e13 e10
  have e51 (X0 : G) : (D.op (M.op X0 X0) (M.op X0 X0)) = (M.op (D.op X0 X0) (D.op X0 X0)) := superpose e15 e27
  have e69 (X0 : G) : (M.op (M.op X0 X0) (D.op X0 X0)) = (M.op (D.op X0 X0) (D.op X0 X0)) := superpose e24 e51
  have e70 (X0 : G) : (D.op X0 (M.op X0 X0)) = (M.op (D.op X0 X0) (D.op X0 X0)) := superpose e18 e69
  have e71 (X0 : G) : (M.op (D.op X0 X0) (D.op X0 X0)) = X0 := superpose e10 e70
  have e112 (X0 X1 : G) : (M.op X1 X1) = (D.op X0 (D.op (D.op X0 X0) X1)) := superpose e71 e27
  have e1031 : sK0 ≠ (M.op (D.op sK0 sK0) (D.op sK0 sK0)) := superpose e112 e11
  subsumption e1031 e71

private theorem transfer947_947 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation947 G M) : @Equation947 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op (D.op sK2 sK0) (D.op sK1 sK0))) := mod_symm hn
  have e12 (X0 X1 X2 : G) : (D.op X2 X0) = (M.op X1 (M.op X0 (M.op X1 (D.op X2 X0)))) := superpose e9 e8
  have e16 (X0 X1 X2 : G) : (M.op (M.op X2 X0) (M.op X1 X0)) = (D.op X1 X0) := superpose e8 e10
  have e19 (X0 X1 X2 : G) : (D.op X2 (D.op X1 X0)) = (M.op X0 (M.op X2 (D.op X1 X0))) := superpose e9 e16
  have e21 (X0 X1 X3 : G) : (D.op X3 (M.op X0 X1)) = (M.op (D.op X0 X1) (M.op X3 (M.op X0 X1))) := superpose e16 e16
  have e24 (X0 X1 X2 X3 : G) : (D.op (M.op X3 X1) (M.op X0 X1)) = (M.op (M.op X2 (M.op X0 X1)) (D.op X0 X1)) := superpose e16 e16
  have e28 (X0 X1 X2 : G) : (M.op X0 X1) = (D.op (M.op X2 X1) (D.op X0 X1)) := superpose e16 e10
  have e32 (X0 X1 : G) : (D.op X1 X0) = (M.op X1 (M.op X0 X0)) := superpose e9 e12
  have e43 (X0 X1 X2 : G) : (D.op X2 (M.op X0 X1)) = (M.op X2 (D.op X0 X1)) := superpose e16 e32
  have e49 (X0 X1 X2 : G) : (D.op X2 (M.op X1 X1)) = (M.op (D.op X0 X1) (M.op X2 (M.op X1 X1))) := superpose e32 e16
  have e52 (X0 X1 : G) : (M.op X1 X1) = (D.op X0 (D.op X0 X1)) := superpose e32 e10
  have e53 (X0 X1 : G) : (D.op (M.op X0 X1) X1) = (D.op X1 X1) := superpose e32 e16
  have e54 (X0 X1 : G) : (M.op X1 (D.op (M.op X0 X1) X1)) = X1 := superpose e32 e8
  have e57 (X0 X1 X2 : G) : (D.op X2 (M.op X1 X1)) = (M.op (D.op X0 X1) (D.op X2 X1)) := superpose e32 e49
  have e60 (X0 X1 X2 : G) : (M.op (D.op X0 X1) (D.op X2 X1)) = (M.op X2 (D.op X1 X1)) := superpose e43 e57
  have e122 (X0 X1 X2 : G) : (M.op (D.op X0 X1) (D.op X0 X1)) = (D.op (M.op X2 X1) (M.op X0 X1)) := superpose e28 e52
  have e126 (X0 X1 X2 : G) : (M.op (M.op X2 X1) (D.op X0 X1)) = (M.op (D.op X0 X1) (D.op X0 X1)) := superpose e43 e122
  have e134 (X0 X1 X2 : G) : (M.op X0 (D.op X1 X1)) = (M.op (M.op X2 X1) (D.op X0 X1)) := superpose e60 e126
  have e152 (X0 X1 : G) : (D.op X0 (D.op X1 X0)) = (D.op (D.op X1 X0) (D.op X1 X0)) := superpose e9 e53
  have e153 (X0 X1 X2 : G) : (D.op (M.op (M.op X2 X0) (M.op X1 X0)) (M.op (M.op X2 X0) (M.op X1 X0))) = (D.op X0 (M.op (M.op X2 X0) (M.op X1 X0))) := superpose e8 e53
  have e171 (X0 X1 X2 : G) : (D.op (M.op (M.op X2 X0) (M.op X1 X0)) (M.op (M.op X2 X0) (M.op X1 X0))) = (M.op X0 (D.op (M.op X2 X0) (M.op X1 X0))) := superpose e43 e153
  have e176 (X0 X1 X2 : G) : (D.op (M.op (M.op X2 X0) (M.op X1 X0)) (M.op (M.op X2 X0) (M.op X1 X0))) = (M.op X0 (M.op (M.op X2 X0) (D.op X1 X0))) := superpose e43 e171
  have e181 (X0 X1 X2 : G) : (D.op (M.op (M.op X2 X0) (M.op X1 X0)) (M.op (M.op X2 X0) (M.op X1 X0))) = (D.op (M.op X2 X0) (D.op X1 X0)) := superpose e19 e176
  have e185 (X0 X1 X2 : G) : (M.op X1 X0) = (D.op (M.op (M.op X2 X0) (M.op X1 X0)) (M.op (M.op X2 X0) (M.op X1 X0))) := superpose e28 e181
  have e189 (X0 X1 X2 : G) : (M.op X1 X0) = (M.op (M.op (M.op X2 X0) (M.op X1 X0)) (D.op (M.op X2 X0) (M.op X1 X0))) := superpose e43 e185
  have e191 (X0 X1 X2 : G) : (M.op X1 X0) = (M.op (M.op X2 X0) (D.op (M.op X1 X0) (M.op X1 X0))) := superpose e134 e189
  have e193 (X0 X1 X2 : G) : (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (D.op X1 X0))) := superpose e43 e191
  have e195 (X0 X1 X2 : G) : (M.op X1 X0) = (M.op (M.op X2 X0) (M.op X1 (D.op X0 X0))) := superpose e134 e193
  have e220 (X0 X1 : G) : (M.op X1 X1) = (M.op (M.op X1 X1) (D.op (D.op X0 X1) (M.op X1 X1))) := superpose e32 e54
  have e241 (X0 X1 : G) : (M.op X1 X1) = (M.op (M.op X1 X1) (M.op (D.op X0 X1) (D.op X1 X1))) := superpose e43 e220
  have e246 (X0 X1 : G) : (M.op X1 X1) = (M.op (D.op X0 X1) X1) := superpose e195 e241
  have e470 (X0 X1 : G) : (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := superpose e10 e246
  have e505 (X0 X1 : G) : (D.op X1 X0) = (M.op X0 (M.op X1 X0)) := superpose e16 e470
  have e546 (X0 X1 X2 : G) : (D.op (D.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op (D.op X0 (M.op X1 X2)) (D.op X0 (M.op X1 X2))) := superpose e21 e21
  have e573 (X0 X1 X2 : G) : (D.op (D.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X0 (D.op (M.op X1 X2) (M.op X1 X2))) := superpose e60 e546
  have e614 (X0 X1 X2 : G) : (D.op (D.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X0 (M.op (M.op X1 X2) (D.op X1 X2))) := superpose e43 e573
  have e641 (X0 X1 X2 : G) : (M.op X0 (M.op X1 (D.op X2 X2))) = (D.op (D.op X1 X2) (M.op X0 (M.op X1 X2))) := superpose e134 e614
  have e652 (X0 X1 X2 : G) : (M.op X0 (M.op X1 (D.op X2 X2))) = (M.op (D.op X1 X2) (D.op X0 (M.op X1 X2))) := superpose e43 e641
  have e658 (X0 X1 X2 : G) : (M.op X0 (M.op X1 (D.op X2 X2))) = (M.op (D.op X1 X2) (M.op X0 (D.op X1 X2))) := superpose e43 e652
  have e661 (X0 X1 X2 : G) : (M.op X0 (M.op X1 (D.op X2 X2))) = (D.op X0 (D.op X1 X2)) := superpose e505 e658
  have e912 (X0 X1 X2 X3 : G) : (D.op (M.op X2 (M.op X1 X1)) (D.op X0 X1)) = (M.op (M.op X3 (D.op X0 X1)) (D.op X0 (M.op X1 X1))) := superpose e32 e24
  have e1040 (X0 X1 X2 X3 : G) : (D.op (M.op X2 (M.op X1 X1)) (D.op X0 X1)) = (M.op (M.op X3 (D.op X0 X1)) (M.op X0 (D.op X1 X1))) := superpose e43 e912
  have e1107 (X0 X1 X2 X3 : G) : (D.op (M.op X2 (M.op X1 X1)) (D.op X0 X1)) = (D.op (M.op X3 (D.op X0 X1)) (D.op X0 X1)) := superpose e661 e1040
  have e1159 (X0 X1 X2 : G) : (D.op (D.op X0 X1) (D.op X0 X1)) = (D.op (M.op X2 (M.op X1 X1)) (D.op X0 X1)) := superpose e53 e1107
  have e1201 (X0 X1 X2 : G) : (D.op (D.op X0 X1) (D.op X0 X1)) = (D.op (D.op X2 X1) (D.op X0 X1)) := superpose e32 e1159
  have e1228 (X0 X1 X2 : G) : (D.op X1 (D.op X0 X1)) = (D.op (D.op X2 X1) (D.op X0 X1)) := superpose e152 e1201
  have e1272 (X0 X1 X2 : G) : (D.op X2 (M.op X0 (D.op X1 X2))) = (M.op (M.op X0 (D.op X1 X2)) (D.op X0 (D.op X1 X2))) := superpose e19 e505
  have e1288 (X0 X1 : G) : (M.op X0 X1) = (D.op X1 (D.op X0 X1)) := superpose e505 e10
  have e1319 (X0 X1 X2 : G) : (D.op X2 (M.op X0 (D.op X1 X2))) = (M.op X0 (D.op (D.op X1 X2) (D.op X1 X2))) := superpose e134 e1272
  have e1338 (X0 X1 X2 : G) : (D.op X2 (M.op X0 (D.op X1 X2))) = (M.op X0 (D.op X2 (D.op X1 X2))) := superpose e152 e1319
  have e1348 (X0 X1 X2 : G) : (M.op X0 (M.op X1 X2)) = (D.op X2 (M.op X0 (D.op X1 X2))) := superpose e1288 e1338
  have e1352 (X0 X1 X2 : G) : (M.op X0 (M.op X1 X2)) = (M.op X2 (D.op X0 (D.op X1 X2))) := superpose e43 e1348
  have e1922 (X0 X1 X2 X3 : G) : (D.op X3 (D.op X0 (D.op X1 X2))) = (M.op X3 (D.op X2 (M.op X0 (D.op X1 X2)))) := superpose e19 e43
  have e1997 (X0 X1 X2 X3 : G) : (D.op X3 (D.op X0 (D.op X1 X2))) = (M.op X3 (M.op X2 (D.op X0 (D.op X1 X2)))) := superpose e43 e1922
  have e2024 (X0 X1 X2 X3 : G) : (D.op X3 (D.op X0 (D.op X1 X2))) = (M.op X3 (M.op X0 (M.op X1 X2))) := superpose e1352 e1997
  have e13821 : sK0 ≠ (D.op sK1 (D.op sK0 (D.op sK1 sK0))) := superpose e1228 e11
  have e13940 : sK0 ≠ (M.op sK1 (M.op sK0 (M.op sK1 sK0))) := superpose e2024 e13821
  have e14019 : sK0 ≠ (M.op sK1 (D.op sK1 sK0)) := superpose e505 e13940
  subsumption e14019 e9

private theorem transfer960_960 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation960 G M) : @Equation960 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op (D.op sK2 sK1) (D.op sK0 sK0))) := mod_symm hn
  have e12 (X0 X1 X2 : G) : (M.op (D.op X1 X0) (M.op X0 (M.op X2 X2))) = X2 := superpose e9 e8
  have e14 (X0 X1 : G) : (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := superpose e8 e8
  have e15 (X0 X1 X2 : G) : (M.op (M.op X2 X1) (M.op X0 X0)) = (D.op X1 X0) := superpose e8 e10
  have e21 (X0 X1 X2 : G) : (M.op X2 (M.op X0 X0)) = (D.op (D.op X1 X2) X0) := superpose e12 e10
  have e50 (X0 : G) : (D.op X0 X0) = (M.op X0 (M.op X0 X0)) := superpose e14 e15
  have e62 (X0 X1 : G) : (M.op (D.op X1 X0) (D.op X0 X0)) = X0 := superpose e50 e12
  have e95 (X0 X1 X2 X3 : G) : (D.op (D.op X0 X1) X2) = (D.op (D.op X3 X1) X2) := superpose e21 e21
  have e117 (X0 X1 X2 : G) : (M.op X2 X2) = (D.op X1 (D.op (D.op X0 X1) X2)) := superpose e21 e10
  have e744 (X0 : G) : sK0 ≠ (D.op sK1 (D.op (D.op X0 sK1) (D.op sK0 sK0))) := superpose e95 e11
  have e764 : sK0 ≠ (M.op (D.op sK0 sK0) (D.op sK0 sK0)) := superpose e117 e744
  subsumption e764 e62

private theorem transfer978_978 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation978 G M) : @Equation978 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 := mod_symm (h ..)
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op (D.op sK2 sK2) (D.op sK0 sK1))) := mod_symm hn
  have e14 (X0 X1 X2 : G) : (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X1)) X0) := superpose e8 e8
  have e15 (X0 X1 X2 : G) : (M.op (M.op X2 X2) (M.op X0 X1)) = (D.op X1 X0) := superpose e8 e10
  have e29 (X0 X1 : G) : (M.op X1 X1) = (M.op X0 X0) := superpose e14 e14
  have e110 (X0 X1 : G) : (M.op X1 X1) = (D.op X0 X0) := superpose e15 e29
  have e112 (X0 X1 X2 : G) : (M.op X1 X0) = (D.op (M.op X2 X2) (D.op X0 X1)) := superpose e15 e10
  have e249 (X0 : G) : sK0 ≠ (D.op sK1 (D.op (M.op X0 X0) (D.op sK0 sK1))) := superpose e110 e11
  have e250 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) := superpose e112 e249
  subsumption e250 e10

private theorem transfer1075_1075 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1075 G M) : @Equation1075 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 : G) : (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X0)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op (D.op sK0 (D.op sK0 sK1)) sK0)) := mod_symm hn
  have e12 (X0 X1 : G) : (M.op (D.op X1 X0) (M.op (M.op X1 X0) X1)) = X1 := superpose e9 e8
  have e21 (X0 X1 : G) : (M.op (M.op X0 X1) X0) = (D.op (D.op X0 X1) X0) := superpose e12 e10
  have e56 : sK0 ≠ (D.op sK1 (M.op (M.op sK0 (D.op sK0 sK1)) sK0)) := superpose e21 e11
  have e61 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) := superpose e9 e56
  subsumption e61 e10

private theorem transfer1152_1152 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1152 G M) : @Equation1152 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X2 (M.op X0 X1)) X2)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op (D.op sK2 (D.op sK0 sK1)) sK2)) := mod_symm hn
  have e12 (X0 X1 X2 : G) : (M.op (D.op X1 X0) (M.op (M.op X2 X0) X2)) = X1 := superpose e9 e8
  have e14 (X0 X1 X2 : G) : (M.op (M.op X2 (M.op X0 X1)) X2) = (D.op X1 X0) := superpose e8 e10
  have e22 (X0 X1 X2 : G) : (M.op (M.op X2 X1) X2) = (D.op (D.op X0 X1) X0) := superpose e12 e10
  have e28 (X0 X1 X2 X3 : G) : (D.op X3 (M.op X3 (M.op X1 X0))) = (M.op (M.op X2 (D.op X0 X1)) X2) := superpose e14 e14
  have e39 (X0 X1 X2 : G) : (M.op X1 X0) = (M.op (M.op X2 (D.op X0 X1)) X2) := superpose e10 e28
  have e78 (X0 : G) : sK0 ≠ (D.op sK1 (M.op (M.op X0 (D.op sK0 sK1)) X0)) := superpose e22 e11
  have e84 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) := superpose e39 e78
  subsumption e84 e10

private theorem transfer1353_1353 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1353 G M) : @Equation1353 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op (M.op X2 X0) X1) X0)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op (D.op (D.op sK2 sK0) sK1) sK0)) := mod_symm hn
  have e14 (X0 X1 X2 : G) : (M.op (D.op (M.op X1 X2) X0) (M.op X0 X2)) = X2 := superpose e9 e8
  have e16 (X0 X1 X2 : G) : (M.op (M.op (M.op X2 X0) X1) X0) = (D.op X1 X0) := superpose e8 e10
  have e27 (X0 X1 X2 : G) : (M.op X2 X0) = (D.op (D.op (M.op X1 X0) X2) X0) := superpose e14 e10
  have e92 (X0 X1 X2 : G) : (M.op X2 X1) = (D.op (D.op (D.op X0 X1) X2) X1) := superpose e16 e27
  have e275 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) := superpose e92 e11
  subsumption e275 e10

private theorem transfer2115_2115 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation2115 G M) : @Equation2115 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op (M.op (M.op X1 X0) X2) (M.op X2 X0)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op (D.op (D.op sK1 sK0) sK2) (D.op sK2 sK0)) := mod_symm hn
  have e15 (X0 X1 X2 : G) : (M.op X0 (M.op (D.op (M.op X1 X2) X0) X2)) = X2 := superpose e9 e8
  have e35 (X0 X1 X2 : G) : (D.op X1 X0) = (M.op (D.op (M.op X2 X0) X1) X0) := superpose e15 e10
  have e169 (X0 X1 X2 : G) : (D.op X2 X1) = (M.op (D.op (D.op X0 X1) X2) X1) := superpose e35 e35
  have e565 (X0 X1 X2 : G) : (D.op (D.op (D.op X2 X1) X0) (D.op X0 X1)) = X1 := superpose e169 e10
  have e767 : sK0 ≠ sK0 := superpose e565 e11
  subsumption e767 rfl

private theorem implies723_72 {G : Type} (M : Magma G)
    (h : @Equation723 G M) : @Equation72 G M := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e6 (X0 X1 X2 : G) : (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := mod_symm (h ..)
  have e7 : sK0 ≠ (M.op sK1 (M.op sK1 (M.op sK0 sK0))) := mod_symm hn
  have e8 (X0 X1 X2 X3 : G) : (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := superpose e6 e6
  have e22 (X0 X1 X2 : G) : (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := superpose e6 e8
  have e46 (X0 X1 : G) : (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := superpose e22 e6
  have e86 (X0 : G) : (M.op X0 X0) = (M.op (M.op X0 X0) X0) := superpose e46 e46
  have e150 (X0 X1 : G) : (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := superpose e86 e6
  have e246 : sK0 ≠ sK0 := superpose e150 e7
  subsumption e246 rfl

private theorem implies947_72 {G : Type} (M : Magma G)
    (h : @Equation947 G M) : @Equation72 G M := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e6 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := mod_symm (h ..)
  have e7 : sK0 ≠ (M.op sK1 (M.op sK1 (M.op sK0 sK0))) := mod_symm hn
  have e8 (X0 X1 X2 X3 : G) : (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := superpose e6 e6
  have e14 (X0 X1 X2 : G) : (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := superpose e6 e8
  have e63 (X0 X1 : G) : (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := superpose e14 e6
  have e149 : sK0 ≠ sK0 := superpose e63 e7
  subsumption e149 rfl

private theorem implies978_2494 {G : Type} (M : Magma G)
    (h : @Equation978 G M) : @Equation2494 G M := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e6 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 := mod_symm (h ..)
  have e7 : sK0 ≠ (M.op (M.op sK1 (M.op (M.op sK0 sK0) sK0)) sK1) := mod_symm hn
  have e8 (X0 X1 X2 X3 : G) : (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X3 X3) X0)) = X2 := superpose e6 e6
  have e9 (X0 X1 X2 : G) : (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X1)) X0) := superpose e6 e6
  have e15 (X0 X1 : G) : (M.op X0 X0) = (M.op X1 X1) := superpose e9 e9
  have e20 (X0 X1 : G) : (M.op X1 (M.op X0 X0)) = X1 := superpose e9 e6
  have e36 (X0 X1 X2 X3 X4 X5 : G) : (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X5 X5) (M.op (M.op X2 X2) (M.op X3 X0)))) := superpose e8 e8
  have e38 (X0 X1 X2 : G) : (M.op (M.op X0 X0) (M.op (M.op X2 X2) X1)) = X1 := superpose e9 e8
  have e43 (X0 X1 X2 X3 : G) : (M.op (M.op (M.op X1 X1) (M.op (M.op (M.op X2 X2) X0) X3)) X0) = X3 := superpose e8 e8
  have e50 (X0 X1 X2 X3 X4 : G) : (M.op (M.op X4 X4) (M.op X2 X0)) = (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X3 X3) X0)) := superpose e8 e6
  have e59 (X0 X1 X3 X4 : G) : (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op X3 X0)) := superpose e38 e36
  have e96 (X0 : G) : sK0 ≠ (M.op (M.op sK1 (M.op (M.op X0 X0) sK0)) sK1) := superpose e15 e7
  have e150 (X0 X1 X3 : G) : (M.op (M.op X3 X3) X0) = (M.op (M.op X1 X1) X0) := superpose e38 e38
  have e530 (X0 X1 : G) : sK0 ≠ (M.op (M.op sK1 (M.op (M.op (M.op X0 X0) X1) (M.op sK0 X1))) sK1) := superpose e59 e96
  have e748 (X0 X1 X2 X3 X4 : G) : (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X3 X3) X4)) X2) = X4 := superpose e50 e43
  have e866 (X2 X3 X4 : G) : (M.op (M.op X2 (M.op (M.op X3 X3) X4)) X2) = X4 := superpose e38 e748
  have e994 (X0 X1 : G) : sK0 ≠ (M.op (M.op sK1 (M.op (M.op X0 X0) (M.op sK0 (M.op X1 X1)))) sK1) := superpose e150 e530
  have e997 (X1 : G) : sK0 ≠ (M.op sK0 (M.op X1 X1)) := superpose e866 e994
  subsumption e997 e20

private theorem implies1152_2494 {G : Type} (M : Magma G)
    (h : @Equation1152 G M) : @Equation2494 G M := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e6 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X2 (M.op X0 X1)) X2)) = X0 := mod_symm (h ..)
  have e7 : sK0 ≠ (M.op (M.op sK1 (M.op (M.op sK0 sK0) sK0)) sK1) := mod_symm hn
  have e8 (X0 X1 X2 X3 : G) : (M.op (M.op (M.op X1 (M.op X0 X2)) X1) (M.op (M.op X3 X0) X3)) = X2 := superpose e6 e6
  have e16 (X0 X1 X2 X3 : G) : (M.op (M.op (M.op X1 (M.op (M.op (M.op X2 X0) X2) X3)) X1) X0) = X3 := superpose e8 e8
  have e25 (X0 X1 X3 X4 : G) : (M.op (M.op X4 X3) X4) = (M.op (M.op (M.op X1 X0) X1) (M.op X3 X0)) := superpose e8 e16
  have e64 (X0 X1 X2 : G) : (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X2) := superpose e25 e25
  have e80 (X0 X1 X2 : G) : (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) = X2 := superpose e25 e8
  have e319 (X0 : G) : sK0 ≠ (M.op (M.op X0 (M.op (M.op sK0 sK0) sK0)) X0) := superpose e64 e7
  subsumption e319 e80

private theorem implies2115_117 {G : Type} (M : Magma G)
    (h : @Equation2115 G M) : @Equation117 G M := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e6 (X0 X1 X2 : G) : (M.op (M.op (M.op X1 X0) X2) (M.op X2 X0)) = X0 := mod_symm (h ..)
  have e7 : sK0 ≠ (M.op sK1 (M.op (M.op sK0 sK1) sK0)) := mod_symm hn
  have e9 (X0 X2 : G) : (M.op X0 (M.op (M.op X2 X0) X2)) = X2 := superpose e6 e6
  have e16 : sK0 ≠ sK0 := superpose e9 e7
  subsumption e16 rfl

/-- E72 characterizes its own left-division image on arbitrary carriers.
The two division identities transfer E72 to the inverse operation; the
existing uniform division term supplies bijectivity for the converse. -/
@[parastrophe_result] theorem left_characterizes72_all :
    Characterizes .all Law72 .left Law72 := by
  apply characterizes_of_division
  · exact termRecovery_sideQuasigroup (uniform_implies_term ⟨_,left_term72_all_inverse⟩)
  all_goals
    intro G M D _ hd h
    exact (@Law72.models_iff G D).mpr (transfer72_72 M D hd ((@Law72.models_iff G M).mp h))

/-- E117 characterizes its own left-division image on arbitrary carriers.
The two division identities transfer E117 to the inverse operation; the
existing uniform division term supplies bijectivity for the converse. -/
@[parastrophe_result] theorem left_characterizes117_all :
    Characterizes .all Law117 .left Law117 := by
  apply characterizes_of_division
  · exact termRecovery_sideQuasigroup (uniform_implies_term ⟨_,left_term117_all_inverse⟩)
  all_goals
    intro G M D _ hd h
    exact (@Law117.models_iff G D).mpr (transfer117_117 M D hd ((@Law117.models_iff G M).mp h))

/-- E501 characterizes its own left-division image on arbitrary carriers.
The two division identities transfer E501 to the inverse operation; the
existing uniform division term supplies bijectivity for the converse. -/
@[parastrophe_result] theorem left_characterizes501_all :
    Characterizes .all Law501 .left Law501 := by
  apply characterizes_of_division
  · exact termRecovery_sideQuasigroup (uniform_implies_term ⟨_,left_term501_all_inverse⟩)
  all_goals
    intro G M D _ hd h
    exact (@Law501.models_iff G D).mpr (transfer501_501 M D hd ((@Law501.models_iff G M).mp h))

/-- E690 characterizes its own left-division image on arbitrary carriers.
The two division identities transfer E690 to the inverse operation; the
existing uniform division term supplies bijectivity for the converse. -/
@[parastrophe_result] theorem left_characterizes690_all :
    Characterizes .all Law690 .left Law690 := by
  apply characterizes_of_division
  · exact termRecovery_sideQuasigroup (uniform_implies_term ⟨_,left_term690_all⟩)
  all_goals
    intro G M D _ hd h
    exact (@Law690.models_iff G D).mpr (transfer690_690 M D hd ((@Law690.models_iff G M).mp h))

/-- E916 characterizes its own left-division image on arbitrary carriers.
The two division identities transfer E916 to the inverse operation; the
existing uniform division term supplies bijectivity for the converse. -/
@[parastrophe_result] theorem left_characterizes916_all :
    Characterizes .all Law916 .left Law916 := by
  apply characterizes_of_division
  · exact termRecovery_sideQuasigroup (uniform_implies_term ⟨_,left_term916_all_inverse⟩)
  all_goals
    intro G M D _ hd h
    exact (@Law916.models_iff G D).mpr (transfer916_916 M D hd ((@Law916.models_iff G M).mp h))

/-- E1353 characterizes its own left-division image on arbitrary carriers.
The two division identities transfer E1353 to the inverse operation; the
existing uniform division term supplies bijectivity for the converse. -/
@[parastrophe_result] theorem left_characterizes1353_all :
    Characterizes .all Law1353 .left Law1353 := by
  apply characterizes_of_division
  · exact termRecovery_sideQuasigroup (uniform_implies_term ⟨_,left_term1353_all⟩)
  all_goals
    intro G M D _ hd h
    exact (@Law1353.models_iff G D).mpr (transfer1353_1353 M D hd ((@Law1353.models_iff G M).mp h))

/-- E723 characterizes its own left-division image on arbitrary carriers. -/
@[parastrophe_result] theorem left_characterizes723_all :
    Characterizes .all Law723 .left Law723 := by
  apply characterizes_of_division
  · intro G M _ h
    have ht := implies723_72 M ((@Law723.models_iff G M).mp h)
    exact sideQuasigroup_of_division (left_term72_all_inverse G M trivial
      ((@Law72.models_iff G M).mpr ht))
  all_goals
    intro G M D _ hd h
    exact (@Law723.models_iff G D).mpr (transfer723_723 M D hd ((@Law723.models_iff G M).mp h))

/-- E947 characterizes its own left-division image on arbitrary carriers. -/
@[parastrophe_result] theorem left_characterizes947_all :
    Characterizes .all Law947 .left Law947 := by
  apply characterizes_of_division
  · intro G M _ h
    have ht := implies947_72 M ((@Law947.models_iff G M).mp h)
    exact sideQuasigroup_of_division (left_term72_all_inverse G M trivial
      ((@Law72.models_iff G M).mpr ht))
  all_goals
    intro G M D _ hd h
    exact (@Law947.models_iff G D).mpr (transfer947_947 M D hd ((@Law947.models_iff G M).mp h))

/-- E2115 characterizes its own left-division image on arbitrary carriers. -/
@[parastrophe_result] theorem left_characterizes2115_all :
    Characterizes .all Law2115 .left Law2115 := by
  apply characterizes_of_division
  · intro G M _ h
    have ht := implies2115_117 M ((@Law2115.models_iff G M).mp h)
    exact sideQuasigroup_of_division (left_term117_all_inverse G M trivial
      ((@Law117.models_iff G M).mpr ht))
  all_goals
    intro G M D _ hd h
    exact (@Law2115.models_iff G D).mpr (transfer2115_2115 M D hd ((@Law2115.models_iff G M).mp h))

/-- E978 characterizes its own left-division image on arbitrary carriers. -/
@[parastrophe_result] theorem left_characterizes978_all :
    Characterizes .all Law978 .left Law978 := by
  apply characterizes_of_division
  · intro G M _ h
    have ht := implies978_2494 M ((@Law978.models_iff G M).mp h)
    have hd := right_term1073 G (opposite M) trivial
      ((@Law1073.models_iff G (opposite M)).mpr ht)
    have hq := sideQuasigroup_of_division hd
    exact hq
  all_goals
    intro G M D _ hd h
    exact (@Law978.models_iff G D).mpr (transfer978_978 M D hd ((@Law978.models_iff G M).mp h))

/-- E1152 characterizes its own left-division image on arbitrary carriers. -/
@[parastrophe_result] theorem left_characterizes1152_all :
    Characterizes .all Law1152 .left Law1152 := by
  apply characterizes_of_division
  · intro G M _ h
    have ht := implies1152_2494 M ((@Law1152.models_iff G M).mp h)
    have hd := right_term1073 G (opposite M) trivial
      ((@Law1073.models_iff G (opposite M)).mpr ht)
    have hq := sideQuasigroup_of_division hd
    exact hq
  all_goals
    intro G M D _ hd h
    exact (@Law1152.models_iff G D).mpr (transfer1152_1152 M D hd ((@Law1152.models_iff G M).mp h))

/-- E731 characterizes its own left-division image on arbitrary carriers. -/
@[parastrophe_result] theorem left_characterizes731_all :
    Characterizes .all Law731 .left Law731 := by
  apply characterizes_of_division
  · intro G M _ h
    have hh := (@Law731.models_iff G M).mp h
    exact leftQuasigroup_of_translationLoops M (fun y => [y,M.op y y])
      (fun y x => (hh x y y).symm)
  all_goals
    intro G M D _ hd h
    exact (@Law731.models_iff G D).mpr (transfer731_731 M D hd ((@Law731.models_iff G M).mp h))

/-- E960 characterizes its own left-division image on arbitrary carriers. -/
@[parastrophe_result] theorem left_characterizes960_all :
    Characterizes .all Law960 .left Law960 := by
  apply characterizes_of_division
  · intro G M _ h
    have hh := (@Law960.models_iff G M).mp h
    exact sideQuasigroup_of_division (left_term916_all_inverse G M trivial
      ((@Law916.models_iff G M).mpr (fun x y => hh x y y)))
  all_goals
    intro G M D _ hd h
    exact (@Law960.models_iff G D).mpr (transfer960_960 M D hd ((@Law960.models_iff G M).mp h))

/-- E669 characterizes its own left-division image on finite carriers.
Its defining identity makes rows surjective, hence bijective in this scope. -/
@[parastrophe_result] theorem left_characterizes669_fin :
    Characterizes .fin Law669 .left Law669 := by
  apply characterizes_of_division
  · intro G M hG h
    letI : Finite G := hG
    have hh := (@Law669.models_iff G M).mp h
    intro y
    have hs : Function.Surjective (M.op y) := fun x => ⟨M.op x (M.op (M.op x y) x),(hh x y).symm⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs,hs⟩
  all_goals
    intro G M D _ hd h
    exact (@Law669.models_iff G D).mpr (transfer669_669 M D hd ((@Law669.models_iff G M).mp h))

/-- E1075 characterizes its own left-division image on finite carriers.
Its defining identity makes rows surjective, hence bijective in this scope. -/
@[parastrophe_result] theorem left_characterizes1075_fin :
    Characterizes .fin Law1075 .left Law1075 := by
  apply characterizes_of_division
  · intro G M hG h
    letI : Finite G := hG
    have hh := (@Law1075.models_iff G M).mp h
    intro y
    have hs : Function.Surjective (M.op y) := fun x => ⟨M.op (M.op x (M.op x y)) x,(hh x y).symm⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs,hs⟩
  all_goals
    intro G M D _ hd h
    exact (@Law1075.models_iff G D).mpr (transfer1075_1075 M D hd ((@Law1075.models_iff G M).mp h))

end Parastrophes.Catalogue

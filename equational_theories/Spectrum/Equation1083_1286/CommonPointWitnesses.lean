import equational_theories.Spectrum.Equation1083_1286.CommonPoint
import equational_theories.Spectrum.Equation1083_1286.DesignWitnesses
import equational_theories.Spectrum.QuadraticSeeds
import equational_theories.Spectrum.Generated.NoteWitnesses

/-! Smaller common-point models and polynomial families in residue two mod 3.
E1083: 119*(30*t+2)^2-6. E1286: 119*(30*t+2)^4-6.
The design and all large model checks are symbolic. -/
namespace Spectrum.E1083E1286
open Law Law.MagmaLaw
variable {which : Bool}

def scalarPointed {n : ℕ} [NeZero n] (a b : ZMod n)
    (hx : (if which then a*b*(a^2+b) else a*b*(a+b^2))=1)
    (hy : a+a^2*b^2+b^2=0) : Pointed which (ZMod n) where
  op := scalar a b
  lawful := scalar_lawful a b hx hy
  point := 0
  fixed := by simp [scalar]

def pointed17 (which : Bool) : Pointed which (ZMod 17) := by
  cases which
  · exact scalarPointed 14 6 (by decide) (by decide)
  · exact scalarPointed 11 6 (by decide) (by decide)

def squarePointed (n : ℕ) : Pointed false (ZMod n × ZMod n) where
  op := QuadraticSeeds.eisenstein
  lawful := fun x y => (QuadraticSeeds.law1083 x y).symm
  point := (0,0)
  fixed := by simp [QuadraticSeeds.eisenstein]

def quarticPointed (n : ℕ) (which : Bool) :
    Pointed which (ZMod n × ZMod n × ZMod n × ZMod n) where
  op := QuarticSeeds.op 1 (-1) 2 (-2)
  lawful := by
    cases which
    · exact fun x y => (QuarticSeeds.law_1083 x y).symm
    · exact fun x y => (QuarticSeeds.law_1286 x y).symm
  point := (0,0,0,0)
  fixed := QuarticSeeds.idempotent _ _ _ _ _

private theorem cyclic_units (q : ℕ) (hq : q.Coprime 30)
    (i j : Fin 6) (hij : i ≠ j) : IsUnit ((i.val : ZMod q) - (j.val : ZMod q)) := by
  have hu (k : ℕ) (hk : k ∣ 30^2) : IsUnit (k : ZMod q) :=
    (ZMod.isUnit_iff_coprime k q).mpr ((hq.pow_right 2).symm.of_dvd_left hk)
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | norm_num
  all_goals exact hu _ (by decide)

theorem cyclic7 {q : ℕ} (hq : 0 < q) (hc : q.Coprime 30) : PBD.HasTD 7 q := by
  letI : NeZero q := ⟨by omega⟩
  let D := PBD.Transversal.ring (fun i : Fin 6 => (i.val : ZMod q)) (cyclic_units q hc)
  exact ⟨(D.reindex (finSuccEquiv 6)).relabel (ZMod.finEquiv q).toEquiv.symm⟩

theorem model113 : (law which).HasModel 113 :=
  common_point_model
    (PBD.HasTD.primePower (k := 7) (p := 2) (e := 4) (by decide) (by decide) (by decide))
    idem7 (pointed17 which) (by simp)

theorem model_1083_50 : Law1083.HasModel 50 := by
  let G : Pointed false (Fin 8) := {
    op := NoteWitness.table_1083_8.op
    lawful := by unfold Lawful; decide
    point := 0
    fixed := rfl }
  exact common_point_model
    (PBD.HasTD.primePower (k := 7) (p := 7) (e := 1) (by decide) (by decide) (by decide))
    idem7 G (by simp)

theorem quadratic_family (t : ℕ) : Law1083.HasModel (119*(30*t+2)^2-6) := by
  let m := 30*t+2
  let q := 17*m^2-1
  letI : NeZero m := ⟨by dsimp [m]; omega⟩
  have hm : m % 30 = 2 := by dsimp [m]; omega
  have hp : 0 < m^2 := pow_pos (by dsimp [m]; omega) _
  have hq : 0 < q := by dsimp [q]; omega
  have hc : q+1 = 17*m^2 := by dsimp [q]; omega
  have hmod : (q+1)%30 = 8 := by
    rw [hc]
    norm_num [Nat.mul_mod, Nat.pow_mod, hm]
  have hcop : q.Coprime 30 := by
    have hr : q%30 = 7 := by omega
    change Nat.gcd q 30 = 1
    rw [Nat.gcd_comm q 30, Nat.gcd_rec 30 q, hr]
    decide
  have h := common_point_model (cyclic7 hq hcop) idem7
    ((pointed17 false).product (squarePointed m)) (show _ = q+1 from by
      simpa [pow_two] using hc.symm)
  convert h using 1
  change 119*m^2-6 = 7*q+1
  omega

theorem quartic_family (t : ℕ) : Law1286.HasModel (119*(30*t+2)^4-6) := by
  let m := 30*t+2
  let q := 17*m^4-1
  letI : NeZero m := ⟨by dsimp [m]; omega⟩
  have hm : m % 30 = 2 := by dsimp [m]; omega
  have hp : 0 < m^4 := pow_pos (by dsimp [m]; omega) _
  have hq : 0 < q := by dsimp [q]; omega
  have hc : q+1 = 17*m^4 := by dsimp [q]; omega
  have hmod : (q+1)%30 = 2 := by
    rw [hc]
    norm_num [Nat.mul_mod, Nat.pow_mod, hm]
  have hcop : q.Coprime 30 := by
    have hr : q%30 = 1 := by omega
    change Nat.gcd q 30 = 1
    rw [Nat.gcd_comm q 30, Nat.gcd_rec 30 q, hr]
    decide
  have h := common_point_model (cyclic7 hq hcop) idem7
    ((pointed17 true).product (quarticPointed m true)) (show _ = q+1 from by
      simpa [pow_succ, Nat.mul_assoc] using hc.symm)
  convert h using 1
  change 119*m^4-6 = 7*q+1
  omega

theorem model_1083_113 : Law1083.HasModel 113 := model113 (which := false)
theorem model_1286_113 : Law1286.HasModel 113 := model113 (which := true)
theorem model_1083_17 : Law1083.HasModel 17 := (pointed17 false).hasModel (by simp)
theorem model_1286_17 : Law1286.HasModel 17 := (pointed17 true).hasModel (by simp)
theorem model_1083_470 : Law1083.HasModel 470 := quadratic_family 0
theorem model_1286_1898 : Law1286.HasModel 1898 := quartic_family 0

spectrum_assert quadratic_family complete
spectrum_assert quartic_family complete
spectrum_assert model_1083_50 complete
spectrum_assert model_1083_113 complete
spectrum_assert model_1286_113 complete

/-- info: 'Spectrum.E1083E1286.quartic_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quartic_family

end Spectrum.E1083E1286

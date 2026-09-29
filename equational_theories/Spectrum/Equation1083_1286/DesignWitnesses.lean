import equational_theories.Spectrum.Equation1083_1286.DesignModels
import equational_theories.Spectrum.QuarticSeeds
import equational_theories.Spectrum.OpenWitnesses

/-! Symbolic constructions for E1083 and E1286, including orders congruent
to two modulo three. Finite-field designs and companion operations replace
large multiplication tables. All displayed witnesses are proved in Lean. -/
namespace Spectrum.E1083E1286
open Law Law.MagmaLaw
variable {which : Bool}

def scalar {R : Type*} [CommRing R] (a b : R) (x y : R) := a*x+b*y

theorem scalar_lawful {R : Type*} [CommRing R] (a b : R)
    (hx : (if which then a*b*(a^2+b) else a*b*(a+b^2))=1)
    (hy : a+a^2*b^2+b^2=0) : Lawful which (scalar a b) := by
  cases which <;> intro x y <;> dsimp [scalar] <;>
    dsimp at hx <;> linear_combination x*hx+y*hy

theorem scalar_model {n : ℕ} [NeZero n] (a b : ZMod n)
    (hx : (if which then a*b*(a^2+b) else a*b*(a+b^2))=1)
    (hy : a+a^2*b^2+b^2=0) : Model which (Fin n) := by
  have h : Model which (ZMod n) := ⟨scalar a b, scalar_lawful a b hx hy, by simp⟩
  exact h.relabel (ZMod.finEquiv n).toEquiv.symm

theorem scalar_idempotent {n : ℕ} [NeZero n] (a b : ZMod n)
    (hx : (if which then a*b*(a^2+b) else a*b*(a+b^2))=1)
    (hy : a+a^2*b^2+b^2=0) (hi : a+b=1) : Model which (Fin n) true := by
  have h : Model which (ZMod n) true := ⟨scalar a b, scalar_lawful a b hx hy, by
    intro _ x
    dsimp [scalar]
    linear_combination x*hi⟩
  exact h.relabel (ZMod.finEquiv n).toEquiv.symm

theorem quartic (n : ℕ) [NeZero n] : Model which (Fin (n^4)) true := by
  let A := ZMod n × ZMod n × ZMod n × ZMod n
  have hl : Lawful which (QuarticSeeds.op (R := ZMod n) 1 (-1) 2 (-2)) := by
    cases which
    · exact fun x y => (QuarticSeeds.law_1083 x y).symm
    · exact fun x y => (QuarticSeeds.law_1286 x y).symm
  have h : Model which A true := ⟨QuarticSeeds.op 1 (-1) 2 (-2), hl,
    fun _ => QuarticSeeds.idempotent _ _ _ _⟩
  exact h.relabel (Fintype.equivFinOfCardEq (by simp [A, pow_succ, Nat.mul_assoc]))

theorem idem7 : Model which (Fin 7) true :=
  scalar_idempotent 2 6 (by cases which <;> decide) (by decide) (by decide)

theorem idem9 : Model which (Fin 9) true := by
  have hl : Lawful which (OpenWitnesses.op1286_9 (R := ZMod 3)) := by
    have h6 : (6 : ZMod 3) = 0 := by decide
    have h7 : (7 : ZMod 3) = 1 := by decide
    have h9 : (9 : ZMod 3) = 0 := by decide
    cases which <;> intro x y <;> ext <;>
      dsimp [OpenWitnesses.op1286_9] <;> ring_nf <;>
      simp only [h6, h7, h9, mul_zero, mul_one, neg_zero, zero_add, add_zero, sub_zero]
  have h : Model which (ZMod 3 × ZMod 3) true :=
    ⟨OpenWitnesses.op1286_9, hl, fun _ => OpenWitnesses.op1286_9_idempotent⟩
  exact h.relabel (Fintype.equivFinOfCardEq (by simp))

theorem idem1008 : Model which (Fin 1008) true :=
  ((idem7.product idem9).product (quartic 2)).relabel (Fintype.equivFinOfCardEq (by simp))

theorem idem1009 : Model which (Fin 1009) true :=
  scalar_idempotent 958 52 (by cases which <;> decide) (by decide) (by decide)

theorem seed11 : Model which (Fin 11) := by
  cases which
  · exact scalar_model 6 9 (by decide) (by decide)
  · exact scalar_model 1 7 (by decide) (by decide)

theorem Model.pow {n : ℕ} {idem : Bool} (h : Model which (Fin n) idem) (e : ℕ) :
    Model which (Fin (n^e)) idem := by
  induction e with
  | zero =>
    rw [pow_zero]
    refine ⟨fun x _ => x, ?_, fun _ _ => rfl⟩
    cases which <;> exact fun _ _ => Subsingleton.elim _ _
  | succ e ih =>
    exact (ih.product h).relabel (Fintype.equivFinOfCardEq (by simp [pow_succ]))

theorem td1009 : PBD.HasTD 1009 1009 :=
  PBD.HasTD.primePower (p := 1009) (e := 1) (by norm_num) (by decide) (by decide)

theorem million_model : (law which).HasModel 1017083 :=
  hasTD_models td1009 (by decide) idem1009.forget seed11 idem1008 idem1009

/-- An infinite family in the residue class omitted by the idempotent tail. -/
theorem exponential_family (t : ℕ) :
    (law which).HasModel (1008*1009^(t+1)+11) := by
  have hq : 1009 ≤ 1009^(t+1) := by
    have ht : 1 ≤ 1009^t := Nat.one_le_pow t 1009 (by decide)
    rw [pow_succ]
    omega
  have hD : PBD.HasTD 1009 (1009^(t+1)) :=
    PBD.HasTD.primePower (by norm_num) (by omega) (by omega)
  exact hasTD_models hD (by omega) (idem1009.pow (t+1)).forget seed11 idem1008 idem1009

theorem model_1083_1017083 : Law1083.HasModel 1017083 := million_model (which := false)
theorem model_1286_1017083 : Law1286.HasModel 1017083 := million_model (which := true)
theorem model_1083_11 : Law1083.HasModel 11 := (seed11 (which := false)).hasModel
theorem model_1286_11 : Law1286.HasModel 11 := (seed11 (which := true)).hasModel
theorem model_1083_1008 : Law1083.HasModel 1008 := (idem1008 (which := false)).hasModel
theorem model_1286_1008 : Law1286.HasModel 1008 := (idem1008 (which := true)).hasModel
theorem model_1083_1009 : Law1083.HasModel 1009 := (idem1009 (which := false)).hasModel
theorem model_1286_1009 : Law1286.HasModel 1009 := (idem1009 (which := true)).hasModel

spectrum_assert exponential_family complete
spectrum_assert model_1083_1017083 complete
spectrum_assert model_1286_1017083 complete

/-- info: 'Spectrum.E1083E1286.exponential_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exponential_family

end Spectrum.E1083E1286

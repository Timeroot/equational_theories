import equational_theories.Definability.CycleFourCounting

/-!
# Exact E3253 row counts separate the four-cycle law

Adding rows that reach a distinct two-cycle completes the exact E3253 count.
It has an unbounded ratio to the E411 count, refuting unrestricted FO-structural
interpretation from E3253 to E411.
-/

open Law Law.MagmaLaw
namespace EventualRowExactCounting
variable {A : Type} [Fintype A] [DecidableEq A]
open EventualRowUpperCounting

noncomputable def tripleEquiv (a b c : A) (_hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Triple a b c ≃ CycleThreeCounting.Fiber a b c where
  toFun f := ⟨Function.update f.val c a,by simp [Function.update,hac,hbc,f.property]⟩
  invFun f := ⟨Function.update f.val c b,by simp [Function.update,hac,hbc,f.property]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    by_cases hx : x = c
    · subst x; simp [Function.update,f.property]
    · simp [Function.update,hx]
  right_inv f := by
    apply Subtype.ext
    funext x
    by_cases hx : x = c
    · subst x; simp [Function.update,f.property]
    · simp [Function.update,hx]

noncomputable def longEquiv (a : A) : Long a ≃ CycleThreeCounting.Extra a :=
  Equiv.sigmaCongrRight (fun b => Equiv.sigmaCongrRight (fun c => by
    have hc := c.property
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hc
    exact tripleEquiv a b.val c.val b.property.symm (Ne.symm hc.1) (Ne.symm hc.2)))

theorem long_count (a : A) : Fintype.card (Long a) =
    (Fintype.card A - 1) * ((Fintype.card A - 2) * Fintype.card A ^ (Fintype.card A - 3)) := by
  rw [Fintype.card_congr (longEquiv a),CycleThreeCounting.extra_count]

abbrev Short (a : A) := EightRowCounting.Row8 a ⊕ EventualRowCounting.Extra a

def rowEncode (a : A) : Short a ⊕ Long a → EventualRowCounting.Row a
  | .inl f => EventualRowCounting.rowEncode a f
  | .inr ⟨b,c,f⟩ => ⟨f.val,by rw [f.property.1,f.property.2.1,f.property.2.2]⟩

omit [Fintype A] in
theorem short_long_ne (a : A) (s : Short a) (t : Long a) :
    (EventualRowCounting.rowEncode a s).val ≠ t.2.2.val := by
  intro h
  have hc := t.2.1.property
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hc
  cases s with
  | inl f =>
    have hh := f.property
    change f.val = t.2.2.val at h
    rw [h,t.2.2.property.1,t.2.2.property.2.1] at hh
    exact hc.1 hh
  | inr f =>
    have hh : f.2.val (f.2.val a) = f.2.val a := by rw [f.2.property.1,f.2.property.2]
    change f.2.val = t.2.2.val at h
    rw [h,t.2.2.property.1,t.2.2.property.2.1] at hh
    exact hc.2 hh

omit [Fintype A] in
theorem rowEncode_injective (a : A) : Function.Injective (rowEncode a) := by
  intro f g h
  have hv := congrArg Subtype.val h
  cases f with
  | inl f =>
    cases g with
    | inl g => exact congrArg Sum.inl (EventualRowCounting.rowEncode_injective a (Subtype.ext hv))
    | inr g => exact (short_long_ne a f g hv).elim
  | inr f =>
    cases g with
    | inl g => exact (short_long_ne a g f hv.symm).elim
    | inr g =>
      congr 1
      rcases f with ⟨⟨b,hb⟩,⟨c,hc⟩,f⟩
      rcases g with ⟨⟨b',hb'⟩,⟨c',hc'⟩,g⟩
      change f.val = g.val at hv
      have hbb : b = b' := f.property.1.symm.trans ((congrFun hv a).trans g.property.1)
      subst b'
      have hcc : c = c' := f.property.2.1.symm.trans ((congrFun hv b).trans g.property.2.1)
      subst c'
      congr 2
      exact Subtype.ext hv

omit [Fintype A] in
theorem rowEncode_surjective (a : A) : Function.Surjective (rowEncode a) := by
  intro f
  obtain ⟨p,hp⟩ := EventualRowUpperCounting.casesMap_surjective a f
  rcases p with p | p | p
  · exact ⟨.inl (.inl p),hp⟩
  · exact ⟨.inl (.inr p),hp⟩
  · exact ⟨.inr p,hp⟩

theorem row_count (a : A) : Fintype.card (EventualRowCounting.Row a) =
    Fintype.card A ^ (Fintype.card A - 1) + 2 * ((Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2)) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) * Fintype.card A ^ (Fintype.card A - 3)) := by
  rw [← Fintype.card_congr (Equiv.ofBijective (rowEncode a) ⟨rowEncode_injective a,rowEncode_surjective a⟩),
    Fintype.card_sum,Fintype.card_sum,EightRowCounting.card_row,EventualRowCounting.extra_count,long_count]
  omega

theorem count_nat : Nat.card (FORecoveryCompactness.Tables Law3253 A) =
    (Fintype.card A ^ (Fintype.card A - 1) + 2 * ((Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2)) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) * Fintype.card A ^ (Fintype.card A - 3))) ^ Fintype.card A := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law3253.models_iff A ⟨f⟩)),
    Nat.card_eq_fintype_card,Fintype.card_congr EventualRowCounting.tableEquiv,Fintype.card_pi]
  simp only [row_count,Finset.prod_const,Finset.card_univ]


theorem row_lower (a : A) :
    Fintype.card A ^ (Fintype.card A - 1) + 2 * ((Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2)) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) * Fintype.card A ^ (Fintype.card A - 3)) ≤
        Fintype.card (EventualRowCounting.Row a) := by
  have hh := Fintype.card_le_of_injective (rowEncode a) (rowEncode_injective a)
  rw [Fintype.card_sum,Fintype.card_sum,EightRowCounting.card_row,EventualRowCounting.extra_count,long_count] at hh
  omega

theorem count_lower :
    (Fintype.card A ^ (Fintype.card A - 1) + 2 * ((Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2)) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) * Fintype.card A ^ (Fintype.card A - 3))) ^ Fintype.card A ≤
        Nat.card (FORecoveryCompactness.Tables Law3253 A) := by
  rw [count_nat]

theorem numerical_lower (n : ℕ) (hn : 16 ≤ n) :
    n * (3 * n ^ (n - 1)) ^ n ≤
      6 * (n ^ (n - 1) + 2 * ((n - 1) * n ^ (n - 2)) +
        (n - 1) * ((n - 2) * n ^ (n - 3))) ^ n := by
  let I := n ^ (n - 1)
  let S := I + 2 * ((n - 1) * n ^ (n - 2)) + (n - 1) * ((n - 2) * n ^ (n - 3))
  have h1 : n - 1 + 1 = n := by omega
  have h2 : n - 2 + 2 = n := by omega
  have hp1 : I = n * (n * n ^ (n - 3)) := by
    dsimp [I]; rw [← pow_succ',← pow_succ']; congr 1; omega
  have hp2 : n ^ (n - 2) = n * n ^ (n - 3) := by rw [← pow_succ']; congr 1; omega
  have hc : 7 * I ≤ 2 * S := by
    have hbase : 7 * (n * n) ≤ 2 * (n * n + 2 * ((n - 1) * n) + (n - 1) * (n - 2)) := by
      nlinarith [Nat.mul_le_mul_left n hn]
    dsimp [S]
    rw [hp1,hp2]
    nlinarith [Nat.mul_le_mul_right (n ^ (n - 3)) hbase]
  have hS : 3 * I ≤ S := by omega
  have hdiff : S - 3 * I + 3 * I = S := Nat.sub_add_cancel hS
  have hgap : 3 * I ≤ 6 * (S - 3 * I) := by omega
  have hh := CycleFourCounting.growth_bound (3 * I) (S - 3 * I) n 6 (by omega) hgap
  have he : 3 * I + (S - 3 * I) = S := by omega
  rw [he] at hh
  exact hh

theorem cardinal_lower (n : ℕ) (hn : 16 ≤ n) :
    n * Nat.card (FORecoveryCompactness.Tables Law411 (Fin n)) ≤
      6 * Nat.card (FORecoveryCompactness.Tables Law3253 (Fin n)) := by
  have h411 : Nat.card (FORecoveryCompactness.Tables Law411 (Fin n)) ≤ (3 * n ^ (n - 1)) ^ n := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law411.models_iff (Fin n) ⟨f⟩)),
      CycleFourCounting.count_nat,Fintype.card_fin]
    exact Nat.pow_le_pow_left (CycleFourCounting.numerical_upper n (by omega)) n
  exact (Nat.mul_le_mul_left n h411).trans ((numerical_lower n hn).trans
    (Nat.mul_le_mul_left 6 (by simpa only [Fintype.card_fin] using count_lower (A := Fin n))))

theorem negative : ¬ Law411.StructuralFrom Law3253 := by
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts Law3253 Law411 h
  let n := 6 * K + 16
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  have hn : 16 ≤ n := by dsimp [n]; omega
  haveI : Nonempty (FORecoveryCompactness.Tables Law411 (Fin n)) :=
    ⟨⟨fun x _ => x,(@Law411.models_iff (Fin n) ⟨fun x _ => x⟩).mpr (fun _ => rfl)⟩⟩
  have hb : n * Nat.card (FORecoveryCompactness.Tables Law411 (Fin n)) ≤
      (6 * K) * Nat.card (FORecoveryCompactness.Tables Law411 (Fin n)) := by
    calc
      _ ≤ 6 * Nat.card (FORecoveryCompactness.Tables Law3253 (Fin n)) := cardinal_lower n hn
      _ ≤ 6 * (K * Nat.card (FORecoveryCompactness.Tables Law411 (Fin n))) := Nat.mul_le_mul_left 6 (hK (Fin n))
      _ = _ := (Nat.mul_assoc _ _ _).symm
  have hh := Nat.le_of_mul_le_mul_right hb Nat.card_pos
  dsimp [n] at hh
  omega

end EventualRowExactCounting

theorem Equation411_not_StructuralFrom_Equation3253_compactness :
    ¬ Law411.StructuralFrom Law3253 := EventualRowExactCounting.negative

/-- info: 'Equation411_not_StructuralFrom_Equation3253_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation411_not_StructuralFrom_Equation3253_compactness

import equational_theories.Definability.CycleThreeCounting

/-!
# Counting square-commuting magmas

For E4470, fix the square map s. If s(a) differs from a, the row at s(a) is
determined by the row at a. An additional entry of the latter row is fixed,
leaving at most n^(n(n-2)) tables for each nonidentity s. Thus E4470 has at most
twice as many tables as idempotence. Compactness separates it from E8, E47,
E151, and E3659 on arbitrary carriers.
-/

open Law Law.MagmaLaw
namespace SquareBalancedCounting
variable {A : Type} [Fintype A] [DecidableEq A]

abbrev Fixed (s : A → A) := {f : A → A → A // (∀ x, f x x = s x) ∧ @Equation4470 A ⟨f⟩}

omit [Fintype A] [DecidableEq A] in
theorem law_eq (s : A → A) (f : Fixed s) (x y : A) : f.val x (s y) = f.val (s x) y := by
  have hh := f.property.2 x y
  change f.val x (f.val y y) = f.val (f.val x x) y at hh
  simpa only [f.property.1] using hh

abbrev Code (s : A → A) (a : A) :=
  (EightRowCounting.Outside a (s (s a)) → A) ×
    ((x : EightRowCounting.Outside a (s a)) → {y : A // y ≠ x.val} → A)

def encode (s : A → A) (a : A) (f : Fixed s) : Code s a :=
  (fun y => f.val a y.val,fun x y => f.val x.val y.val)

omit [Fintype A] in
theorem encode_injective (s : A → A) (a : A) :
    Function.Injective (encode s a) := by
  intro f g h
  have extra (f : Fixed s) : f.val a (s (s a)) = s (s a) :=
    (law_eq s f a (s a)).trans (f.property.1 (s a))
  have rowa (y : A) : f.val a y = g.val a y := by
    by_cases hy : y = a
    · subst y; exact (f.property.1 a).trans (g.property.1 a).symm
    by_cases ht' : y = s (s a)
    · subst y; exact (extra f).trans (extra g).symm
    · exact congrFun (congrArg Prod.fst h) ⟨y,by simp [hy,ht']⟩
  apply Subtype.ext
  funext x y
  by_cases hx : x = a
  · subst x; exact rowa y
  by_cases hb : x = s a
  · subst x
    exact (law_eq s f a y).symm.trans ((rowa (s y)).trans (law_eq s g a y))
  by_cases hy : y = x
  · subst y; exact (f.property.1 x).trans (g.property.1 x).symm
  · exact congrFun (congrFun (congrArg Prod.snd h) ⟨x,by simp [hx,hb]⟩) ⟨y,hy⟩

theorem code_count (s : A → A) (a : A) (ha : s a ≠ a) (ht : s (s a) ≠ a)
    (hn : 2 ≤ Fintype.card A) :
    Fintype.card (Code s a) = (Fintype.card A ^ (Fintype.card A - 2)) ^ Fintype.card A := by
  rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_pi]
  simp only [Fintype.card_fun]
  have hrow (x : EightRowCounting.Outside a (s a)) : Fintype.card {y : A // y ≠ x.val} = Fintype.card A - 1 := by
    simp [Fintype.card_subtype_compl]
  simp only [hrow,Finset.prod_const,Finset.card_univ,EightRowCounting.card_outside,
    Finset.card_pair ha.symm,Finset.card_pair ht.symm]
  rw [← pow_mul,← pow_add,← pow_mul]
  congr 1
  have hh : Fintype.card A - 1 + 1 = Fintype.card A := by omega
  nlinarith

theorem fixed_bound (s : A → A) (a : A) (ha : s a ≠ a) (hn : 2 ≤ Fintype.card A) :
    Fintype.card (Fixed s) ≤ (Fintype.card A ^ (Fintype.card A - 2)) ^ Fintype.card A := by
  by_cases ht : s (s a) = a
  · haveI : IsEmpty (Fixed s) := ⟨fun f => by
      have hh := law_eq s f a (s a)
      rw [ht,f.property.1,f.property.1,ht] at hh
      exact ha hh⟩
    simp
  · rw [← code_count s a ha ht hn]
    exact Fintype.card_le_of_injective (encode s a) (encode_injective s a)

theorem nonid_bound (s : A → A) (hs : s ≠ id) (hn : 2 ≤ Fintype.card A) :
    Fintype.card (Fixed s) ≤ (Fintype.card A ^ (Fintype.card A - 2)) ^ Fintype.card A := by
  obtain ⟨a,ha⟩ : ∃ a, s a ≠ a := by
    by_contra h
    push Not at h
    exact hs (funext h)
  exact fixed_bound s a ha hn

def idEncode (f : Fixed (id : A → A)) : {f : A → A → A // @Equation3 A ⟨f⟩} :=
  ⟨f.val,fun x => (f.property.1 x).symm⟩

theorem id_bound : Fintype.card (Fixed (id : A → A)) ≤
    (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [← EightRowCounting.count_idem]
  apply Fintype.card_le_of_injective idEncode
  intro f g h
  apply Subtype.ext
  exact congrArg (fun t : {f : A → A → A // @Equation3 A ⟨f⟩} => t.val) h

def tableEncode (f : {f : A → A → A // @Equation4470 A ⟨f⟩}) : Σ s : A → A, Fixed s :=
  ⟨fun x => f.val x x,⟨f.val,fun _ => rfl,f.property⟩⟩

omit [Fintype A] [DecidableEq A] in
theorem tableEncode_injective : Function.Injective (tableEncode (A := A)) := by
  intro f g h
  exact Subtype.ext (congrArg (fun p : Σ s : A → A, Fixed s => p.2.val) h)

theorem upper_count (hn : 2 ≤ Fintype.card A) :
    Fintype.card {f : A → A → A // @Equation4470 A ⟨f⟩} ≤
      2 * (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  let n := Fintype.card A
  let I := (n ^ (n - 1)) ^ n
  let J := (n ^ (n - 2)) ^ n
  have hJI : n ^ n * J = I := by
    dsimp [I,J]
    rw [← mul_pow,← pow_succ']
    congr 2
    omega
  calc
    _ ≤ Fintype.card (Σ s : A → A, Fixed s) := Fintype.card_le_of_injective tableEncode tableEncode_injective
    _ = Fintype.card (Fixed (id : A → A)) + ∑ s ∈ Finset.univ.erase id, Fintype.card (Fixed s) := by
      rw [Fintype.card_sigma,← Finset.add_sum_erase _ _ (Finset.mem_univ id)]
    _ ≤ I + ∑ _s ∈ Finset.univ.erase (id : A → A), J := by
      apply Nat.add_le_add id_bound
      apply Finset.sum_le_sum
      intro s hs
      exact nonid_bound s (Finset.mem_erase.mp hs).1 hn
    _ ≤ I + n ^ n * J := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      gcongr
      exact (Finset.card_erase_le).trans (by simp [n])
    _ = 2 * I := by rw [hJI]; omega

theorem upper_count_nat (hn : 2 ≤ Fintype.card A) :
    Nat.card {f : A → A → A // @Equation4470 A ⟨f⟩} ≤
      2 * (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Nat.card_eq_fintype_card]
  exact upper_count hn

theorem law_upper (hn : 2 ≤ Fintype.card A) :
    Nat.card (FORecoveryCompactness.Tables Law4470 A) ≤
      2 * (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law4470.models_iff A ⟨f⟩))]
  exact upper_count_nat hn

theorem cardinal_upper (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (FORecoveryCompactness.Tables Law4470 (Fin n)) ≤
      2 * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law3.models_iff (Fin n) ⟨f⟩)),
    EightRowCounting.count_idem_nat]
  exact law_upper (by simpa only [Fintype.card_fin] using hn)

theorem upper_profile (hn : 3 ≤ Fintype.card A) :
    Nat.card (FORecoveryCompactness.Tables Law4470 A) ≤ 4 ^ Fintype.card A *
      (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  have hp : 2 ≤ 4 ^ Fintype.card A :=
    (by decide : 2 ≤ 4 ^ 1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  exact (law_upper (by omega)).trans (Nat.mul_le_mul_right _ hp)

theorem negative_of_lower (L : NatMagmaLaw) (c : ℕ)
    (hL : ∀ n : ℕ, 4 ≤ n → n * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)) ≤
      c * Nat.card (FORecoveryCompactness.Tables L (Fin n))) : ¬ Law4470.StructuralFrom L := by
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts L Law4470 h
  let n := 2 * c * K + 4
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  have hn : 4 ≤ n := by dsimp [n]; omega
  have hb : n * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)) ≤
      (2 * c * K) * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)) := by
    calc
      _ ≤ c * Nat.card (FORecoveryCompactness.Tables L (Fin n)) := hL n hn
      _ ≤ c * (K * Nat.card (FORecoveryCompactness.Tables Law4470 (Fin n))) := Nat.mul_le_mul_left c (hK (Fin n))
      _ ≤ c * (K * (2 * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)))) :=
        Nat.mul_le_mul_left c (Nat.mul_le_mul_left K (cardinal_upper n (by omega)))
      _ = _ := by ac_rfl
  have hh := Nat.le_of_mul_le_mul_right hb (EightRowCounting.idem_count_pos n (by omega))
  dsimp [n] at hh
  omega


end SquareBalancedCounting


theorem Equation4470_not_StructuralFrom_Equation8_compactness :
    ¬ Law4470.StructuralFrom Law8 := SquareBalancedCounting.negative_of_lower Law8 1
      (by intro n hn; simpa using EightRowCounting.cardinal_bound n (by omega))

theorem Equation4470_not_StructuralFrom_Equation47_compactness :
    ¬ Law4470.StructuralFrom Law47 := SquareBalancedCounting.negative_of_lower Law47 4
      CycleThreeCounting.lower_idem

theorem Equation4470_not_StructuralFrom_Equation151_compactness :
    ¬ Law4470.StructuralFrom Law151 := DiagonalTableCounting.involution_negative_of_upper Law4470
      (by
        intro G _ _ hn
        classical
        exact SquareBalancedCounting.upper_profile hn)

theorem Equation4470_not_StructuralFrom_Equation3659_compactness :
    ¬ Law4470.StructuralFrom Law3659 := DiagonalTableCounting.retract_negative_of_upper Law4470
      (by
        intro G _ _ hn
        classical
        exact SquareBalancedCounting.upper_profile hn)

/-- info: 'Equation4470_not_StructuralFrom_Equation8_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4470_not_StructuralFrom_Equation8_compactness

/-- info: 'Equation4470_not_StructuralFrom_Equation47_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4470_not_StructuralFrom_Equation47_compactness

/-- info: 'Equation4470_not_StructuralFrom_Equation151_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4470_not_StructuralFrom_Equation151_compactness

/-- info: 'Equation4470_not_StructuralFrom_Equation3659_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4470_not_StructuralFrom_Equation3659_compactness

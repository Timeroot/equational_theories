import equational_theories.Definability.DiagonalTableCounting
import equational_theories.Definability.SquareColumnCounting

/-!
# Counting three-cycle rows

An E47 row has a fixed diagonal point or a three-cycle through it. The exact
count lies below the E8 count but has an unbounded ratio to idempotent tables.
Consequently E47 → E326 and E3253 → E47 are false FO-structurally on arbitrary
magmas. The finite variants are not refuted by these compactness arguments.
-/

open Law Law.MagmaLaw
namespace CycleThreeCounting
variable {A : Type} [Fintype A] [DecidableEq A]
abbrev Row (a : A) := {f : A → A // f (f (f a)) = a}
abbrev Fiber (a b c : A) := {f : A → A // f a = b ∧ f b = c ∧ f c = a}
abbrev Outside (a b c : A) := {z : A // z ∉ ({a,b,c} : Finset A)}
abbrev Extra (a : A) := Σ b : {b : A // b ≠ a},
  Σ c : EightRowCounting.Outside a b.val, Fiber a b.val c.val
abbrev Cases (a : A) := EightRowCounting.Fiber a a ⊕ Extra a

noncomputable def fiberEquiv (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Fiber a b c ≃ (Outside a b c → A) where
  toFun f z := f.val z.val
  invFun g := ⟨fun z => if ha : z = a then b else if hb : z = b then c
    else if hc : z = c then a else g ⟨z,by simp [ha,hb,hc]⟩,by simp [Ne.symm hab,Ne.symm hac,Ne.symm hbc]⟩
  left_inv f := by
    apply Subtype.ext
    funext z
    dsimp
    split_ifs with ha hb hc
    · subst z; exact f.property.1.symm
    · subst z; exact f.property.2.1.symm
    · subst z; exact f.property.2.2.symm
    · rfl
  right_inv g := by
    funext z
    have hz := z.property
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hz
    simp only [dif_neg hz.1,dif_neg hz.2.1,dif_neg hz.2.2]

theorem fiber_count (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Fintype.card (Fiber a b c) = Fintype.card A ^ (Fintype.card A - 3) := by
  rw [Fintype.card_congr (fiberEquiv a b c hab hac hbc),Fintype.card_fun]
  have hh := Fintype.card_subtype_compl (fun z : A => z ∈ ({a,b,c} : Finset A))
  have hc : ({a,b,c} : Finset A).card = 3 := by simp [hab,hac,hbc]
  have he : Fintype.card (Outside a b c) = Fintype.card A - 3 := by
    simpa only [Fintype.card_coe,hc] using hh
  rw [he]

theorem extra_count (a : A) : Fintype.card (Extra a) =
    (Fintype.card A - 1) * ((Fintype.card A - 2) * Fintype.card A ^ (Fintype.card A - 3)) := by
  rw [Fintype.card_sigma]
  calc
    _ = ∑ _b : {b : A // b ≠ a}, (Fintype.card A - 2) * Fintype.card A ^ (Fintype.card A - 3) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Fintype.card_sigma]
      calc
        _ = ∑ _c : EightRowCounting.Outside a b.val, Fintype.card A ^ (Fintype.card A - 3) := by
          apply Finset.sum_congr rfl
          intro c _
          have hc := c.property
          simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hc
          exact fiber_count a b.val c.val b.property.symm (Ne.symm hc.1) (Ne.symm hc.2)
        _ = _ := by
          simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
          rw [EightRowCounting.card_outside,Finset.card_pair b.property.symm]
          rfl
    _ = _ := by simp [Fintype.card_subtype_compl]

def casesMap (a : A) : Cases a → Row a
  | .inl f => ⟨f.val,by rw [f.property.1,f.property.1,f.property.1]⟩
  | .inr ⟨b,c,f⟩ => ⟨f.val,by rw [f.property.1,f.property.2.1,f.property.2.2]⟩

omit [Fintype A] in
theorem casesMap_surjective (a : A) : Function.Surjective (casesMap a) := by
  intro f
  by_cases hb : f.val a = a
  · exact ⟨.inl ⟨f.val,hb,hb⟩,rfl⟩
  have hc1 : f.val (f.val a) ≠ a := by
    intro h
    have hh := f.property
    rw [h] at hh
    exact hb hh
  have hc2 : f.val (f.val a) ≠ f.val a := by
    intro h
    have hh := f.property
    rw [h,h] at hh
    exact hb hh
  exact ⟨.inr ⟨⟨f.val a,hb⟩,⟨f.val (f.val a),by simp [hc1,hc2]⟩,
    ⟨f.val,rfl,rfl,f.property⟩⟩,rfl⟩

omit [Fintype A] in
theorem casesMap_injective (a : A) : Function.Injective (casesMap a) := by
  intro f g h
  have hv := congrArg Subtype.val h
  cases f with
  | inl f =>
    cases g with
    | inl g => exact congrArg Sum.inl (Subtype.ext hv)
    | inr g =>
      exfalso
      have he := f.property.1
      change f.val = g.2.2.val at hv
      rw [hv,g.2.2.property.1] at he
      exact g.1.property he
  | inr f =>
    cases g with
    | inl g =>
      exfalso
      have he := g.property.1
      change f.2.2.val = g.val at hv
      rw [← hv,f.2.2.property.1] at he
      exact f.1.property he
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

theorem row_count (a : A) : Fintype.card (Row a) =
    Fintype.card A ^ (Fintype.card A - 1) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) * Fintype.card A ^ (Fintype.card A - 3)) := by
  rw [← Fintype.card_congr (Equiv.ofBijective (casesMap a) ⟨casesMap_injective a,casesMap_surjective a⟩),
    Fintype.card_sum,EightRowCounting.card_fiber,EightRowCounting.card_self_pair,extra_count]

def tableEquiv : {f : A → A → A // @Equation47 A ⟨f⟩} ≃ ((a : A) → Row a) where
  toFun f a := ⟨f.val a,(f.property a).symm⟩
  invFun f := ⟨fun x y => (f x).val y,fun x => (f x).property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_nat : Nat.card {f : A → A → A // @Equation47 A ⟨f⟩} =
    (Fintype.card A ^ (Fintype.card A - 1) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) * Fintype.card A ^ (Fintype.card A - 3))) ^ Fintype.card A := by
  rw [Nat.card_eq_fintype_card,Fintype.card_congr tableEquiv,Fintype.card_pi]
  simp only [row_count,Finset.prod_const,Finset.card_univ]

theorem law_count : Nat.card (FORecoveryCompactness.Tables Law47 A) =
    (Fintype.card A ^ (Fintype.card A - 1) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) * Fintype.card A ^ (Fintype.card A - 3))) ^ Fintype.card A := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law47.models_iff A ⟨f⟩)),count_nat]

theorem numerical_upper (n : ℕ) (hn : 3 ≤ n) :
    n ^ (n - 1) + (n - 1) * ((n - 2) * n ^ (n - 3)) ≤
      n ^ (n - 1) + (n - 1) * n ^ (n - 2) := by
  gcongr
  calc
    (n - 2) * n ^ (n - 3) ≤ n * n ^ (n - 3) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = _ := by rw [← pow_succ']; congr 1; omega

theorem numerical_lower (n : ℕ) (hn : 4 ≤ n) :
    n * (n ^ (n - 1)) ^ n ≤
      4 * (n ^ (n - 1) + (n - 1) * ((n - 2) * n ^ (n - 3))) ^ n := by
  let I := n ^ (n - 1)
  let J := (n - 1) * ((n - 2) * n ^ (n - 3))
  have hI : I = n * (n * n ^ (n - 3)) := by
    dsimp [I]
    rw [← pow_succ',← pow_succ']
    congr 1
    omega
  have h4 : n * n ≤ 4 * ((n - 1) * (n - 2)) := by
    have h1 : n ≤ 2 * (n - 1) := by omega
    have h2 : n ≤ 2 * (n - 2) := by omega
    nlinarith [Nat.mul_le_mul h1 h2]
  have hJ : I ≤ 4 * J := by
    rw [hI]
    dsimp [J]
    nlinarith [Nat.mul_le_mul_right (n ^ (n - 3)) h4]
  have hp : I ^ (n - 1) * I = I ^ n := by rw [← pow_succ]; congr 1; omega
  have hb := pow_add_mul_le_add_pow (a := I) (b := J) (Nat.zero_le _) (Nat.zero_le _) n
  norm_num only [Nat.cast_id] at hb
  calc
    n * I ^ n = (n * I ^ (n - 1)) * I := by rw [Nat.mul_assoc,hp]
    _ ≤ (n * I ^ (n - 1)) * (4 * J) := Nat.mul_le_mul_left _ hJ
    _ = 4 * (n * I ^ (n - 1) * J) := by ring
    _ ≤ 4 * (I ^ n + n * I ^ (n - 1) * J) := Nat.mul_le_mul_left 4 (Nat.le_add_left _ _)
    _ ≤ 4 * (I + J) ^ n := Nat.mul_le_mul_left 4 hb

theorem upper_eight (n : ℕ) (hn : 3 ≤ n) :
    Nat.card (FORecoveryCompactness.Tables Law47 (Fin n)) ≤
      Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) := by
  rw [law_count,Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law8.models_iff (Fin n) ⟨f⟩)),
    EightRowCounting.count_eight_nat,Fintype.card_fin]
  exact Nat.pow_le_pow_left (numerical_upper n hn) n

theorem lower_idem (n : ℕ) (hn : 4 ≤ n) :
    n * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)) ≤
      4 * Nat.card (FORecoveryCompactness.Tables Law47 (Fin n)) := by
  rw [law_count,Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law3.models_iff (Fin n) ⟨f⟩)),
    EightRowCounting.count_idem_nat,Fintype.card_fin]
  exact numerical_lower n hn

theorem upper_profile (hn : 3 ≤ Fintype.card A) :
    Nat.card (FORecoveryCompactness.Tables Law47 A) ≤ 4 ^ Fintype.card A *
      (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  let n := Fintype.card A
  have hJ : (n - 1) * n ^ (n - 2) ≤ n ^ (n - 1) := by
    calc
      _ ≤ n * n ^ (n - 2) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = _ := by rw [← pow_succ']; congr 1; omega
  have hR : n ^ (n - 1) + (n - 1) * n ^ (n - 2) ≤ 4 * n ^ (n - 1) := by omega
  rw [law_count,← mul_pow]
  exact Nat.pow_le_pow_left ((numerical_upper n hn).trans hR) n


theorem negative_to_326 : ¬ Law326.StructuralFrom Law47 := by
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts Law47 Law326 h
  let n := 8 * K + 4
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  have hn : 4 ≤ n := by dsimp [n]; omega
  have hb : n * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)) ≤
      (8 * K) * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)) := by
    calc
      _ ≤ 4 * Nat.card (FORecoveryCompactness.Tables Law47 (Fin n)) := lower_idem n hn
      _ ≤ 4 * (K * Nat.card (FORecoveryCompactness.Tables Law326 (Fin n))) := Nat.mul_le_mul_left 4 (hK (Fin n))
      _ ≤ 4 * (K * (2 * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)))) :=
        Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left K (SquareColumnCounting.cardinal_bound n (by omega)))
      _ = _ := by ac_rfl
  have hh := Nat.le_of_mul_le_mul_right hb (EightRowCounting.idem_count_pos n (by omega))
  dsimp [n] at hh
  omega

theorem negative_from_3253 : ¬ Law47.StructuralFrom Law3253 := by
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts Law3253 Law47 h
  let n := 3 * K + 4
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  have hn : 4 ≤ n := by dsimp [n]; omega
  have hp : 0 < Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) :=
    lt_of_lt_of_le (Nat.mul_pos (by omega) (EightRowCounting.idem_count_pos n (by omega)))
      (EightRowCounting.cardinal_bound n (by omega))
  have hb : n * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) ≤
      (3 * K) * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) := by
    calc
      _ ≤ 3 * Nat.card (FORecoveryCompactness.Tables Law3253 (Fin n)) := EventualRowCounting.cardinal_bound n (by omega)
      _ ≤ 3 * (K * Nat.card (FORecoveryCompactness.Tables Law47 (Fin n))) := Nat.mul_le_mul_left 3 (hK (Fin n))
      _ ≤ 3 * (K * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n))) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left K (upper_eight n (by omega)))
      _ = _ := (Nat.mul_assoc _ _ _).symm
  have hh := Nat.le_of_mul_le_mul_right hb hp
  dsimp [n] at hh
  omega


end CycleThreeCounting


theorem Equation326_not_StructuralFrom_Equation47_compactness :
    ¬ Law326.StructuralFrom Law47 := CycleThreeCounting.negative_to_326

theorem Equation47_not_StructuralFrom_Equation3253_compactness :
    ¬ Law47.StructuralFrom Law3253 := CycleThreeCounting.negative_from_3253

/-- info: 'Equation326_not_StructuralFrom_Equation47_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation326_not_StructuralFrom_Equation47_compactness

/-- info: 'Equation47_not_StructuralFrom_Equation3253_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation47_not_StructuralFrom_Equation3253_compactness


theorem Equation47_not_StructuralFrom_Equation151_compactness :
    ¬ Law47.StructuralFrom Law151 := DiagonalTableCounting.involution_negative_of_upper Law47
      (by
        intro G _ _ hn
        classical
        exact CycleThreeCounting.upper_profile hn)

theorem Equation47_not_StructuralFrom_Equation3659_compactness :
    ¬ Law47.StructuralFrom Law3659 := DiagonalTableCounting.retract_negative_of_upper Law47
      (by
        intro G _ _ hn
        classical
        exact CycleThreeCounting.upper_profile hn)

/-- info: 'Equation47_not_StructuralFrom_Equation151_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation47_not_StructuralFrom_Equation151_compactness

/-- info: 'Equation47_not_StructuralFrom_Equation3659_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation47_not_StructuralFrom_Equation3659_compactness

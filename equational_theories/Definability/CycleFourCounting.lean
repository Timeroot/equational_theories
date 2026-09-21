import equational_theories.Definability.CycleThreeCounting

/-!
# Counting four-cycle rows

E411 rows have cycles of length one, two, or four through the diagonal point.
Their exact counts dominate E8 and E47 by an unbounded factor across tables.
The shared diagonal-family bounds separate E151 and E3659 from E411 as well.
All four conclusions concern unrestricted FO-structural interpretation.
-/

open Law Law.MagmaLaw
namespace CycleFourCounting
variable {A : Type} [Fintype A] [DecidableEq A]
abbrev Row (a : A) := {f : A → A // f (f (f (f a))) = a}
abbrev Fiber (a b c d : A) := {f : A → A // f a = b ∧ f b = c ∧ f c = d ∧ f d = a}
abbrev Outside (a b c d : A) := {z : A // z ∉ ({a,b,c,d} : Finset A)}
abbrev Extra (a : A) := Σ b : {b : A // b ≠ a},
  Σ c : EightRowCounting.Outside a b.val,
  Σ d : CycleThreeCounting.Outside a b.val c.val, Fiber a b.val c.val d.val
abbrev Cases (a : A) := EightRowCounting.Row8 a ⊕ Extra a

noncomputable def fiberEquiv (a b c d : A) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Fiber a b c d ≃ (Outside a b c d → A) where
  toFun f z := f.val z.val
  invFun g := ⟨fun z => if ha : z = a then b else if hb : z = b then c
    else if hc : z = c then d else if hd : z = d then a
    else g ⟨z,by simp [ha,hb,hc,hd]⟩,
    by simp [Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]⟩
  left_inv f := by
    apply Subtype.ext
    funext z
    dsimp
    split_ifs with ha hb hc hd
    · subst z; exact f.property.1.symm
    · subst z; exact f.property.2.1.symm
    · subst z; exact f.property.2.2.1.symm
    · subst z; exact f.property.2.2.2.symm
    · rfl
  right_inv g := by
    funext z
    have hz := z.property
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hz
    simp only [dif_neg hz.1,dif_neg hz.2.1,dif_neg hz.2.2.1,dif_neg hz.2.2.2]

theorem fiber_count (a b c d : A) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Fintype.card (Fiber a b c d) = Fintype.card A ^ (Fintype.card A - 4) := by
  rw [Fintype.card_congr (fiberEquiv a b c d hab hac had hbc hbd hcd),Fintype.card_fun]
  have hh := Fintype.card_subtype_compl (fun z : A => z ∈ ({a,b,c,d} : Finset A))
  have hc : ({a,b,c,d} : Finset A).card = 4 := by simp [hab,hac,had,hbc,hbd,hcd]
  have he : Fintype.card (Outside a b c d) = Fintype.card A - 4 := by
    simpa only [Fintype.card_coe,hc] using hh
  rw [he]

theorem card_outside_three (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Fintype.card (CycleThreeCounting.Outside a b c) = Fintype.card A - 3 := by
  have hh := Fintype.card_subtype_compl (fun z : A => z ∈ ({a,b,c} : Finset A))
  have hc : ({a,b,c} : Finset A).card = 3 := by simp [hab,hac,hbc]
  simpa only [Fintype.card_coe,hc] using hh

theorem extra_count (a : A) : Fintype.card (Extra a) =
    (Fintype.card A - 1) * ((Fintype.card A - 2) *
      ((Fintype.card A - 3) * Fintype.card A ^ (Fintype.card A - 4))) := by
  rw [Fintype.card_sigma]
  calc
    _ = ∑ _b : {b : A // b ≠ a}, (Fintype.card A - 2) *
      ((Fintype.card A - 3) * Fintype.card A ^ (Fintype.card A - 4)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Fintype.card_sigma]
      calc
        _ = ∑ _c : EightRowCounting.Outside a b.val,
          (Fintype.card A - 3) * Fintype.card A ^ (Fintype.card A - 4) := by
          apply Finset.sum_congr rfl
          intro c _
          have hc := c.property
          simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hc
          rw [Fintype.card_sigma]
          calc
            _ = ∑ _d : CycleThreeCounting.Outside a b.val c.val, Fintype.card A ^ (Fintype.card A - 4) := by
              apply Finset.sum_congr rfl
              intro d _
              have hd := d.property
              simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hd
              exact fiber_count a b.val c.val d.val b.property.symm (Ne.symm hc.1)
                (Ne.symm hd.1) (Ne.symm hc.2) (Ne.symm hd.2.1) (Ne.symm hd.2.2)
            _ = _ := by
              simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
              rw [card_outside_three a b.val c.val b.property.symm (Ne.symm hc.1) (Ne.symm hc.2)]
              rfl
        _ = _ := by
          simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
          rw [EightRowCounting.card_outside,Finset.card_pair b.property.symm]
          rfl
    _ = _ := by simp [Fintype.card_subtype_compl]

def casesMap (a : A) : Cases a → Row a
  | .inl f => ⟨f.val,by rw [f.property,f.property]⟩
  | .inr ⟨b,c,d,f⟩ => ⟨f.val,by rw [f.property.1,f.property.2.1,f.property.2.2.1,f.property.2.2.2]⟩

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
      have he := f.property
      change f.val = g.2.2.2.val at hv
      rw [hv,g.2.2.2.property.1,g.2.2.2.property.2.1] at he
      have hc := g.2.1.property
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hc
      exact hc.1 he
  | inr f =>
    cases g with
    | inl g =>
      exfalso
      have he := g.property
      change f.2.2.2.val = g.val at hv
      rw [← hv,f.2.2.2.property.1,f.2.2.2.property.2.1] at he
      have hc := f.2.1.property
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hc
      exact hc.1 he
    | inr g =>
      congr 1
      rcases f with ⟨⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩,f⟩
      rcases g with ⟨⟨b',hb'⟩,⟨c',hc'⟩,⟨d',hd'⟩,g⟩
      change f.val = g.val at hv
      have hbb : b = b' := f.property.1.symm.trans ((congrFun hv a).trans g.property.1)
      subst b'
      have hcc : c = c' := f.property.2.1.symm.trans ((congrFun hv b).trans g.property.2.1)
      subst c'
      have hdd : d = d' := f.property.2.2.1.symm.trans ((congrFun hv c).trans g.property.2.2.1)
      subst d'
      congr 3
      exact Subtype.ext hv

omit [Fintype A] in
theorem casesMap_surjective (a : A) : Function.Surjective (casesMap a) := by
  intro f
  by_cases ha : f.val (f.val a) = a
  · exact ⟨.inl ⟨f.val,ha⟩,rfl⟩
  have hb : f.val a ≠ a := by
    intro h
    apply ha
    rw [h,h]
  have hc : f.val (f.val a) ≠ f.val a := by
    intro h
    have hh := f.property
    simp only [h] at hh
    exact hb hh
  have hd1 : f.val (f.val (f.val a)) ≠ a := by
    intro h
    have hh := f.property
    rw [h] at hh
    exact hb hh
  have hd2 : f.val (f.val (f.val a)) ≠ f.val a := by
    intro h
    have hh := f.property
    rw [h] at hh
    exact ha hh
  have hd3 : f.val (f.val (f.val a)) ≠ f.val (f.val a) := by
    intro h
    have hh := f.property
    simp only [h] at hh
    exact ha hh
  exact ⟨.inr ⟨⟨f.val a,hb⟩,⟨f.val (f.val a),by simp [ha,hc]⟩,
    ⟨f.val (f.val (f.val a)),by simp [hd1,hd2,hd3]⟩,⟨f.val,rfl,rfl,rfl,f.property⟩⟩,rfl⟩

theorem row_count (a : A) : Fintype.card (Row a) =
    (Fintype.card A ^ (Fintype.card A - 1) + (Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2)) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) *
        ((Fintype.card A - 3) * Fintype.card A ^ (Fintype.card A - 4))) := by
  rw [← Fintype.card_congr (Equiv.ofBijective (casesMap a) ⟨casesMap_injective a,casesMap_surjective a⟩),
    Fintype.card_sum,EightRowCounting.card_row,extra_count]


theorem row_lower (a : A) :
    (Fintype.card A ^ (Fintype.card A - 1) + (Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2)) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) *
        ((Fintype.card A - 3) * Fintype.card A ^ (Fintype.card A - 4))) ≤ Fintype.card (Row a) := by
  have hh := Fintype.card_le_of_injective (casesMap a) (casesMap_injective a)
  simpa only [Fintype.card_sum,EightRowCounting.card_row,extra_count] using hh

def tableEquiv : {f : A → A → A // @Equation411 A ⟨f⟩} ≃ ((a : A) → Row a) where
  toFun f a := ⟨f.val a,(f.property a).symm⟩
  invFun f := ⟨fun x y => (f x).val y,fun x => (f x).property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_nat : Nat.card {f : A → A → A // @Equation411 A ⟨f⟩} =
    ((Fintype.card A ^ (Fintype.card A - 1) + (Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2)) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) *
        ((Fintype.card A - 3) * Fintype.card A ^ (Fintype.card A - 4)))) ^ Fintype.card A := by
  rw [Nat.card_eq_fintype_card,Fintype.card_congr tableEquiv,Fintype.card_pi]
  simp only [row_count,Finset.prod_const,Finset.card_univ]

theorem numerical_upper (n : ℕ) (hn : 4 ≤ n) :
    (n ^ (n - 1) + (n - 1) * n ^ (n - 2)) +
      (n - 1) * ((n - 2) * ((n - 3) * n ^ (n - 4))) ≤ 3 * n ^ (n - 1) := by
  have hI : n ^ (n - 1) = n * (n * (n * n ^ (n - 4))) := by
    rw [← pow_succ',← pow_succ',← pow_succ']; congr 1; omega
  have hR : (n - 1) * n ^ (n - 2) ≤ n ^ (n - 1) := by
    calc
      _ ≤ n * n ^ (n - 2) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = _ := by rw [← pow_succ']; congr 1; omega
  have hp := Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le n 1) (Nat.sub_le n 2)) (Nat.sub_le n 3)
  have hJ : (n - 1) * ((n - 2) * ((n - 3) * n ^ (n - 4))) ≤ n ^ (n - 1) := by
    rw [hI]
    nlinarith [Nat.mul_le_mul_right (n ^ (n - 4)) hp]
  omega

theorem upper_profile (hn : 3 ≤ Fintype.card A) :
    Nat.card (FORecoveryCompactness.Tables Law411 A) ≤ 4 ^ Fintype.card A *
      (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law411.models_iff A ⟨f⟩)),count_nat,← mul_pow]
  by_cases h4 : 4 ≤ Fintype.card A
  · exact Nat.pow_le_pow_left ((numerical_upper _ h4).trans (Nat.mul_le_mul_right _ (by decide))) _
  · have he : Fintype.card A = 3 := by omega
    rw [he]
    norm_num


theorem count_lower :
    ((Fintype.card A ^ (Fintype.card A - 1) + (Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2)) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) *
        ((Fintype.card A - 3) * Fintype.card A ^ (Fintype.card A - 4)))) ^ Fintype.card A ≤
          Nat.card {f : A → A → A // @Equation411 A ⟨f⟩} := by
  rw [Nat.card_eq_fintype_card,Fintype.card_congr tableEquiv,Fintype.card_pi]
  calc
    _ = ∏ _a : A, ((Fintype.card A ^ (Fintype.card A - 1) + (Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2)) +
      (Fintype.card A - 1) * ((Fintype.card A - 2) *
        ((Fintype.card A - 3) * Fintype.card A ^ (Fintype.card A - 4)))) := by simp
    _ ≤ _ := Finset.prod_le_prod (by intros; omega) (fun a _ => row_lower a)

theorem growth_bound (I J n c : ℕ) (hn : 0 < n) (hc : I ≤ c * J) :
    n * I ^ n ≤ c * (I + J) ^ n := by
  have hp : I ^ (n - 1) * I = I ^ n := by rw [← pow_succ]; congr 1; omega
  have hb := pow_add_mul_le_add_pow (a := I) (b := J) (Nat.zero_le _) (Nat.zero_le _) n
  norm_num only [Nat.cast_id] at hb
  calc
    n * I ^ n = (n * I ^ (n - 1)) * I := by rw [Nat.mul_assoc,hp]
    _ ≤ (n * I ^ (n - 1)) * (c * J) := Nat.mul_le_mul_left _ hc
    _ = c * (n * I ^ (n - 1) * J) := by ring
    _ ≤ c * (I ^ n + n * I ^ (n - 1) * J) := Nat.mul_le_mul_left c (Nat.le_add_left _ _)
    _ ≤ c * (I + J) ^ n := Nat.mul_le_mul_left c hb

theorem numerical_lower (n : ℕ) (hn : 6 ≤ n) :
    n * (n ^ (n - 1) + (n - 1) * n ^ (n - 2)) ^ n ≤
      16 * ((n ^ (n - 1) + (n - 1) * n ^ (n - 2)) +
        (n - 1) * ((n - 2) * ((n - 3) * n ^ (n - 4)))) ^ n := by
  let I := n ^ (n - 1)
  let R := I + (n - 1) * n ^ (n - 2)
  let J := (n - 1) * ((n - 2) * ((n - 3) * n ^ (n - 4)))
  have hI : I = n * (n * (n * n ^ (n - 4))) := by
    dsimp [I]
    rw [← pow_succ',← pow_succ',← pow_succ']
    congr 1
    omega
  have h8 : n * n * n ≤ 8 * ((n - 1) * (n - 2) * (n - 3)) := by
    have h1 : n ≤ 2 * (n - 1) := by omega
    have h2 : n ≤ 2 * (n - 2) := by omega
    have h3 : n ≤ 2 * (n - 3) := by omega
    nlinarith [Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3]
  have hIJ : I ≤ 8 * J := by
    rw [hI]
    dsimp [J]
    nlinarith [Nat.mul_le_mul_right (n ^ (n - 4)) h8]
  have hR : R ≤ 2 * I := by
    have he : n * n ^ (n - 2) = I := by dsimp [I]; rw [← pow_succ']; congr 1; omega
    have hh := Nat.mul_le_mul_right (n ^ (n - 2)) (Nat.sub_le n 1)
    rw [he] at hh
    dsimp [R]
    omega
  have hc : R ≤ 16 * J := by omega
  exact growth_bound R J n 16 (by omega) hc

theorem cardinal_lower (n : ℕ) (hn : 6 ≤ n) :
    n * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) ≤
      16 * Nat.card (FORecoveryCompactness.Tables Law411 (Fin n)) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law8.models_iff (Fin n) ⟨f⟩)),
    EightRowCounting.count_eight_nat,Fintype.card_fin,
    Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law411.models_iff (Fin n) ⟨f⟩))]
  exact (numerical_lower n hn).trans (Nat.mul_le_mul_left 16
    (by simpa only [Fintype.card_fin] using count_lower (A := Fin n)))

theorem negative_of_count_le (B : NatMagmaLaw)
    (hB : ∀ n : ℕ, 6 ≤ n → Nat.card (FORecoveryCompactness.Tables B (Fin n)) ≤
      Nat.card (FORecoveryCompactness.Tables Law8 (Fin n))) : ¬ B.StructuralFrom Law411 := by
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts Law411 B h
  let n := 16 * K + 6
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  have hn : 6 ≤ n := by dsimp [n]; omega
  have hp : 0 < Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) :=
    lt_of_lt_of_le (Nat.mul_pos (by omega) (EightRowCounting.idem_count_pos n (by omega)))
      (EightRowCounting.cardinal_bound n (by omega))
  have hb : n * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) ≤
      (16 * K) * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) := by
    calc
      _ ≤ 16 * Nat.card (FORecoveryCompactness.Tables Law411 (Fin n)) := cardinal_lower n hn
      _ ≤ 16 * (K * Nat.card (FORecoveryCompactness.Tables B (Fin n))) := Nat.mul_le_mul_left 16 (hK (Fin n))
      _ ≤ 16 * (K * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n))) := Nat.mul_le_mul_left 16 (Nat.mul_le_mul_left K (hB n hn))
      _ = _ := (Nat.mul_assoc _ _ _).symm
  have hh := Nat.le_of_mul_le_mul_right hb hp
  dsimp [n] at hh
  omega


end CycleFourCounting


theorem Equation8_not_StructuralFrom_Equation411_compactness :
    ¬ Law8.StructuralFrom Law411 := CycleFourCounting.negative_of_count_le Law8 (fun _ _ => le_rfl)

theorem Equation47_not_StructuralFrom_Equation411_compactness :
    ¬ Law47.StructuralFrom Law411 := CycleFourCounting.negative_of_count_le Law47
      (fun n hn => CycleThreeCounting.upper_eight n (by omega))

/-- info: 'Equation8_not_StructuralFrom_Equation411_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation8_not_StructuralFrom_Equation411_compactness

/-- info: 'Equation47_not_StructuralFrom_Equation411_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation47_not_StructuralFrom_Equation411_compactness


theorem Equation411_not_StructuralFrom_Equation151_compactness :
    ¬ Law411.StructuralFrom Law151 := DiagonalTableCounting.involution_negative_of_upper Law411
      (by
        intro G _ _ hn
        classical
        exact CycleFourCounting.upper_profile hn)

theorem Equation411_not_StructuralFrom_Equation3659_compactness :
    ¬ Law411.StructuralFrom Law3659 := DiagonalTableCounting.retract_negative_of_upper Law411
      (by
        intro G _ _ hn
        classical
        exact CycleFourCounting.upper_profile hn)

/-- info: 'Equation411_not_StructuralFrom_Equation151_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation411_not_StructuralFrom_Equation151_compactness

/-- info: 'Equation411_not_StructuralFrom_Equation3659_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation411_not_StructuralFrom_Equation3659_compactness

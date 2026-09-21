import equational_theories.Definability.EventualRowExactCounting
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-!
# Counting magmas invariant under the left cube

Collapsing a repeated pair of columns reduces each row to a function on n-1
points. Prescribing the value of its second iterate leaves at most
2 n^(n-2) rows. Splitting according to the left-cube map gives
N_3319(n) ≤ 2 (2 n^(n-1))^n ≤ 4 N_8(n).

Compactness separates E3253, E411, E151, and E3659 from E3319 on arbitrary
carriers. The point-constraint counting lemma is shared infrastructure.
-/

namespace PointConstraintCounting
variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
abbrev One (u : X) (v : Y) := {f : X → Y // f u = v}
abbrev Two (u w : X) (v z : Y) := {f : X → Y // f u = v ∧ f w = z}

noncomputable def oneEquiv (u : X) (v : Y) : One u v ≃ ({x : X // x ≠ u} → Y) where
  toFun f x := f.val x.val
  invFun g := ⟨fun x => if h : x = u then v else g ⟨x,h⟩,by simp⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    dsimp
    split_ifs with h
    · subst x; exact f.property.symm
    · rfl
  right_inv g := by funext x; simp only [dif_neg x.property]

theorem one_count (u : X) (v : Y) : Fintype.card (One u v) = Fintype.card Y ^ (Fintype.card X - 1) := by
  rw [Fintype.card_congr (oneEquiv u v),Fintype.card_fun]
  simp [Fintype.card_subtype_compl]

noncomputable def twoEquiv (u w : X) (v z : Y) (huw : u ≠ w) :
    Two u w v z ≃ ({x : X // x ∉ ({u,w} : Finset X)} → Y) where
  toFun f x := f.val x.val
  invFun g := ⟨fun x => if h : x = u then v else if h' : x = w then z
    else g ⟨x,by simp [h,h']⟩,by simp [huw.symm]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    dsimp
    split_ifs with h h'
    · subst x; exact f.property.1.symm
    · subst x; exact f.property.2.symm
    · rfl
  right_inv g := by
    funext x
    have hx := x.property
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hx
    simp only [dif_neg hx.1,dif_neg hx.2]

theorem two_count (u w : X) (v z : Y) (huw : u ≠ w) :
    Fintype.card (Two u w v z) = Fintype.card Y ^ (Fintype.card X - 2) := by
  rw [Fintype.card_congr (twoEquiv u w v z huw),Fintype.card_fun]
  have hh := Fintype.card_subtype_compl (fun x : X => x ∈ ({u,w} : Finset X))
  have he : Fintype.card {x : X // x ∉ ({u,w} : Finset X)} = Fintype.card X - 2 := by
    simpa only [Fintype.card_coe,Finset.card_pair huw] using hh
  rw [he]

abbrev Constraint (p : Y → X) (u : X) (v : Y) := {f : X → Y // f (p (f u)) = v}
abbrev Code (p : Y → X) (u : X) (v : Y) := One u v ⊕ Σ d : {d : Y // d ≠ v}, Two u (p d.val) d.val v

def encode (p : Y → X) (u : X) (v : Y) (f : Constraint p u v) : Code p u v :=
  if h : f.val u = v then .inl ⟨f.val,h⟩ else .inr ⟨⟨f.val u,h⟩,⟨f.val,rfl,f.property⟩⟩

def decode (p : Y → X) (u : X) (v : Y) : Code p u v → (X → Y)
  | .inl f => f.val
  | .inr ⟨_,f⟩ => f.val

omit [Fintype X] [Fintype Y] [DecidableEq X] in
theorem decode_encode (p : Y → X) (u : X) (v : Y) (f : Constraint p u v) :
    decode p u v (encode p u v f) = f.val := by
  unfold encode
  split_ifs <;> rfl

omit [Fintype X] [Fintype Y] [DecidableEq X] in
theorem encode_injective (p : Y → X) (u : X) (v : Y) : Function.Injective (encode p u v) := by
  intro f g h
  apply Subtype.ext
  simpa only [decode_encode] using congrArg (decode p u v) h

theorem two_bound (p : Y → X) (u : X) (v : Y) (d : {d : Y // d ≠ v}) :
    Fintype.card (Two u (p d.val) d.val v) ≤ Fintype.card Y ^ (Fintype.card X - 2) := by
  by_cases h : u = p d.val
  · haveI : IsEmpty (Two u (p d.val) d.val v) := ⟨fun f => d.property (f.property.1.symm.trans (h ▸ f.property.2))⟩
    simp
  · exact le_of_eq (two_count u (p d.val) d.val v h)

theorem upper_count (p : Y → X) (u : X) (v : Y) (hX : 2 ≤ Fintype.card X) :
    Fintype.card (Constraint p u v) ≤ 2 * Fintype.card Y ^ (Fintype.card X - 1) := by
  have he : Fintype.card Y * Fintype.card Y ^ (Fintype.card X - 2) =
      Fintype.card Y ^ (Fintype.card X - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  calc
    _ ≤ Fintype.card (Code p u v) := Fintype.card_le_of_injective (encode p u v) (encode_injective p u v)
    _ = Fintype.card Y ^ (Fintype.card X - 1) + ∑ d : {d : Y // d ≠ v}, Fintype.card (Two u (p d.val) d.val v) := by
      rw [Fintype.card_sum,one_count,Fintype.card_sigma]
    _ ≤ Fintype.card Y ^ (Fintype.card X - 1) + ∑ _d : {d : Y // d ≠ v}, Fintype.card Y ^ (Fintype.card X - 2) := by
      apply Nat.add_le_add_left
      exact Finset.sum_le_sum (fun d _ => two_bound p u v d)
    _ ≤ Fintype.card Y ^ (Fintype.card X - 1) + Fintype.card Y * Fintype.card Y ^ (Fintype.card X - 2) := by
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
      apply Nat.add_le_add_left
      exact Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)
    _ = _ := by rw [he]; omega

end PointConstraintCounting


open Law Law.MagmaLaw
namespace LeftCubeColumnCounting
variable {A : Type} [Fintype A] [DecidableEq A]

abbrev Quot (b : A) := {y : A // y ≠ b}
def project (a b : A) (hab : a ≠ b) (y : A) : Quot b :=
  if h : y = b then ⟨a,hab⟩ else ⟨y,h⟩
abbrev Row (a b x v : A) := {f : A → A // f a = f b ∧ f (f x) = v}

omit [Fintype A] in
theorem realize_project (a b x v : A) (hab : a ≠ b) (f : Row a b x v) (y : A) :
    f.val (project a b hab y).val = f.val y := by
  unfold project
  split_ifs with h
  · subst y; exact f.property.1
  · rfl

def rowEncode (a b x v : A) (hab : a ≠ b) (f : Row a b x v) :
    PointConstraintCounting.Constraint (project a b hab) (project a b hab x) v :=
  ⟨fun q => f.val q.val,by
    change f.val (project a b hab (f.val (project a b hab x).val)).val = v
    rw [realize_project a b x v hab f x,realize_project a b x v hab f (f.val x)]
    exact f.property.2⟩

omit [Fintype A] in
theorem rowEncode_injective (a b x v : A) (hab : a ≠ b) : Function.Injective (rowEncode a b x v hab) := by
  intro f g h
  have hh := congrArg Subtype.val h
  apply Subtype.ext
  funext y
  exact (realize_project a b x v hab f y).symm.trans
    ((congrFun hh (project a b hab y)).trans (realize_project a b x v hab g y))

theorem row_bound (a b x v : A) (hab : a ≠ b) (hn : 3 ≤ Fintype.card A) :
    Fintype.card (Row a b x v) ≤ 2 * Fintype.card A ^ (Fintype.card A - 2) := by
  have hc : Fintype.card (Quot b) = Fintype.card A - 1 := by simp [Quot,Fintype.card_subtype_compl]
  calc
    _ ≤ Fintype.card (PointConstraintCounting.Constraint (project a b hab) (project a b hab x) v) :=
      Fintype.card_le_of_injective (rowEncode a b x v hab) (rowEncode_injective a b x v hab)
    _ ≤ 2 * Fintype.card A ^ (Fintype.card (Quot b) - 1) :=
      PointConstraintCounting.upper_count _ _ _ (by rw [hc]; omega)
    _ = _ := by rw [hc,Nat.sub_sub]

abbrev Fixed (c : A → A) := {f : A → A → A // (∀ x, f x (f x x) = c x) ∧ @Equation3319 A ⟨f⟩}

def fixedEncode (c : A → A) (a : A) (f : Fixed c) : (x : A) → Row a (c a) x (c x) :=
  fun x => ⟨f.val x,by
    have hh := f.property.2 x a
    change f.val x a = f.val x (f.val a (f.val a a)) at hh
    exact ⟨by simpa only [f.property.1] using hh,f.property.1 x⟩⟩

omit [Fintype A] [DecidableEq A] in
theorem fixedEncode_injective (c : A → A) (a : A) : Function.Injective (fixedEncode c a) := by
  intro f g h
  apply Subtype.ext
  funext x y
  exact congrFun (congrArg Subtype.val (congrFun h x)) y

theorem fixed_bound (c : A → A) (hc : c ≠ id) (hn : 3 ≤ Fintype.card A) :
    Fintype.card (Fixed c) ≤ (2 * Fintype.card A ^ (Fintype.card A - 2)) ^ Fintype.card A := by
  obtain ⟨a,ha⟩ : ∃ a, c a ≠ a := by
    by_contra h
    push Not at h
    exact hc (funext h)
  calc
    _ ≤ Fintype.card ((x : A) → Row a (c a) x (c x)) :=
      Fintype.card_le_of_injective (fixedEncode c a) (fixedEncode_injective c a)
    _ = ∏ x : A, Fintype.card (Row a (c a) x (c x)) := Fintype.card_pi
    _ ≤ ∏ _x : A, 2 * Fintype.card A ^ (Fintype.card A - 2) :=
      Finset.prod_le_prod (by intros; omega) (fun x _ => row_bound a (c a) x (c x) ha.symm hn)
    _ = _ := by simp

def idEncode (f : Fixed (id : A → A)) : {f : A → A → A // @Equation8 A ⟨f⟩} :=
  ⟨f.val,fun x => (f.property.1 x).symm⟩

theorem id_bound (hn : 3 ≤ Fintype.card A) : Fintype.card (Fixed (id : A → A)) ≤
    (2 * Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  have hh : Fintype.card (Fixed (id : A → A)) ≤ Fintype.card {f : A → A → A // @Equation8 A ⟨f⟩} := by
    apply Fintype.card_le_of_injective idEncode
    intro f g h
    apply Subtype.ext
    exact congrArg (fun t : {f : A → A → A // @Equation8 A ⟨f⟩} => t.val) h
  rw [EightRowCounting.count_eight] at hh
  apply hh.trans
  apply Nat.pow_le_pow_left
  have hp : Fintype.card A * Fintype.card A ^ (Fintype.card A - 2) = Fintype.card A ^ (Fintype.card A - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hle := Nat.mul_le_mul_right (Fintype.card A ^ (Fintype.card A - 2)) (Nat.sub_le (Fintype.card A) 1)
  rw [hp] at hle
  omega

def tableEncode (f : {f : A → A → A // @Equation3319 A ⟨f⟩}) : Σ c : A → A, Fixed c :=
  ⟨fun x => f.val x (f.val x x),⟨f.val,fun _ => rfl,f.property⟩⟩

omit [Fintype A] [DecidableEq A] in
theorem tableEncode_injective : Function.Injective (tableEncode (A := A)) := by
  intro f g h
  exact Subtype.ext (congrArg (fun p : Σ c : A → A, Fixed c => p.2.val) h)

theorem upper_count (hn : 3 ≤ Fintype.card A) :
    Fintype.card {f : A → A → A // @Equation3319 A ⟨f⟩} ≤
      2 * (2 * Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  let n := Fintype.card A
  let T := (2 * n ^ (n - 1)) ^ n
  let J := (2 * n ^ (n - 2)) ^ n
  have hp : n ^ (n - 1) = n * n ^ (n - 2) := by rw [← pow_succ']; congr 1; omega
  have hJT : n ^ n * J = T := by
    dsimp [J,T]
    rw [← mul_pow,hp]
    congr 1
    ring
  calc
    _ ≤ Fintype.card (Σ c : A → A, Fixed c) := Fintype.card_le_of_injective tableEncode tableEncode_injective
    _ = Fintype.card (Fixed (id : A → A)) + ∑ c ∈ Finset.univ.erase id, Fintype.card (Fixed c) := by
      rw [Fintype.card_sigma,← Finset.add_sum_erase _ _ (Finset.mem_univ id)]
    _ ≤ T + ∑ _c ∈ Finset.univ.erase (id : A → A), J := by
      apply Nat.add_le_add (id_bound hn)
      exact Finset.sum_le_sum (fun c hc => fixed_bound c (Finset.mem_erase.mp hc).1 hn)
    _ ≤ T + n ^ n * J := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      gcongr
      exact (Finset.card_erase_le).trans (by simp [n])
    _ = 2 * T := by rw [hJT]; omega

theorem upper_count_nat (hn : 3 ≤ Fintype.card A) :
    Nat.card {f : A → A → A // @Equation3319 A ⟨f⟩} ≤
      2 * (2 * Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Nat.card_eq_fintype_card]
  exact upper_count hn

theorem law_upper (hn : 3 ≤ Fintype.card A) :
    Nat.card (FORecoveryCompactness.Tables Law3319 A) ≤
      2 * (2 * Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law3319.models_iff A ⟨f⟩))]
  exact upper_count_nat hn

theorem upper_profile (hn : 3 ≤ Fintype.card A) :
    Nat.card (FORecoveryCompactness.Tables Law3319 A) ≤ 4 ^ Fintype.card A *
      (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  have hp : 2 ≤ 2 ^ Fintype.card A :=
    (by decide : 2 ≤ 2 ^ 1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hc : 2 * 2 ^ Fintype.card A ≤ 4 ^ Fintype.card A := by
    calc
      _ ≤ 2 ^ Fintype.card A * 2 ^ Fintype.card A := Nat.mul_le_mul_right _ hp
      _ = _ := by rw [← mul_pow]; rfl
  have hh := law_upper hn
  rw [mul_pow,← Nat.mul_assoc] at hh
  exact hh.trans (Nat.mul_le_mul_right _ hc)

theorem double_bound (n : ℕ) (hn : 2 ≤ n) :
    (2 * n ^ (n - 1)) ^ n ≤ 2 * (n ^ (n - 1) + (n - 1) * n ^ (n - 2)) ^ n := by
  let I := n ^ (n - 1)
  let m := n ^ (n - 2)
  let R := I + (n - 1) * m
  have hI : I = n * m := by dsimp [I,m]; rw [← pow_succ']; congr 1; omega
  have hIc : (I : ℤ) = (n : ℤ) * m := by exact_mod_cast hI
  have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hR : (R : ℤ) = 2 * (I : ℤ) - m := by
    dsimp [R]
    rw [hsub]
    nlinarith [hIc]
  have hIm : m ≤ I := by
    rw [hI]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hImc : (m : ℤ) ≤ I := by exact_mod_cast hIm
  have hp : (2 * (I : ℤ)) ^ (n - 1) * (2 * I) = (2 * (I : ℤ)) ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have he : 2 * ((n : ℤ) * (2 * (I : ℤ)) ^ (n - 1) * m) = (2 * (I : ℤ)) ^ n := by
    calc
      _ = (2 * (I : ℤ)) ^ (n - 1) * (2 * I) := by rw [hIc]; ring
      _ = _ := hp
  have hb := pow_add_mul_le_add_pow (a := 2 * (I : ℤ)) (b := -(m : ℤ)) (by positivity) (by omega) n
  have hadd : 2 * (I : ℤ) + -(m : ℤ) = (R : ℤ) := by omega
  rw [hadd] at hb
  have hz : (2 * (I : ℤ)) ^ n ≤ 2 * (R : ℤ) ^ n := by nlinarith
  exact_mod_cast hz

theorem upper_eight (n : ℕ) (hn : 3 ≤ n) :
    Nat.card (FORecoveryCompactness.Tables Law3319 (Fin n)) ≤
      4 * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) := by
  have hh := law_upper (A := Fin n) (by simpa using hn)
  simp only [Fintype.card_fin] at hh
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law8.models_iff (Fin n) ⟨f⟩)),
    EightRowCounting.count_eight_nat,Fintype.card_fin]
  exact hh.trans (by have hp := Nat.mul_le_mul_left 2 (double_bound n (by omega)); simpa only [← Nat.mul_assoc] using hp)

theorem negative_of_lower (L : NatMagmaLaw) (c : ℕ)
    (hL : ∀ n : ℕ, 6 ≤ n → n * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) ≤
      c * Nat.card (FORecoveryCompactness.Tables L (Fin n))) : ¬ Law3319.StructuralFrom L := by
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts L Law3319 h
  let n := 4 * c * K + 6
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  have hn : 6 ≤ n := by dsimp [n]; omega
  have hp : 0 < Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) :=
    lt_of_lt_of_le (Nat.mul_pos (by omega) (EightRowCounting.idem_count_pos n (by omega)))
      (EightRowCounting.cardinal_bound n (by omega))
  have hb : n * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) ≤
      (4 * c * K) * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) := by
    calc
      _ ≤ c * Nat.card (FORecoveryCompactness.Tables L (Fin n)) := hL n hn
      _ ≤ c * (K * Nat.card (FORecoveryCompactness.Tables Law3319 (Fin n))) := Nat.mul_le_mul_left c (hK (Fin n))
      _ ≤ c * (K * (4 * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)))) :=
        Nat.mul_le_mul_left c (Nat.mul_le_mul_left K (upper_eight n (by omega)))
      _ = _ := by ac_rfl
  have hh := Nat.le_of_mul_le_mul_right hb hp
  dsimp [n] at hh
  omega


end LeftCubeColumnCounting


theorem Equation3319_not_StructuralFrom_Equation3253_compactness :
    ¬ Law3319.StructuralFrom Law3253 := LeftCubeColumnCounting.negative_of_lower Law3253 3
      (fun n hn => EventualRowCounting.cardinal_bound n (by omega))

theorem Equation3319_not_StructuralFrom_Equation411_compactness :
    ¬ Law3319.StructuralFrom Law411 := LeftCubeColumnCounting.negative_of_lower Law411 16
      CycleFourCounting.cardinal_lower

theorem Equation3319_not_StructuralFrom_Equation151_compactness :
    ¬ Law3319.StructuralFrom Law151 := DiagonalTableCounting.involution_negative_of_upper Law3319
      (by
        intro G _ _ hn
        classical
        exact LeftCubeColumnCounting.upper_profile hn)

theorem Equation3319_not_StructuralFrom_Equation3659_compactness :
    ¬ Law3319.StructuralFrom Law3659 := DiagonalTableCounting.retract_negative_of_upper Law3319
      (by
        intro G _ _ hn
        classical
        exact LeftCubeColumnCounting.upper_profile hn)

/-- info: 'Equation3319_not_StructuralFrom_Equation3253_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3319_not_StructuralFrom_Equation3253_compactness

/-- info: 'Equation3319_not_StructuralFrom_Equation411_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3319_not_StructuralFrom_Equation411_compactness

/-- info: 'Equation3319_not_StructuralFrom_Equation151_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3319_not_StructuralFrom_Equation151_compactness

/-- info: 'Equation3319_not_StructuralFrom_Equation3659_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3319_not_StructuralFrom_Equation3659_compactness

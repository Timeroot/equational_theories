import equational_theories.Definability.SingleDefectCounting

/-!
# A four-point single-row defect for E1020

Choose distinct x,s,t,u and prescribe x*x=s, x*s=t, x*u=x, t*t=t, t*x=u.
Every other row satisfies E8. The resulting table satisfies E1020 and fails
E8 exactly at x; successive evaluations recover s,t,u. This gives an injective
family of n*(n-1)*(n-2)*(n-3)*n^(2*n-5)*R^(n-2) tables, where R counts E8 rows.

For n>=6 the family proves n*N_8(n) <= 32*N_1020(n). The existing upper bounds
for E47 and E3319, together with compactness, rule out unrestricted FO recovery.
All counting is symbolic; there is no enumerated model table or SAT certificate.
-/

namespace PointConstraintCounting
variable {A : Type} [Fintype A] [DecidableEq A]
abbrev Three (u v w a b c : A) := {f : A → A // f u=a ∧ f v=b ∧ f w=c}
noncomputable def threeEquiv (u v w a b c : A) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Three u v w a b c ≃ (CycleThreeCounting.Outside u v w → A) where
  toFun f x := f.val x.val
  invFun g := ⟨fun x => if h : x=u then a else if h' : x=v then b else if h'' : x=w then c
    else g ⟨x,by simp [h,h',h'']⟩,by simp [huv.symm,huw.symm,hvw.symm]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    dsimp
    split_ifs with h h' h''
    · subst x; exact f.property.1.symm
    · subst x; exact f.property.2.1.symm
    · subst x; exact f.property.2.2.symm
    · rfl
  right_inv g := by
    funext x
    have hx := x.property
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hx
    simp [hx.1,hx.2.1,hx.2.2]

lemma three_count (u v w a b c : A) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Fintype.card (Three u v w a b c) = Fintype.card A^(Fintype.card A-3) := by
  rw [Fintype.card_congr (threeEquiv u v w a b c huv huw hvw),Fintype.card_fun,
    CycleFourCounting.card_outside_three u v w huv huw hvw]
end PointConstraintCounting

open Law Law.MagmaLaw
namespace E1020SingleDefect
variable {A : Type} [DecidableEq A]
open EightRowCounting PointConstraintCounting
open SingleDefectCounting (rowCount)

abbrev Positions (A : Type) := Fin 4 ↪ A
abbrev Block (e : Positions A) :=
  Three (e 0) (e 1) (e 3) (e 1) (e 2) (e 0) × Two (e 2) (e 0) (e 2) (e 3) ×
    ((r : Outside (e 0) (e 2)) → Row8 r.val)
abbrev Code (A : Type) [DecidableEq A] := Σ e : Positions A, Block e

def table (e : Positions A) (b : Block e) (x y : A) : A :=
  if h : x=e 0 then b.1.val y else if h' : x=e 2 then b.2.1.val y
  else (b.2.2 ⟨x,by simp [h,h']⟩).val y

lemma at_first (e : Positions A) (b : Block e) (y : A) : table e b (e 0) y = b.1.val y := by
  simp [table]
lemma at_second (e : Positions A) (b : Block e) (y : A) : table e b (e 2) y = b.2.1.val y := by
  simp [table,e.injective.ne (by decide : (2 : Fin 4) ≠ 0)]
lemma at_other (e : Positions A) (b : Block e) (r : Outside (e 0) (e 2)) (y : A) :
    table e b r.val y = (b.2.2 r).val y := by
  have hr := r.property
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
  simp [table,hr.1,hr.2]

lemma good_others (e : Positions A) (b : Block e) (x : A) (hx : x ≠ e 0) :
    table e b x (table e b x x) = x := by
  by_cases ht : x=e 2
  · subst x
    rw [at_second,at_second,b.2.1.property.1,b.2.1.property.1]
  · let r : Outside (e 0) (e 2) := ⟨x,by simp [hx,ht]⟩
    change table e b r.val (table e b r.val r.val) = r.val
    rw [at_other,at_other]
    exact (b.2.2 r).property

lemma bad_iff (e : Positions A) (b : Block e) (x : A) :
    table e b x (table e b x x) ≠ x ↔ x=e 0 := by
  constructor
  · contrapose!
    exact good_others e b x
  · rintro rfl
    rw [at_first,at_first,b.1.property.1,b.1.property.2.1]
    exact e.injective.ne (by decide)

lemma law1020 (e : Positions A) (b : Block e) : @Equation1020 A ⟨table e b⟩ := by
  intro x
  change x = table e b x (table e b (table e b x (table e b x x)) x)
  by_cases hx : x=e 0
  · subst x
    simp only [at_first,b.1.property.1,b.1.property.2.1,at_second,b.2.1.property.2,b.1.property.2.2]
  · rw [good_others e b x hx,good_others e b x hx]

def encode (c : Code A) : FORecoveryCompactness.Tables Law1020 A :=
  ⟨table c.1 c.2,(@Law1020.models_iff A ⟨table c.1 c.2⟩).mpr (law1020 c.1 c.2)⟩

lemma table_injective (e : Positions A) : Function.Injective (table e) := by
  intro b c h
  apply Prod.ext
  · apply Subtype.ext
    funext y
    simpa only [at_first] using congrFun (congrFun h (e 0)) y
  · apply Prod.ext
    · apply Subtype.ext
      funext y
      simpa only [at_second] using congrFun (congrFun h (e 2)) y
    · funext r
      apply Subtype.ext
      funext y
      simpa only [at_other] using congrFun (congrFun h r.val) y

lemma encode_injective : Function.Injective (encode (A := A)) := by
  rintro ⟨e,b⟩ ⟨f,c⟩ h
  have hh : table e b = table f c := congrArg Subtype.val h
  have h0 : e 0=f 0 := by
    apply (bad_iff f c (e 0)).mp
    rw [←hh]
    exact (bad_iff e b (e 0)).mpr rfl
  have h1 : e 1=f 1 := by
    have hi := congrFun (congrFun hh (e 0)) (e 0)
    rw [at_first,b.1.property.1,h0,at_first,c.1.property.1] at hi
    exact hi
  have h2 : e 2=f 2 := by
    have hi := congrFun (congrFun hh (e 0)) (e 1)
    rw [at_first,b.1.property.2.1,h0,h1,at_first,c.1.property.2.1] at hi
    exact hi
  have h3 : e 3=f 3 := by
    have hi := congrFun (congrFun hh (e 2)) (e 0)
    rw [at_second,b.2.1.property.2,h2,h0,at_second,c.2.1.property.2] at hi
    exact hi
  have he : e=f := by ext i; fin_cases i <;> assumption
  subst f
  have hb : b=c := table_injective e hh
  subst c
  rfl

variable [Fintype A]
lemma block_count (e : Positions A) : Fintype.card (Block e) =
    Fintype.card A^(Fintype.card A-3) * Fintype.card A^(Fintype.card A-2) *
      rowCount (Fintype.card A)^(Fintype.card A-2) := by
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h03 : e 0 ≠ e 3 := e.injective.ne (by decide)
  have h13 : e 1 ≠ e 3 := e.injective.ne (by decide)
  have h02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  rw [Fintype.card_prod,Fintype.card_prod,three_count _ _ _ _ _ _ h01 h03 h13,
    two_count _ _ _ _ h02.symm,Fintype.card_pi]
  simp only [card_row,Finset.prod_const,Finset.card_univ,card_outside,Finset.card_pair h02]
  simp only [rowCount,mul_assoc]

lemma code_count : Fintype.card (Code A) =
    Fintype.card A * (Fintype.card A-1) * (Fintype.card A-2) * (Fintype.card A-3) *
      (Fintype.card A^(Fintype.card A-3) * Fintype.card A^(Fintype.card A-2) *
      rowCount (Fintype.card A)^(Fintype.card A-2)) := by
  rw [Fintype.card_sigma]
  simp only [block_count,Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
  rw [Fintype.card_embedding_eq]
  simp [Nat.descFactorial_succ,mul_assoc,mul_comm]

lemma count_lower (n : ℕ) :
    n*(n-1)*(n-2)*(n-3)*(n^(n-3)*n^(n-2)*rowCount n^(n-2)) ≤
      Nat.card (FORecoveryCompactness.Tables Law1020 (Fin n)) := by
  classical
  have h := Fintype.card_le_of_injective (encode (A := Fin n)) encode_injective
  rw [code_count,Fintype.card_fin] at h
  exact h.trans_eq Nat.card_eq_fintype_card.symm

lemma numerical_bound (n : ℕ) (hn : 6 ≤ n) :
    n*rowCount n^n ≤ 32*(n*(n-1)*(n-2)*(n-3)*(n^(n-3)*n^(n-2)*rowCount n^(n-2))) := by
  let m := n^(n-3)
  let R := rowCount n
  let q := R^(n-2)
  have hp : n^(n-2) = n*m := by
    dsimp [m]
    rw [←pow_succ']
    congr 1
    omega
  have hp' : n^(n-1) = n^2*m := by
    dsimp [m]
    rw [←pow_add]
    congr 1
    omega
  have hR : R ≤ 2*n^2*m := by
    dsimp [R,rowCount]
    rw [hp,hp']
    have hh := Nat.mul_le_mul_right (n*m) (Nat.sub_le n 1)
    nlinarith only [hh]
  have hR2 : R^2 ≤ 4*n^4*m^2 := by
    have hh := Nat.pow_le_pow_left hR 2
    nlinarith only [hh]
  have h1 : n ≤ 2*(n-1) := by omega
  have h2 : n ≤ 2*(n-2) := by omega
  have h3 : n ≤ 2*(n-3) := by omega
  have hc : n^3 ≤ 8*(n-1)*(n-2)*(n-3) := by
    have hh := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    nlinarith only [hh]
  have hpow : R^n = R^2*q := by
    dsimp [q]
    rw [←pow_add]
    congr 1
    omega
  rw [hp]
  change n*R^n ≤ 32*(n*(n-1)*(n-2)*(n-3)*(m*(n*m)*q))
  rw [hpow]
  have ha := Nat.mul_le_mul_left (n*q) hR2
  have hb := Nat.mul_le_mul_left (4*n^2*m^2*q) hc
  nlinarith only [ha,hb]

lemma cardinal_lower (n : ℕ) (hn : 6 ≤ n) :
    n*Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) ≤
      32*Nat.card (FORecoveryCompactness.Tables Law1020 (Fin n)) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law8.models_iff (Fin n) ⟨f⟩)),
    EightRowCounting.count_eight_nat,Fintype.card_fin]
  exact (numerical_bound n hn).trans (Nat.mul_le_mul_left 32 (count_lower n))

end E1020SingleDefect

theorem Equation3319_not_StructuralFrom_Equation1020_singleDefect :
    ¬ Law3319.StructuralFrom Law1020 :=
  SingleDefectCounting.negative_of_bounds Law1020 Law3319 32 4
    E1020SingleDefect.cardinal_lower
    (fun n hn => LeftCubeColumnCounting.upper_eight n (by omega))

theorem Equation47_not_StructuralFrom_Equation1020_singleDefect :
    ¬ Law47.StructuralFrom Law1020 :=
  SingleDefectCounting.negative_of_bounds Law1020 Law47 32 1
    E1020SingleDefect.cardinal_lower
    (fun n hn => by simpa using CycleThreeCounting.upper_eight n (by omega))

spectrum_assert Equation3319_not_StructuralFrom_Equation1020_singleDefect complete
spectrum_assert Equation47_not_StructuralFrom_Equation1020_singleDefect complete

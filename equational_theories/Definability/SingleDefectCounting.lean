import equational_theories.Definability.LeftCubeColumnCounting
import equational_theories.Spectrum.Status
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Single-row defects separate E1832 and E3862 from E47 and E3319

Keep every row E8 except at x, and choose distinct x,s,t. Always prescribe
x*x=s, x*s=t, t*t=t. The last entry is either t*s=x (giving E1832),
or t*x=s (giving E3862, the dual of E3456). The table fails E8 precisely
at x and recovers all three named points, so distinct codes give distinct tables.

Writing R=n^(n-1)+(n-1)*n^(n-2), the family has
n*(n-1)*(n-2)*n^(2*n-4)*R^(n-2) tables. For n>=4,
n*N_8(n) <= 16*N_source(n). Compactness converts the unbounded ratio into
FO-structural negatives on arbitrary carriers. The defining formulas may
depend on the model; no finite-variant negative follows from this argument.
-/

open Law Law.MagmaLaw
namespace SingleDefectCounting
variable {A : Type} [DecidableEq A]
open EightRowCounting PointConstraintCounting

abbrev Positions (A : Type) := Fin 3 ↪ A
def input (flip : Bool) (e : Positions A) : A := if flip then e 0 else e 1
def output (flip : Bool) (e : Positions A) : A := if flip then e 1 else e 0
variable (flip : Bool)
abbrev Block (e : Positions A) :=
  Two (e 0) (e 1) (e 1) (e 2) × Two (e 2) (input flip e) (e 2) (output flip e) ×
    ((r : Outside (e 0) (e 2)) → Row8 r.val)
abbrev Code (flip : Bool) (A : Type) [DecidableEq A] := Σ e : Positions A, Block flip e

def table (e : Positions A) (b : Block flip e) (x y : A) : A :=
  if h : x=e 0 then b.1.val y else if h' : x=e 2 then b.2.1.val y
  else (b.2.2 ⟨x,by simp [h,h']⟩).val y

lemma at_first (e : Positions A) (b : Block flip e) (y : A) : table flip e b (e 0) y = b.1.val y := by
  simp [table]
lemma at_second (e : Positions A) (b : Block flip e) (y : A) : table flip e b (e 2) y = b.2.1.val y := by
  simp [table, e.injective.ne (by decide : (2 : Fin 3) ≠ 0)]
lemma at_other (e : Positions A) (b : Block flip e) (r : Outside (e 0) (e 2)) (y : A) :
    table flip e b r.val y = (b.2.2 r).val y := by
  have hr := r.property
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
  simp [table,hr.1,hr.2]

lemma good_others (e : Positions A) (b : Block flip e) (x : A) (hx : x ≠ e 0) :
    table flip e b x (table flip e b x x) = x := by
  by_cases ht : x=e 2
  · subst x
    rw [at_second,at_second,b.2.1.property.1,b.2.1.property.1]
  · let r : Outside (e 0) (e 2) := ⟨x,by simp [hx,ht]⟩
    change table flip e b r.val (table flip e b r.val r.val) = r.val
    rw [at_other,at_other]
    exact (b.2.2 r).property

lemma bad_iff (e : Positions A) (b : Block flip e) (x : A) :
    table flip e b x (table flip e b x x) ≠ x ↔ x=e 0 := by
  constructor
  · contrapose!
    exact good_others flip e b x
  · rintro rfl
    rw [at_first,at_first,b.1.property.1,b.1.property.2]
    exact e.injective.ne (by decide)

lemma law1832 (e : Positions A) (b : Block false e) : @Equation1832 A ⟨table false e b⟩ := by
  intro x
  change x = table false e b (table false e b x (table false e b x x)) (table false e b x x)
  by_cases hx : x=e 0
  · subst x
    simp only [at_first,b.1.property.1,b.1.property.2,at_second]
    exact b.2.1.property.2.symm
  · rw [good_others false e b x hx,good_others false e b x hx]

lemma law3862 (e : Positions A) (b : Block true e) : @Equation3862 A ⟨table true e b⟩ := by
  intro x
  change table true e b x x = table true e b (table true e b x (table true e b x x)) x
  by_cases hx : x=e 0
  · subst x
    simp only [at_first,b.1.property.1,b.1.property.2,at_second]
    exact b.2.1.property.2.symm
  · rw [good_others true e b x hx]

def target (flip : Bool) : NatMagmaLaw := if flip then Law3862 else Law1832

def encode (c : Code flip A) : FORecoveryCompactness.Tables (target flip) A := by
  refine ⟨table flip c.1 c.2,?_⟩
  cases flip
  · exact (@Law1832.models_iff A ⟨table false c.1 c.2⟩).mpr (law1832 c.1 c.2)
  · exact (@Law3862.models_iff A ⟨table true c.1 c.2⟩).mpr (law3862 c.1 c.2)

lemma table_injective (e : Positions A) : Function.Injective (table flip e) := by
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

lemma encode_injective : Function.Injective (encode flip (A := A)) := by
  rintro ⟨e,b⟩ ⟨f,c⟩ h
  have hh : table flip e b = table flip f c := congrArg Subtype.val h
  have h0 : e 0=f 0 := by
    apply (bad_iff flip f c (e 0)).mp
    rw [←hh]
    exact (bad_iff flip e b (e 0)).mpr rfl
  have h1 : e 1=f 1 := by
    have hi := congrFun (congrFun hh (e 0)) (e 0)
    rw [at_first,b.1.property.1,h0,at_first,c.1.property.1] at hi
    exact hi
  have h2 : e 2=f 2 := by
    have hi := congrFun (congrFun hh (e 0)) (e 1)
    rw [at_first,b.1.property.2,h0,h1,at_first,c.1.property.2] at hi
    exact hi
  have he : e=f := by ext i; fin_cases i <;> assumption
  subst f
  have hb : b=c := table_injective flip e hh
  subst c
  rfl

def rowCount (n : ℕ) := n^(n-1)+(n-1)*n^(n-2)

variable [Fintype A]

lemma block_count (e : Positions A) : Fintype.card (Block flip e) =
    Fintype.card A^(Fintype.card A-2) * Fintype.card A^(Fintype.card A-2) *
      rowCount (Fintype.card A)^(Fintype.card A-2) := by
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h21 : e 2 ≠ input flip e := by
    cases flip <;> simp only [input,Bool.false_eq_true,↓reduceIte]
    · exact e.injective.ne (by decide)
    · exact e.injective.ne (by decide)
  have h02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  rw [Fintype.card_prod,Fintype.card_prod,two_count _ _ _ _ h01,two_count _ _ _ _ h21,Fintype.card_pi]
  simp only [card_row,Finset.prod_const,Finset.card_univ,card_outside,Finset.card_pair h02]
  simp only [rowCount,mul_assoc]

lemma code_count : Fintype.card (Code flip A) =
    Fintype.card A * (Fintype.card A-1) * (Fintype.card A-2) *
      (Fintype.card A^(Fintype.card A-2) * Fintype.card A^(Fintype.card A-2) *
      rowCount (Fintype.card A)^(Fintype.card A-2)) := by
  rw [Fintype.card_sigma]
  simp only [block_count,Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
  rw [Fintype.card_embedding_eq]
  simp [Nat.descFactorial_succ, mul_assoc, mul_comm]

lemma count_lower (n : ℕ) :
    n*(n-1)*(n-2)*(n^(n-2)*n^(n-2)*rowCount n^(n-2)) ≤
      Nat.card (FORecoveryCompactness.Tables (target flip) (Fin n)) := by
  classical
  have h := Fintype.card_le_of_injective (encode flip (A := Fin n)) (encode_injective flip)
  rw [code_count,Fintype.card_fin] at h
  exact h.trans_eq Nat.card_eq_fintype_card.symm

lemma numerical_bound (n : ℕ) (hn : 4 ≤ n) :
    n*rowCount n^n ≤ 16*(n*(n-1)*(n-2)*(n^(n-2)*n^(n-2)*rowCount n^(n-2))) := by
  let m := n^(n-2)
  let R := rowCount n
  let q := R^(n-2)
  have hp : n^(n-1) = n*m := by
    dsimp [m]
    rw [←pow_succ']
    congr 1
    omega
  have hR : R ≤ 2*n*m := by
    dsimp [R,rowCount]
    rw [hp]
    change n*m+(n-1)*m ≤ 2*n*m
    have hh := Nat.mul_le_mul_right m (Nat.sub_le n 1)
    nlinarith
  have hR2 : R^2 ≤ 4*n^2*m^2 := by
    have hh := Nat.pow_le_pow_left hR 2
    nlinarith only [hh]
  have h1 : n ≤ 2*(n-1) := by omega
  have h2 : n ≤ 2*(n-2) := by omega
  have hc : n^2 ≤ 4*(n-1)*(n-2) := by
    have hh := Nat.mul_le_mul h1 h2
    nlinarith only [hh]
  have hpow : R^n = R^2*q := by
    dsimp [q]
    rw [←pow_add]
    congr 1
    omega
  change n*R^n ≤ 16*(n*(n-1)*(n-2)*(m*m*q))
  rw [hpow]
  have ha := Nat.mul_le_mul_left (n*q) hR2
  have hb := Nat.mul_le_mul_left (4*n*m^2*q) hc
  nlinarith only [ha,hb]

lemma cardinal_lower (n : ℕ) (hn : 4 ≤ n) :
    n*Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) ≤
      16*Nat.card (FORecoveryCompactness.Tables (target flip) (Fin n)) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law8.models_iff (Fin n) ⟨f⟩)),
    EightRowCounting.count_eight_nat,Fintype.card_fin]
  exact (numerical_bound n hn).trans (Nat.mul_le_mul_left 16 (count_lower flip n))

/-- An unbounded table-count ratio obstructs even model-dependent FO recovery. -/
lemma negative_of_bounds (S T : NatMagmaLaw) (c d : ℕ)
    (hS : ∀ n, 6 ≤ n → n*Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) ≤
      c*Nat.card (FORecoveryCompactness.Tables S (Fin n)))
    (hT : ∀ n, 6 ≤ n → Nat.card (FORecoveryCompactness.Tables T (Fin n)) ≤
      d*Nat.card (FORecoveryCompactness.Tables Law8 (Fin n))) :
    ¬ T.StructuralFrom S := by
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts S T h
  let n := c*d*K+6
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  have hn : 6 ≤ n := by dsimp [n]; omega
  haveI : Nonempty (FORecoveryCompactness.Tables Law8 (Fin n)) :=
    ⟨⟨fun x _ => x,(@Law8.models_iff (Fin n) ⟨fun x _ => x⟩).mpr (fun _ => rfl)⟩⟩
  have hb : n*Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) ≤
      (c*d*K)*Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) := by
    calc
      _ ≤ c*Nat.card (FORecoveryCompactness.Tables S (Fin n)) := hS n hn
      _ ≤ c*(K*Nat.card (FORecoveryCompactness.Tables T (Fin n))) :=
        Nat.mul_le_mul_left c (hK (Fin n))
      _ ≤ c*(K*(d*Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)))) :=
        Nat.mul_le_mul_left c (Nat.mul_le_mul_left K (hT n hn))
      _ = _ := by ring
  have hh := Nat.le_of_mul_le_mul_right hb Nat.card_pos
  dsimp [n] at hh
  omega

end SingleDefectCounting

theorem Equation3319_not_StructuralFrom_Equation1832_singleDefect :
    ¬ Law3319.StructuralFrom Law1832 :=
  SingleDefectCounting.negative_of_bounds Law1832 Law3319 16 4
    (fun n hn => SingleDefectCounting.cardinal_lower false n (by omega))
    (fun n hn => LeftCubeColumnCounting.upper_eight n (by omega))

theorem Equation47_not_StructuralFrom_Equation1832_singleDefect :
    ¬ Law47.StructuralFrom Law1832 :=
  SingleDefectCounting.negative_of_bounds Law1832 Law47 16 1
    (fun n hn => SingleDefectCounting.cardinal_lower false n (by omega))
    (fun n hn => by simpa using CycleThreeCounting.upper_eight n (by omega))

spectrum_assert Equation3319_not_StructuralFrom_Equation1832_singleDefect complete
spectrum_assert Equation47_not_StructuralFrom_Equation1832_singleDefect complete

theorem Equation3319_not_StructuralFrom_Equation3862_singleDefect :
    ¬ Law3319.StructuralFrom Law3862 :=
  SingleDefectCounting.negative_of_bounds Law3862 Law3319 16 4
    (fun n hn => SingleDefectCounting.cardinal_lower true n (by omega))
    (fun n hn => LeftCubeColumnCounting.upper_eight n (by omega))

theorem Equation47_not_StructuralFrom_Equation3862_singleDefect :
    ¬ Law47.StructuralFrom Law3862 :=
  SingleDefectCounting.negative_of_bounds Law3862 Law47 16 1
    (fun n hn => SingleDefectCounting.cardinal_lower true n (by omega))
    (fun n hn => by simpa using CycleThreeCounting.upper_eight n (by omega))

spectrum_assert Equation3319_not_StructuralFrom_Equation3862_singleDefect complete
spectrum_assert Equation47_not_StructuralFrom_Equation3862_singleDefect complete
spectrum_assert SingleDefectCounting.count_lower complete

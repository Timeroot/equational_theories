import equational_theories.Definability.LeftCubeColumnCounting

/-! Counting collisions in short straight-line evaluations of a binary operation.
A program uses each syntactically distinct input pair once. Before any two
intermediate values coincide, it therefore reads a fresh table entry. -/

namespace StraightLineCounting

structure Program (r : ℕ) where
  left : Fin r → ℕ
  right : Fin r → ℕ
  left_le : ∀ i, left i ≤ i.val
  right_le : ∀ i, right i ≤ i.val
  distinct : Function.Injective (fun i => (left i, right i))

variable {A X : Type} [Fintype A] [Fintype X] [DecidableEq A] [DecidableEq X]

abbrev Fixed {s : ℕ} (q : Fin s → X) (v : Fin s → A) :=
  {f : X → A // ∀ i, f (q i) = v i}

def restrictFixed {s : ℕ} (q : Fin s → X) (v : Fin s → A) (f : Fixed q v) :
    {x : X // x ∉ Finset.univ.image q} → A := fun x => f.val x.val

omit [Fintype A] [Fintype X] [DecidableEq A] in
theorem restrictFixed_injective {s : ℕ} (q : Fin s → X) (v : Fin s → A) :
    Function.Injective (restrictFixed q v) := by
  intro f g h
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ Finset.univ.image q
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact (f.property i).trans (g.property i).symm
  · exact congrFun h ⟨x,hx⟩

theorem fixed_bound {s : ℕ} (q : Fin s → X) (v : Fin s → A) (hq : Function.Injective q) :
    Fintype.card (Fixed q v) ≤ Fintype.card A ^ (Fintype.card X - s) := by
  have hc : Fintype.card {x : X // x ∉ Finset.univ.image q} = Fintype.card X - s := by
    rw [Fintype.card_subtype_compl,Fintype.card_coe,Finset.card_image_of_injective _ hq]
    simp
  calc
    _ ≤ Fintype.card ({x : X // x ∉ Finset.univ.image q} → A) :=
      Fintype.card_le_of_injective (restrictFixed q v) (restrictFixed_injective q v)
    _ = _ := by rw [Fintype.card_fun,hc]

variable {r : ℕ}

def query (P : Program r) (k : Fin r) (v : Fin (k.val+1) → A) (i : Fin (k.val+1)) : A × A :=
  (v ⟨P.left ⟨i.val,by omega⟩,by have h := P.left_le ⟨i.val,by omega⟩; dsimp only at h; omega⟩,
   v ⟨P.right ⟨i.val,by omega⟩,by have h := P.right_le ⟨i.val,by omega⟩; dsimp only at h; omega⟩)

omit [Fintype A] [DecidableEq A] in
theorem query_injective (P : Program r) (k : Fin r) (v : Fin (k.val+1) → A)
    (hv : Function.Injective v) : Function.Injective (query P k v) := by
  intro i j h
  have hl := congrArg Fin.val (hv (congrArg Prod.fst h))
  have hr := congrArg Fin.val (hv (congrArg Prod.snd h))
  have he := P.distinct (Prod.ext hl hr)
  exact Fin.ext (congrArg (fun z : Fin r => z.val) he)

def output (k : Fin r) (v : Fin (k.val+1) → A) (c i : Fin (k.val+1)) : A :=
  if h : i.val < k.val then v ⟨i.val+1,by omega⟩ else v c

abbrev Prefix (k : Fin r) (x : A) :=
  {v : Fin (k.val+1) → A // v 0 = x ∧ Function.Injective v}

abbrev StepCode (P : Program r) (k : Fin r) (x : A) :=
  Σ v : Prefix k x, Σ c : Fin (k.val+1), Fixed (query P k v.val) (output k v.val c)
abbrev Code (P : Program r) (x : A) := Σ k : Fin r, StepCode P k x

def table (P : Program r) (x : A) (c : Code P x) : A × A → A := c.2.2.2.val

abbrev Bad (P : Program r) (x : A) := {f : A × A → A // ∃ c : Code P x, table P x c = f}

noncomputable def encode (P : Program r) (x : A) (f : Bad P x) : Code P x := f.property.choose

omit [Fintype A] [DecidableEq A] in
theorem encode_injective (P : Program r) (x : A) : Function.Injective (encode P x) := by
  intro f g h
  apply Subtype.ext
  exact f.property.choose_spec.symm.trans ((congrArg (table P x) h).trans g.property.choose_spec)

theorem prefix_bound (k : Fin r) (x : A) : Fintype.card (Prefix k x) ≤ Fintype.card A ^ k.val := by
  let e : Prefix k x → PointConstraintCounting.One (0 : Fin (k.val+1)) x :=
    fun v => ⟨v.val,v.property.1⟩
  have hi : Function.Injective e := by intro v w h; exact Subtype.ext (congrArg (fun z : PointConstraintCounting.One (0 : Fin (k.val+1)) x => z.val) h)
  calc
    _ ≤ Fintype.card (PointConstraintCounting.One (0 : Fin (k.val+1)) x) := Fintype.card_le_of_injective e hi
    _ = _ := by rw [PointConstraintCounting.one_count]; simp

theorem step_bound (P : Program r) (k : Fin r) (x : A) (hn : r ≤ Fintype.card A * Fintype.card A) :
    Fintype.card (StepCode P k x) ≤ r * Fintype.card A ^ (Fintype.card A * Fintype.card A - 1) := by
  let n := Fintype.card A
  change r ≤ n*n at hn
  have hp : k.val + (n*n-(k.val+1)) = n*n-1 := by omega
  calc
    _ = ∑ v : Prefix k x, ∑ c : Fin (k.val+1), Fintype.card (Fixed (query P k v.val) (output k v.val c)) := by
      simp only [Fintype.card_sigma]
    _ ≤ ∑ _v : Prefix k x, ∑ _c : Fin (k.val+1), n ^ (n*n-(k.val+1)) := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro c _
      simpa only [Fintype.card_prod] using fixed_bound (query P k v.val) (output k v.val c) (query_injective P k v.val v.property.2)
    _ = Fintype.card (Prefix k x) * ((k.val+1) * n^(n*n-(k.val+1))) := by simp
    _ ≤ n^k.val * ((k.val+1) * n^(n*n-(k.val+1))) := Nat.mul_le_mul_right _ (prefix_bound k x)
    _ = (k.val+1) * n^(n*n-1) := by rw [← hp,pow_add]; ac_rfl
    _ ≤ r * n^(n*n-1) := Nat.mul_le_mul_right _ (by omega)

theorem bad_bound (P : Program r) (x : A) (hn : r ≤ Fintype.card A * Fintype.card A) :
    Fintype.card (Bad P x) ≤ r*r * Fintype.card A ^ (Fintype.card A * Fintype.card A - 1) := by
  calc
    _ ≤ Fintype.card (Code P x) := Fintype.card_le_of_injective (encode P x) (encode_injective P x)
    _ = ∑ k : Fin r, Fintype.card (StepCode P k x) := Fintype.card_sigma
    _ ≤ ∑ _k : Fin r, r * Fintype.card A ^ (Fintype.card A * Fintype.card A - 1) :=
      Finset.sum_le_sum (fun k _ => step_bound P k x hn)
    _ = _ := by simp [Nat.mul_assoc]

def Trace (P : Program r) (f : A × A → A) (v : Fin (r+1) → A) : Prop :=
  ∀ i : Fin r, f (v ⟨P.left i,by have h := P.left_le i; omega⟩,
    v ⟨P.right i,by have h := P.right_le i; omega⟩) = v ⟨i.val+1,by omega⟩

omit [Fintype A] in
theorem bad_of_trace (P : Program r) (f : A × A → A) (v : Fin (r+1) → A)
    (ht : Trace P f v) (hv : ¬ Function.Injective v) : ∃ c : Code P (v 0), table P (v 0) c = f := by
  classical
  have hex : ∃ j : ℕ, ∃ hj : j < r+1, ∃ i : Fin j,
      v ⟨j,hj⟩ = v ⟨i.val,by omega⟩ := by
    obtain ⟨a,b,he,hab⟩ := Function.not_injective_iff.mp hv
    have hn : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rcases lt_or_gt_of_ne hn with h | h
    · exact ⟨b.val,b.isLt,⟨a.val,h⟩,he.symm⟩
    · exact ⟨a.val,a.isLt,⟨b.val,h⟩,he⟩
  let j := Nat.find hex
  obtain ⟨hj,i,hi⟩ := Nat.find_spec hex
  have hjpos : 0 < j := by have := i.isLt; omega
  let k : Fin r := ⟨j-1,by dsimp [j]; omega⟩
  have hkj : k.val+1 = j := by dsimp [k]; omega
  let w : Fin (k.val+1) → A := fun a => v ⟨a.val,by omega⟩
  have hw : Function.Injective w := by
    intro a b he
    by_contra hab
    have hn : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rcases lt_or_gt_of_ne hn with h | h
    · have hbad : ∃ hb : b.val < r+1, ∃ a' : Fin b.val,
          v ⟨b.val,hb⟩ = v ⟨a'.val,by omega⟩ := ⟨by omega,⟨a.val,h⟩,he.symm⟩
      have hle := Nat.find_min' hex hbad
      have := b.isLt
      change j ≤ b.val at hle
      omega
    · have hbad : ∃ ha : a.val < r+1, ∃ b' : Fin a.val,
          v ⟨a.val,ha⟩ = v ⟨b'.val,by omega⟩ := ⟨by omega,⟨b.val,h⟩,he⟩
      have hle := Nat.find_min' hex hbad
      have := a.isLt
      change j ≤ a.val at hle
      omega
  let c : Fin (k.val+1) := ⟨i.val,by omega⟩
  have hf : ∀ a, f (query P k w a) = output k w c a := by
    intro a
    have he := ht ⟨a.val,by omega⟩
    change f (query P k w a) = v ⟨a.val+1,by omega⟩ at he
    rw [he]
    unfold output
    split_ifs with ha
    · rfl
    · have heq : a.val+1 = j := by omega
      change v ⟨a.val+1,_⟩ = v ⟨i.val,_⟩
      convert hi using 1
      exact congrArg v (Fin.ext heq)
  exact ⟨⟨k,⟨w,rfl,hw⟩,c,⟨f,hf⟩⟩,rfl⟩

open Law Law.MagmaLaw

def Captures (B : NatMagmaLaw) (P : Program r) : Prop :=
  ∀ (G : Type) (f : G → G → G), @satisfies _ G ⟨f⟩ B → ∀ x : G,
    ∃ v : Fin (r+1) → G, v 0 = x ∧ Trace P (Function.uncurry f) v ∧ ¬ Function.Injective v

theorem capture_bound (B : NatMagmaLaw) (P : Program r) (hB : Captures B P)
    (x : A) (hn : r ≤ Fintype.card A * Fintype.card A) :
    Nat.card (FORecoveryCompactness.Tables B A) ≤ r*r * Fintype.card A ^ (Fintype.card A * Fintype.card A - 1) := by
  classical
  let e : FORecoveryCompactness.Tables B A → Bad P x := fun f => ⟨Function.uncurry f.val,by
    obtain ⟨v,hv,ht,hi⟩ := hB A f.val f.property x
    rw [← hv]
    exact bad_of_trace P _ v ht hi⟩
  have he : Function.Injective e := by
    intro f g h
    apply Subtype.ext
    funext a b
    exact congrFun (congrArg (fun t : Bad P x => t.val) h) (a,b)
  have hh := Nat.card_le_card_of_injective e he
  rw [Nat.card_eq_fintype_card (α := Bad P x)] at hh
  exact hh.trans (bad_bound P x hn)

def freeEquiv : FORecoveryCompactness.Tables Law1 A ≃ (A × A → A) where
  toFun f := Function.uncurry f.val
  invFun f := ⟨Function.curry f,(@Law1.models_iff A ⟨Function.curry f⟩).mpr (fun _ => rfl)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem free_count : Nat.card (FORecoveryCompactness.Tables Law1 A) =
    Fintype.card A ^ (Fintype.card A * Fintype.card A) := by
  rw [Nat.card_congr freeEquiv,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_prod]

theorem negative (B : NatMagmaLaw) (P : Program r) (hB : Captures B P) : ¬ B.StructuralFrom Law1 := by
  classical
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts Law1 B h
  let n := r*r*K+r+2
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hr : r ≤ n*n := by
    have : r ≤ n := by dsimp [n]; omega
    nlinarith
  have hb : Nat.card (FORecoveryCompactness.Tables B (Fin n)) ≤ r*r * n^(n*n-1) := by
    simpa only [Fintype.card_fin] using capture_bound B P hB (0 : Fin n) (by simpa using hr)
  have ha : Nat.card (FORecoveryCompactness.Tables Law1 (Fin n)) = n^(n*n) := by
    simpa only [Fintype.card_fin] using (free_count (A := Fin n))
  have hp : n^(n*n) = n * n^(n*n-1) := by
    have he : n*n-1+1 = n*n := Nat.sub_add_cancel (by nlinarith)
    rw [← pow_succ',he]
  have hh : n * n^(n*n-1) ≤ (K*(r*r)) * n^(n*n-1) := by
    rw [← hp,← ha]
    exact (hK (Fin n)).trans ((Nat.mul_le_mul_left K hb).trans_eq (Nat.mul_assoc _ _ _).symm)
  have hbad : n ≤ K*(r*r) := Nat.le_of_mul_le_mul_right hh (pow_pos (by omega) _)
  dsimp [n] at hbad
  nlinarith

end StraightLineCounting

/-- info: 'StraightLineCounting.negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StraightLineCounting.negative

import equational_theories.Definability.PairSwapCounting

/-! Compactness counts for independent regular actions of any nontrivial finite
 group. Local operations are `a * p (a⁻¹ * b)`, with no commutativity assumption.
 The cross-block factor is common to all unary laws and cancels from the bound. -/

open Law Law.MagmaLaw FORecoveryCompactness
namespace RegularBlockCounting

variable {I H : Type} [DecidableEq I] [Group H]
abbrev Point (I H : Type) := I × H
abbrev Cross (I : Type) := PairSwapCounting.Cross I
abbrev Params (I H : Type) := (I → H → H) × (Cross I → Bool × H)

def shift (s : I → H) (x : Point I H) : Point I H := (x.1,s x.1 * x.2)

def shiftPerm (s : I → H) : Equiv.Perm (Point I H) where
  toFun := shift s
  invFun := shift (fun i => (s i)⁻¹)
  left_inv x := by simp [shift]
  right_inv x := by simp [shift]

def Invariant (f : Point I H → Point I H → Point I H) : Prop :=
  ∀ s, (Magma.mk f).IsEndo (shiftPerm s)

def localOp (p : H → H) (a b : H) := a * p (a⁻¹ * b)

def table (c : Params I H) (x y : Point I H) : Point I H :=
  if h : x.1 = y.1 then (x.1, localOp (c.1 x.1) x.2 y.2)
  else let q := c.2 ⟨(x.1,y.1),h⟩
       if q.1 then (x.1,x.2 * q.2) else (y.1,y.2 * q.2)

lemma same (c : Params I H) (i : I) (a b : H) :
    table c (i,a) (i,b) = (i,localOp (c.1 i) a b) := by simp [table]

lemma local_shift (p : H → H) (s a b : H) :
    s * localOp p a b = localOp p (s*a) (s*b) := by
  simp [localOp,mul_assoc]

theorem table_invariant (c : Params I H) : Invariant (table c) := by
  intro s ⟨i,a⟩ ⟨j,b⟩
  change shift s (table c (i,a) (j,b)) = table c (shift s (i,a)) (shift s (j,b))
  by_cases h : i = j
  · subst j
    simp only [same,shift]
    exact congrArg (Prod.mk i) (local_shift _ _ _ _)
  · simp only [table,shift,dif_neg h]
    split_ifs <;> simp [mul_assoc]

theorem support [Nontrivial H] {f : Point I H → Point I H → Point I H}
    (hf : Invariant f) (x y : Point I H) : (f x y).1 = x.1 ∨ (f x y).1 = y.1 := by
  by_contra hn
  push Not at hn
  obtain ⟨z,hz⟩ := exists_ne (1 : H)
  let s : I → H := fun i => if i = (f x y).1 then z else 1
  have he := hf s x y
  change shift s (f x y) = f (shift s x) (shift s y) at he
  have hx : shift s x = x := by simp [shift,s,Ne.symm hn.1]
  have hy : shift s y = y := by simp [shift,s,Ne.symm hn.2]
  rw [hx,hy] at he
  have hh := congrArg Prod.snd he
  simp [shift,s] at hh
  exact hz hh

omit [DecidableEq I] in
lemma equal_transport {f g : Point I H → Point I H → Point I H}
    (hf : Invariant f) (hg : Invariant g) (s : I → H) (x y : Point I H)
    (h : f x y = g x y) : f (shift s x) (shift s y) = g (shift s x) (shift s y) :=
  (hf s x y).symm.trans ((congrArg (shift s) h).trans (hg s x y))

theorem determined {f g : Point I H → Point I H → Point I H}
    (hf : Invariant f) (hg : Invariant g)
    (hl : ∀ i z, f (i,1) (i,z) = g (i,1) (i,z))
    (hc : ∀ i j, i ≠ j → f (i,1) (j,1) = g (i,1) (j,1)) : f = g := by
  funext ⟨i,a⟩ ⟨j,b⟩
  by_cases h : i = j
  · subst j
    simpa [shift,mul_assoc] using
      equal_transport hf hg (fun _ => a) (i,1) (i,a⁻¹*b) (hl i (a⁻¹*b))
  · let s : I → H := fun k => if k = i then a else if k = j then b else 1
    simpa [shift,s,Ne.symm h] using equal_transport hf hg s (i,1) (j,1) (hc i j h)

def parameters (f : Point I H → Point I H → Point I H) : Params I H :=
  (fun i z => (f (i,1) (i,z)).2,
   fun p => (decide ((f (p.val.1,1) (p.val.2,1)).1 = p.val.1),
     (f (p.val.1,1) (p.val.2,1)).2))

theorem reconstruct [Nontrivial H] {f : Point I H → Point I H → Point I H}
    (hf : Invariant f) : table (parameters f) = f := by
  apply determined (table_invariant _) hf
  · intro i z
    have h := support hf (i,1) (i,z)
    simp only [or_self] at h
    apply Prod.ext
    · simpa [table] using h.symm
    · simp [table,parameters,localOp]
  · intro i j hij
    have h := support hf (i,1) (j,1)
    by_cases hi : (f (i,1) (j,1)).1 = i
    · apply Prod.ext
      · simp [table,parameters,hij,hi]
      · simp [table,parameters,hij,hi]
    · have hj := h.resolve_left hi
      apply Prod.ext
      · simpa [table,parameters,hij,hi] using hj.symm
      · simp [table,parameters,hij,hi]

theorem parameters_table (c : Params I H) : parameters (table c) = c := by
  apply Prod.ext
  · funext i z
    simp [parameters,table,localOp]
  · funext ⟨⟨i,j⟩,hij⟩
    rcases hq : c.2 ⟨(i,j),hij⟩ with ⟨b,v⟩
    cases b <;> simp [parameters,table,hij,hq,Ne.symm hij]

lemma eval_same (c : Params I H) (i : I) (v : ℕ → H) (t : FreeMagma ℕ) :
    @FreeMagma.evalInMagma _ _ ⟨table c⟩ (fun a => (i,v a)) t =
      (i, @FreeMagma.evalInMagma _ _ ⟨localOp (c.1 i)⟩ v t) := by
  induction t with
  | Leaf a => rfl
  | Fork l r hl hr =>
    change table c _ _ = (i,localOp (c.1 i) _ _)
    rw [hl,hr,same]

lemma eval_shift (p : H → H) (s : H) (v : ℕ → H) (t : FreeMagma ℕ) :
    @FreeMagma.evalInMagma _ _ ⟨localOp p⟩ (fun a => s * v a) t =
      s * @FreeMagma.evalInMagma _ _ ⟨localOp p⟩ v t := by
  induction t with
  | Leaf a => rfl
  | Fork l r hl hr =>
    change localOp p _ _ = s * localOp p _ _
    rw [hl,hr,← local_shift]

theorem local_law [Nontrivial H] {A : NatMagmaLaw}
    {f : Point I H → Point I H → Point I H}
    (hf : Invariant f) (hA : @satisfies _ (Point I H) ⟨f⟩ A) (i : I) :
    @satisfies _ H ⟨localOp ((parameters f).1 i)⟩ A := by
  rw [← reconstruct hf] at hA
  intro v
  have h := hA (fun a => (i,v a))
  change @FreeMagma.evalInMagma _ _ ⟨table (parameters f)⟩ _ A.lhs =
    @FreeMagma.evalInMagma _ _ ⟨table (parameters f)⟩ _ A.rhs at h
  rw [eval_same,eval_same] at h
  exact congrArg Prod.snd h

/-- Equivariance makes the valuation at the identity sufficient. -/
def LocalHolds (A : NatMagmaLaw) (p : H → H) : Prop :=
  @satisfiesPhi ℕ H ⟨localOp p⟩ (fun _ => 1) A

instance [DecidableEq H] (A : NatMagmaLaw) (p : H → H) : Decidable (LocalHolds A p) := by
  unfold LocalHolds satisfiesPhi
  infer_instance

abbrev LocalChoices (A : NatMagmaLaw) (H : Type) [Group H] := {p : H → H // LocalHolds A p}
abbrev Code (A : NatMagmaLaw) (I H : Type) [Group H] :=
  (I → LocalChoices A H) × (Cross I → Bool × H)

def localCount [Fintype H] [DecidableEq H] (A : NatMagmaLaw) :=
  Fintype.card (LocalChoices A H)

def codeParams {A : NatMagmaLaw} (c : Code A I H) : Params I H :=
  (fun i => (c.1 i).val, c.2)

theorem table_law {A : NatMagmaLaw} (hA : PairSwapCounting.unaryLaw A = true) (c : Code A I H) :
    @satisfies _ (Point I H) ⟨table (codeParams c)⟩ A := by
  letI : Magma (Point I H) := ⟨table (codeParams c)⟩
  intro v
  have h : PairSwapCounting.unaryTerm A.lhs = true ∧ PairSwapCounting.unaryTerm A.rhs = true := by
    simpa [PairSwapCounting.unaryLaw] using hA
  change @FreeMagma.evalInMagma _ _ ⟨table (codeParams c)⟩ v A.lhs =
    @FreeMagma.evalInMagma _ _ ⟨table (codeParams c)⟩ v A.rhs
  rw [PairSwapCounting.eval_unary _ _ h.1, PairSwapCounting.eval_unary _ _ h.2]
  rcases hv : v 0 with ⟨i,b⟩
  simp only [eval_same]
  apply congrArg (Prod.mk i)
  have he := congrArg (fun z : H => b*z) (c.1 i).property
  simpa only [LocalHolds,satisfiesPhi,← eval_shift,mul_one] using he

def encode [Nontrivial H] {A : NatMagmaLaw}
    (f : RestrictedTables A (Point I H) Invariant) : Code A I H :=
  (fun i => ⟨(parameters f.val).1 i,
    local_law f.property.2 f.property.1 i (fun _ => 1)⟩,
   (parameters f.val).2)

def decode {A : NatMagmaLaw} (hA : PairSwapCounting.unaryLaw A = true) (c : Code A I H) :
    RestrictedTables A (Point I H) Invariant :=
  ⟨table (codeParams c), table_law hA c, table_invariant _⟩

def invariantEquiv [Nontrivial H] {A : NatMagmaLaw} (hA : PairSwapCounting.unaryLaw A = true) :
    RestrictedTables A (Point I H) Invariant ≃ Code A I H where
  toFun := encode
  invFun := decode hA
  left_inv f := by
    apply Subtype.ext
    exact reconstruct f.property.2
  right_inv c := by
    have h := parameters_table (codeParams c)
    apply Prod.ext
    · funext i
      apply Subtype.ext
      exact congrFun (congrArg Prod.fst h) i
    · exact congrArg (fun p : Params I H => p.2) h

theorem invariant_count [Fintype I] [Fintype H] [DecidableEq H] [Nontrivial H]
    {A : NatMagmaLaw} (hA : PairSwapCounting.unaryLaw A = true) :
    Nat.card (RestrictedTables A (Point I H) Invariant) =
      localCount (H := H) A ^ Fintype.card I *
        (2 * Fintype.card H) ^ Fintype.card (Cross I) := by
  classical
  have h := Nat.card_congr (invariantEquiv (I := I) (H := H) hA)
  simpa only [Nat.card_eq_fintype_card, Code, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, localCount] using h

theorem not_structural [Fintype H] [DecidableEq H] [Nontrivial H] {A B : NatMagmaLaw}
    (hA : PairSwapCounting.unaryLaw A = true) (hB : PairSwapCounting.unaryLaw B = true)
    (hpos : 0 < localCount (H := H) B) (hgap : localCount (H := H) B < localCount (H := H) A) :
    ¬ B.StructuralFrom A := by
  intro h
  obtain ⟨K,hK⟩ := bounded_restricted_counts A B h
  let I := Fin (K * localCount (H := H) B + 1)
  have hc := hK (Point I H) Invariant (by
    intro M N q hq hp s
    exact Magma.IsEndo.of_definable hq.definable (hp s))
  rw [invariant_count hA, invariant_count hB] at hc
  simp only [I,Fintype.card_fin] at hc
  have hlt := Nat.mul_lt_mul_of_pos_right (PairSwapCounting.numerical_gap K _ _ hpos hgap)
    (show 0 < (2 * Fintype.card H) ^ Fintype.card (Cross I) by positivity)
  exact (not_lt_of_ge hc) (by simpa only [Nat.mul_assoc] using hlt)

end RegularBlockCounting

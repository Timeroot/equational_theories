import equational_theories.Definability.FOInvariantCompactness
import equational_theories.Equations.All
import Mathlib.Tactic

/-! Operations on independently swappable pairs. Their off-block data have four
choices per ordered pair of blocks; a unary law constrains only the two local
bits in each block. This makes exponential ratios visible to FO compactness. -/

open Law Law.MagmaLaw
namespace PairSwapCounting

variable {I : Type} [DecidableEq I]
abbrev Point (I : Type) := I × Bool
abbrev Cross (I : Type) := {p : I × I // p.1 ≠ p.2}
abbrev Params (I : Type) := (I → Bool × Bool) × (Cross I → Bool × Bool)

def flip (s : I → Bool) (x : Point I) : Point I := (x.1, x.2 ^^ s x.1)

def flipPerm (s : I → Bool) : Equiv.Perm (Point I) where
  toFun := flip s
  invFun := flip s
  left_inv x := by rcases x with ⟨i,b⟩; cases b <;> cases h : s i <;> simp [flip,h]
  right_inv x := by rcases x with ⟨i,b⟩; cases b <;> cases h : s i <;> simp [flip,h]

def Invariant (f : Point I → Point I → Point I) : Prop :=
  ∀ s, (Magma.mk f).IsEndo (flipPerm s)

def localOp (p : Bool × Bool) (a b : Bool) := a ^^ (if a = b then p.1 else p.2)

def table (c : Params I) (x y : Point I) : Point I :=
  if h : x.1 = y.1 then (x.1, localOp (c.1 x.1) x.2 y.2)
  else let q := c.2 ⟨(x.1,y.1),h⟩
       if q.1 then (x.1,x.2 ^^ q.2) else (y.1,y.2 ^^ q.2)

lemma same (c : Params I) (i : I) (a b : Bool) :
    table c (i,a) (i,b) = (i,localOp (c.1 i) a b) := by simp [table]

lemma xor_shuffle (a b c : Bool) : ((a ^^ b) ^^ c) = ((a ^^ c) ^^ b) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma local_flip (p : Bool × Bool) (a b s : Bool) :
    (localOp p a b ^^ s) = localOp p (a ^^ s) (b ^^ s) := by
  rcases p with ⟨d,q⟩
  cases d <;> cases q <;> cases a <;> cases b <;> cases s <;> decide

theorem table_invariant (c : Params I) : Invariant (table c) := by
  intro s ⟨i,a⟩ ⟨j,b⟩
  change flip s (table c (i,a) (j,b)) = table c (flip s (i,a)) (flip s (j,b))
  by_cases h : i = j
  · subst j
    simp only [same, flip]
    exact congrArg (Prod.mk i) (local_flip _ _ _ _)
  · simp only [table, flip, dif_neg h]
    split_ifs
    · exact congrArg (Prod.mk i) (xor_shuffle _ _ _)
    · exact congrArg (Prod.mk j) (xor_shuffle _ _ _)

theorem support {f : Point I → Point I → Point I} (hf : Invariant f) (x y : Point I) :
    (f x y).1 = x.1 ∨ (f x y).1 = y.1 := by
  by_contra hn
  push Not at hn
  let s : I → Bool := fun i => decide (i = (f x y).1)
  have he := hf s x y
  change flip s (f x y) = f (flip s x) (flip s y) at he
  have hx : flip s x = x := by simp [flip,s,Ne.symm hn.1]
  have hy : flip s y = y := by simp [flip,s,Ne.symm hn.2]
  rw [hx,hy] at he
  have hh := congrArg Prod.snd he
  simp [flip,s] at hh

omit [DecidableEq I] in
lemma equal_transport {f g : Point I → Point I → Point I}
    (hf : Invariant f) (hg : Invariant g) (s : I → Bool) (x y : Point I)
    (h : f x y = g x y) : f (flip s x) (flip s y) = g (flip s x) (flip s y) :=
  (hf s x y).symm.trans ((congrArg (flip s) h).trans (hg s x y))

theorem determined {f g : Point I → Point I → Point I}
    (hf : Invariant f) (hg : Invariant g)
    (hd : ∀ i, f (i,false) (i,false) = g (i,false) (i,false))
    (hp : ∀ i, f (i,false) (i,true) = g (i,false) (i,true))
    (hc : ∀ i j, i ≠ j → f (i,false) (j,false) = g (i,false) (j,false)) : f = g := by
  funext ⟨i,a⟩ ⟨j,b⟩
  by_cases h : i = j
  · subst j
    cases a <;> cases b
    · exact hd i
    · exact hp i
    · simpa [flip] using equal_transport hf hg (fun _ => true) (i,false) (i,true) (hp i)
    · simpa [flip] using equal_transport hf hg (fun _ => true) (i,false) (i,false) (hd i)
  · let s : I → Bool := fun k => if k = i then a else if k = j then b else false
    simpa [flip,s,Ne.symm h] using equal_transport hf hg s (i,false) (j,false) (hc i j h)

def parameters (f : Point I → Point I → Point I) : Params I :=
  (fun i => ((f (i,false) (i,false)).2, (f (i,false) (i,true)).2),
   fun p => (decide ((f (p.val.1,false) (p.val.2,false)).1 = p.val.1),
     (f (p.val.1,false) (p.val.2,false)).2))

theorem reconstruct {f : Point I → Point I → Point I} (hf : Invariant f) :
    table (parameters f) = f := by
  apply determined (table_invariant _) hf
  · intro i
    have h := support hf (i,false) (i,false)
    simp only [or_self] at h
    apply Prod.ext
    · simpa [table] using h.symm
    · simp [table,parameters,localOp]
  · intro i
    have h := support hf (i,false) (i,true)
    simp only [or_self] at h
    apply Prod.ext
    · simpa [table] using h.symm
    · simp [table,parameters,localOp]
  · intro i j hij
    have h := support hf (i,false) (j,false)
    by_cases hi : (f (i,false) (j,false)).1 = i
    · apply Prod.ext
      · simp [table,parameters,hij,hi]
      · simp [table,parameters,hij,hi]
    · have hj := h.resolve_left hi
      apply Prod.ext
      · simpa [table,parameters,hij,hi] using hj.symm
      · simp [table,parameters,hij,hi]

theorem parameters_table (c : Params I) : parameters (table c) = c := by
  apply Prod.ext
  · funext i
    simp [parameters,table,localOp]
  · funext ⟨⟨i,j⟩,hij⟩
    rcases hq : c.2 ⟨(i,j),hij⟩ with ⟨b,v⟩
    cases b <;> simp [parameters,table,hij,hq,Ne.symm hij]

theorem table_injective : Function.Injective (table (I := I)) := by
  intro c d h
  simpa only [parameters_table] using congrArg parameters h

lemma eval_same (c : Params I) (i : I) (v : ℕ → Bool) (t : FreeMagma ℕ) :
    @FreeMagma.evalInMagma _ _ ⟨table c⟩ (fun a => (i,v a)) t =
      (i, @FreeMagma.evalInMagma _ _ ⟨localOp (c.1 i)⟩ v t) := by
  induction t with
  | Leaf a => rfl
  | Fork l r hl hr =>
    change table c _ _ = (i,localOp (c.1 i) _ _)
    rw [hl,hr,same]

/-- Restrict any law to one pair, which is a submagma. -/
theorem local_law {B : NatMagmaLaw} {f : Point I → Point I → Point I}
    (hf : Invariant f) (hB : @satisfies _ (Point I) ⟨f⟩ B) (i : I) :
    @satisfies _ Bool ⟨localOp ((parameters f).1 i)⟩ B := by
  rw [← reconstruct hf] at hB
  intro v
  have h := hB (fun a => (i,v a))
  change @FreeMagma.evalInMagma _ _ ⟨table (parameters f)⟩ _ B.lhs =
    @FreeMagma.evalInMagma _ _ ⟨table (parameters f)⟩ _ B.rhs at h
  rw [eval_same,eval_same] at h
  exact congrArg Prod.snd h


/-- Both sides of the law use only variable zero. -/
def unaryTerm : FreeMagma ℕ → Bool
  | .Leaf a => a == 0
  | .Fork l r => unaryTerm l && unaryTerm r

def unaryLaw (A : NatMagmaLaw) : Bool := unaryTerm A.lhs && unaryTerm A.rhs

lemma eval_unary {G : Type} [Magma G] (v : ℕ → G) (t : FreeMagma ℕ)
    (ht : unaryTerm t = true) :
    FreeMagma.evalInMagma v t = FreeMagma.evalInMagma (fun _ => v 0) t := by
  induction t with
  | Leaf a =>
    have ha : a = 0 := by simpa [unaryTerm] using ht
    subst a
    rfl
  | Fork l r hl hr =>
    have h : unaryTerm l = true ∧ unaryTerm r = true := by simpa [unaryTerm] using ht
    exact congrArg₂ Magma.op (hl h.1) (hr h.2)

/-- A finite test: evaluate the law at both constant Boolean valuations. -/
def LocalHolds (A : NatMagmaLaw) (p : Bool × Bool) : Prop :=
  ∀ b : Bool, @satisfiesPhi ℕ Bool ⟨localOp p⟩ (fun _ => b) A

instance (A : NatMagmaLaw) (p : Bool × Bool) : Decidable (LocalHolds A p) := by
  unfold LocalHolds satisfiesPhi
  infer_instance

abbrev LocalChoices (A : NatMagmaLaw) := {p : Bool × Bool // LocalHolds A p}
abbrev Code (A : NatMagmaLaw) (I : Type) := (I → LocalChoices A) × (Cross I → Bool × Bool)

def localCount (A : NatMagmaLaw) := Fintype.card (LocalChoices A)

def codeParams {A : NatMagmaLaw} (c : Code A I) : Params I :=
  (fun i => (c.1 i).val, c.2)

theorem table_law {A : NatMagmaLaw} (hA : unaryLaw A = true) (c : Code A I) :
    @satisfies _ (Point I) ⟨table (codeParams c)⟩ A := by
  letI : Magma (Point I) := ⟨table (codeParams c)⟩
  intro v
  have h : unaryTerm A.lhs = true ∧ unaryTerm A.rhs = true := by simpa [unaryLaw] using hA
  change @FreeMagma.evalInMagma _ _ ⟨table (codeParams c)⟩ v A.lhs =
    @FreeMagma.evalInMagma _ _ ⟨table (codeParams c)⟩ v A.rhs
  rw [eval_unary _ _ h.1, eval_unary _ _ h.2]
  rcases hv : v 0 with ⟨i,b⟩
  simp only [eval_same]
  exact congrArg (Prod.mk i) ((c.1 i).property b)

open FORecoveryCompactness

def encode {A : NatMagmaLaw} (f : RestrictedTables A (Point I) Invariant) : Code A I :=
  (fun i => ⟨(parameters f.val).1 i,
    fun b => local_law f.property.2 f.property.1 i (fun _ => b)⟩,
   (parameters f.val).2)

def decode {A : NatMagmaLaw} (hA : unaryLaw A = true) (c : Code A I) :
    RestrictedTables A (Point I) Invariant :=
  ⟨table (codeParams c), table_law hA c, table_invariant _⟩

def invariantEquiv {A : NatMagmaLaw} (hA : unaryLaw A = true) :
    RestrictedTables A (Point I) Invariant ≃ Code A I where
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
    · exact congrArg (fun p : Params I => p.2) h

/-- Exact count of the tables with the prescribed independent pair swaps.
No enumeration of the large carrier or of its operation tables is needed. -/
theorem invariant_count [Fintype I] {A : NatMagmaLaw} (hA : unaryLaw A = true) :
    Nat.card (RestrictedTables A (Point I) Invariant) =
      localCount A ^ Fintype.card I * 4 ^ Fintype.card (Cross I) := by
  classical
  have h := Nat.card_congr (invariantEquiv (I := I) hA)
  simpa only [Nat.card_eq_fintype_card, Code, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, localCount] using h

/-- Linear growth of the binomial term suffices to beat any proposed multiplier. -/
lemma numerical_gap (K a b : ℕ) (hb : 0 < b) (hab : b < a) :
    K * b ^ (K * b + 1) < a ^ (K * b + 1) := by
  have hbin := pow_add_mul_le_add_pow (a := b) (b := 1) (Nat.zero_le b) (by omega) (K * b + 1)
  have hpow : 0 < b ^ (K * b) := pow_pos hb _
  calc
    K * b ^ (K * b + 1) = (K * b) * b ^ (K * b) := by rw [pow_succ]; ring
    _ < (K * b + 1) * b ^ (K * b) := Nat.mul_lt_mul_of_pos_right (by omega) hpow
    _ ≤ b ^ (K * b + 1) + (K * b + 1) * b ^ (K * b) := Nat.le_add_left _ _
    _ ≤ (b + 1) ^ (K * b + 1) := by simpa using hbin
    _ ≤ a ^ (K * b + 1) := Nat.pow_le_pow_left (by omega) _

/-- Any strict gap between nonzero local counts refutes unrestricted FO recovery. -/
theorem not_structural {A B : NatMagmaLaw} (hA : unaryLaw A = true)
    (hB : unaryLaw B = true) (hpos : 0 < localCount B) (hgap : localCount B < localCount A) :
    ¬ B.StructuralFrom A := by
  intro h
  obtain ⟨K,hK⟩ := bounded_restricted_counts A B h
  let I := Fin (K * localCount B + 1)
  have hc := hK (Point I) Invariant (by
    intro M N q hq hp s
    exact Magma.IsEndo.of_definable hq.definable (hp s))
  rw [invariant_count hA, invariant_count hB] at hc
  simp only [I,Fintype.card_fin] at hc
  have hlt := Nat.mul_lt_mul_of_pos_right (numerical_gap K _ _ hpos hgap)
    (show 0 < 4 ^ Fintype.card (Cross I) by positivity)
  exact (not_lt_of_ge hc) (by simpa only [Nat.mul_assoc] using hlt)

end PairSwapCounting

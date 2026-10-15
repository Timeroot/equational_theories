import equational_theories.Definability.RegularBlockCounting

/-! Independent regular group actions with one shared fixed point.
The fixed point lets unary terms leave their original free orbit. Counting these
operations therefore distinguishes laws that all unpointed regular counts miss. -/

open Law Law.MagmaLaw FORecoveryCompactness
namespace PointedBlockCounting

variable {I H : Type} [DecidableEq I] [Group H]
abbrev Point (I H : Type) := Option (I × H)
abbrev Cross (I : Type) := RegularBlockCounting.Cross I
abbrev LocalParam (H : Type) := (H → Option H) × Option H × Option H
abbrev Params (I H : Type) := (I → LocalParam H) × (Cross I → Option (Bool × H))

def put (i : I) (x : Option H) : Point I H := x.map (Prod.mk i)
def forget (x : Point I H) : Option H := x.map Prod.snd

def scale (s : H) (x : Option H) : Option H := x.map (s * ·)
def shift (s : I → H) (x : Point I H) : Point I H := x.map (fun p => (p.1,s p.1 * p.2))

def shiftPerm (s : I → H) : Equiv.Perm (Point I H) where
  toFun := shift s
  invFun := shift (fun i => (s i)⁻¹)
  left_inv x := by cases x <;> simp [shift]
  right_inv x := by cases x <;> simp [shift]

def Invariant (f : Point I H → Point I H → Point I H) : Prop :=
  ∀ s, (Magma.mk f).IsEndo (shiftPerm s)

def localOp (p : LocalParam H) : Option H → Option H → Option H
  | none,none => none
  | some a,none => scale a p.2.1
  | none,some b => scale b p.2.2
  | some a,some b => scale a (p.1 (a⁻¹*b))

def table (c : Params I H) : Point I H → Point I H → Point I H
  | none,none => none
  | some (i,a),none => put i (localOp (c.1 i) (some a) none)
  | none,some (j,b) => put j (localOp (c.1 j) none (some b))
  | some (i,a),some (j,b) =>
      if h : i = j then put i (localOp (c.1 i) (some a) (some b))
      else (c.2 ⟨(i,j),h⟩).map (fun q => if q.1 then (i,a*q.2) else (j,b*q.2))

omit [DecidableEq I] in
lemma shift_put (s : I → H) (i : I) (x : Option H) :
    shift s (put i x) = put i (scale (s i) x) := by cases x <;> rfl

lemma same (c : Params I H) (i : I) (a b : Option H) :
    table c (put i a) (put i b) = put i (localOp (c.1 i) a b) := by
  cases a <;> cases b <;> simp [put,table,localOp]

lemma scale_scale (s a : H) (x : Option H) : scale s (scale a x) = scale (s*a) x := by
  cases x <;> simp [scale,mul_assoc]

lemma local_shift (p : LocalParam H) (s : H) (a b : Option H) :
    scale s (localOp p a b) = localOp p (scale s a) (scale s b) := by
  cases a <;> cases b <;> simp [scale,localOp,Option.map_map,Function.comp_def,mul_assoc]

theorem table_invariant (c : Params I H) : Invariant (table c) := by
  intro s x y
  change shift s (table c x y) = table c (shift s x) (shift s y)
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      rcases y with ⟨i,b⟩
      change shift s (put i (scale b (c.1 i).2.2)) = put i (scale (s i*b) (c.1 i).2.2)
      rw [shift_put,scale_scale]
  | some x =>
    rcases x with ⟨i,a⟩
    cases y with
    | none =>
      change shift s (put i (scale a (c.1 i).2.1)) = put i (scale (s i*a) (c.1 i).2.1)
      rw [shift_put,scale_scale]
    | some y =>
      rcases y with ⟨j,b⟩
      by_cases h : i = j
      · subst j
        change shift s (table c (put i (some a)) (put i (some b))) =
          table c (put i (scale (s i) (some a))) (put i (scale (s i) (some b)))
        rw [same,same,shift_put,local_shift]
      · simp only [table,dif_neg h,shift,Option.map_some]
        cases hq : c.2 ⟨(i,j),h⟩ with
        | none => rfl
        | some q =>
          rcases q with ⟨b,z⟩
          cases b <;> simp [mul_assoc]

/-- Outputs lie in an input orbit or at the shared fixed point. -/
theorem support [Nontrivial H] {f : Point I H → Point I H → Point I H}
    (hf : Invariant f) (x y : Point I H) :
    (f x y).map Prod.fst = none ∨ (f x y).map Prod.fst = x.map Prod.fst ∨
      (f x y).map Prod.fst = y.map Prod.fst := by
  cases he : f x y with
  | none => simp
  | some v =>
    rcases v with ⟨i,a⟩
    simp only [Option.map_some,reduceCtorEq,false_or]
    by_contra hn
    push Not at hn
    obtain ⟨z,hz⟩ := exists_ne (1 : H)
    let s : I → H := fun j => if j = i then z else 1
    have fixed (w : Point I H) (hw : some i ≠ w.map Prod.fst) : shift s w = w := by
      cases w with
      | none => rfl
      | some w =>
        rcases w with ⟨j,b⟩
        have hj : j ≠ i := by intro h; subst j; exact hw rfl
        simp [shift,s,hj]
    have hh := hf s x y
    change shift s (f x y) = f (shift s x) (shift s y) at hh
    rw [fixed x hn.1,fixed y hn.2,he] at hh
    have hz' : z*a=a := by simpa [shift,s,forget] using congrArg (fun w => (forget w)) hh
    exact hz (by simpa using hz')

theorem root_fixed [Nontrivial H] {f : Point I H → Point I H → Point I H}
    (hf : Invariant f) : f none none = none := by
  have h := support hf none none
  cases he : f none none <;> simp_all

theorem block_closed [Nontrivial H] {f : Point I H → Point I H → Point I H}
    (hf : Invariant f) (i : I) (a b : Option H) :
    put i (forget (f (put i a) (put i b))) = f (put i a) (put i b) := by
  have h := support hf (put i a) (put i b)
  cases he : f (put i a) (put i b) with
  | none => rfl
  | some v =>
    rcases v with ⟨j,z⟩
    have hj : j=i := by
      cases a <;> cases b <;> simp_all [put]
    subst j
    rfl

omit [DecidableEq I] in
lemma equal_transport {f g : Point I H → Point I H → Point I H}
    (hf : Invariant f) (hg : Invariant g) (s : I → H) (x y : Point I H)
    (h : f x y = g x y) : f (shift s x) (shift s y) = g (shift s x) (shift s y) :=
  (hf s x y).symm.trans ((congrArg (shift s) h).trans (hg s x y))

theorem determined {f g : Point I H → Point I H → Point I H}
    (hf : Invariant f) (hg : Invariant g) (h0 : f none none = g none none)
    (hl : ∀ i z, f (some (i,1)) (some (i,z)) = g (some (i,1)) (some (i,z)))
    (hr : ∀ i, f (some (i,1)) none = g (some (i,1)) none)
    (hlr : ∀ i, f none (some (i,1)) = g none (some (i,1)))
    (hc : ∀ i j, i ≠ j → f (some (i,1)) (some (j,1)) = g (some (i,1)) (some (j,1))) : f = g := by
  funext x y
  cases x with
  | none =>
    cases y with
    | none => exact h0
    | some y =>
      rcases y with ⟨i,b⟩
      simpa [shift] using equal_transport hf hg (fun _ => b) none (some (i,1)) (hlr i)
  | some x =>
    rcases x with ⟨i,a⟩
    cases y with
    | none => simpa [shift] using equal_transport hf hg (fun _ => a) (some (i,1)) none (hr i)
    | some y =>
      rcases y with ⟨j,b⟩
      by_cases h : i=j
      · subst j
        simpa [shift,mul_assoc] using equal_transport hf hg (fun _ => a)
          (some (i,1)) (some (i,a⁻¹*b)) (hl i (a⁻¹*b))
      · let s : I → H := fun k => if k=i then a else if k=j then b else 1
        simpa [shift,s,Ne.symm h] using equal_transport hf hg s (some (i,1)) (some (j,1)) (hc i j h)

def parameters (f : Point I H → Point I H → Point I H) : Params I H :=
  (fun i => (fun z => forget (f (some (i,1)) (some (i,z))),
    forget (f (some (i,1)) none),forget (f none (some (i,1)))),
   fun p => (f (some (p.val.1,1)) (some (p.val.2,1))).map
     (fun q => (decide (q.1 = p.val.1),q.2)))

theorem reconstruct [Nontrivial H] {f : Point I H → Point I H → Point I H}
    (hf : Invariant f) : table (parameters f) = f := by
  apply determined (table_invariant _) hf
  · exact (root_fixed hf).symm
  · intro i z
    simpa [table,localOp,parameters,scale] using block_closed hf i (some 1) (some z)
  · intro i
    simpa [table,localOp,parameters,scale] using block_closed hf i (some 1) none
  · intro i
    simpa [table,localOp,parameters,scale] using block_closed hf i none (some 1)
  · intro i j hij
    have h := support hf (some (i,1)) (some (j,1))
    cases he : f (some (i,1)) (some (j,1)) with
    | none => simp [table,parameters,hij,he]
    | some v =>
      rcases v with ⟨k,z⟩
      have hk : k=i ∨ k=j := by simpa [he] using h
      rcases hk with rfl | rfl <;> simp [table,parameters,hij,he,Ne.symm hij]

theorem parameters_table (c : Params I H) : parameters (table c) = c := by
  apply Prod.ext
  · funext i
    apply Prod.ext
    · funext z
      simp [parameters,table,localOp,scale,put,forget]
    · apply Prod.ext <;> simp [parameters,table,localOp,scale,put,forget]
  · funext ⟨⟨i,j⟩,hij⟩
    cases hq : c.2 ⟨(i,j),hij⟩ with
    | none => simp [parameters,table,hij,hq]
    | some q =>
      rcases q with ⟨b,z⟩
      cases b <;> simp [parameters,table,hij,hq,Ne.symm hij]

lemma eval_same (c : Params I H) (i : I) (v : ℕ → Option H) (t : FreeMagma ℕ) :
    @FreeMagma.evalInMagma _ _ ⟨table c⟩ (fun a => put i (v a)) t =
      put i (@FreeMagma.evalInMagma _ _ ⟨localOp (c.1 i)⟩ v t) := by
  induction t with
  | Leaf a => rfl
  | Fork l r hl hr =>
    change table c _ _ = put i (localOp (c.1 i) _ _)
    rw [hl,hr,same]

lemma eval_shift (p : LocalParam H) (s : H) (v : ℕ → Option H) (t : FreeMagma ℕ) :
    @FreeMagma.evalInMagma _ _ ⟨localOp p⟩ (fun a => scale s (v a)) t =
      scale s (@FreeMagma.evalInMagma _ _ ⟨localOp p⟩ v t) := by
  induction t with
  | Leaf a => rfl
  | Fork l r hl hr =>
    change localOp p _ _ = scale s (localOp p _ _)
    rw [hl,hr,← local_shift]

lemma eval_root (c : Params I H) (t : FreeMagma ℕ) :
    @FreeMagma.evalInMagma _ _ ⟨table c⟩ (fun _ => none) t = none := by
  induction t with
  | Leaf a => rfl
  | Fork l r hl hr =>
    change table c _ _ = none
    rw [hl,hr]
    rfl

theorem local_law [Nontrivial H] {A : NatMagmaLaw}
    {f : Point I H → Point I H → Point I H}
    (hf : Invariant f) (hA : @satisfies _ (Point I H) ⟨f⟩ A) (i : I) :
    @satisfies _ (Option H) ⟨localOp ((parameters f).1 i)⟩ A := by
  rw [← reconstruct hf] at hA
  intro v
  have h := hA (fun a => put i (v a))
  change @FreeMagma.evalInMagma _ _ ⟨table (parameters f)⟩ _ A.lhs =
    @FreeMagma.evalInMagma _ _ ⟨table (parameters f)⟩ _ A.rhs at h
  rw [eval_same,eval_same] at h
  have hi : Function.Injective (put i : Option H → Point I H) := by
    intro x y h
    cases x <;> cases y <;> simp_all [put]
  exact hi h

/-- The shared root satisfies every unary law automatically. Test one free point. -/
def LocalHolds (A : NatMagmaLaw) (p : LocalParam H) : Prop :=
  @satisfiesPhi ℕ (Option H) ⟨localOp p⟩ (fun _ => some 1) A

instance [DecidableEq H] (A : NatMagmaLaw) (p : LocalParam H) : Decidable (LocalHolds A p) := by
  unfold LocalHolds satisfiesPhi
  infer_instance

abbrev LocalChoices (A : NatMagmaLaw) (H : Type) [Group H] := {p : LocalParam H // LocalHolds A p}
abbrev Code (A : NatMagmaLaw) (I H : Type) [Group H] :=
  (I → LocalChoices A H) × (Cross I → Option (Bool × H))

def localCount [Fintype H] [DecidableEq H] (A : NatMagmaLaw) :=
  Fintype.card (LocalChoices A H)

def codeParams {A : NatMagmaLaw} (c : Code A I H) : Params I H :=
  (fun i => (c.1 i).val,c.2)

theorem table_law {A : NatMagmaLaw} (hA : PairSwapCounting.unaryLaw A = true) (c : Code A I H) :
    @satisfies _ (Point I H) ⟨table (codeParams c)⟩ A := by
  letI : Magma (Point I H) := ⟨table (codeParams c)⟩
  intro v
  have h : PairSwapCounting.unaryTerm A.lhs = true ∧ PairSwapCounting.unaryTerm A.rhs = true := by
    simpa [PairSwapCounting.unaryLaw] using hA
  change @FreeMagma.evalInMagma _ _ ⟨table (codeParams c)⟩ v A.lhs =
    @FreeMagma.evalInMagma _ _ ⟨table (codeParams c)⟩ v A.rhs
  rw [PairSwapCounting.eval_unary _ _ h.1,PairSwapCounting.eval_unary _ _ h.2]
  cases hv : v 0 with
  | none => rw [eval_root,eval_root]
  | some w =>
    rcases w with ⟨i,b⟩
    change @FreeMagma.evalInMagma _ _ ⟨table (codeParams c)⟩ (fun _ => put i (some b)) A.lhs =
      @FreeMagma.evalInMagma _ _ ⟨table (codeParams c)⟩ (fun _ => put i (some b)) A.rhs
    rw [eval_same,eval_same]
    apply congrArg (put i)
    have he := congrArg (scale b) (c.1 i).property
    change scale b (@FreeMagma.evalInMagma _ _ ⟨localOp (c.1 i).val⟩ (fun _ => some 1) A.lhs) =
      scale b (@FreeMagma.evalInMagma _ _ ⟨localOp (c.1 i).val⟩ (fun _ => some 1) A.rhs) at he
    rw [← eval_shift,← eval_shift] at he
    simpa only [scale,Option.map_some,mul_one] using he

def encode [Nontrivial H] {A : NatMagmaLaw}
    (f : RestrictedTables A (Point I H) Invariant) : Code A I H :=
  (fun i => ⟨(parameters f.val).1 i,
    local_law f.property.2 f.property.1 i (fun _ => some 1)⟩,
   (parameters f.val).2)

def decode {A : NatMagmaLaw} (hA : PairSwapCounting.unaryLaw A = true) (c : Code A I H) :
    RestrictedTables A (Point I H) Invariant :=
  ⟨table (codeParams c),table_law hA c,table_invariant _⟩

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
        (2 * Fintype.card H + 1) ^ Fintype.card (Cross I) := by
  classical
  have h := Nat.card_congr (invariantEquiv (I := I) (H := H) hA)
  simpa only [Nat.card_eq_fintype_card,Code,Fintype.card_prod,Fintype.card_fun,
    Fintype.card_option,Fintype.card_bool,localCount] using h

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
  rw [invariant_count hA,invariant_count hB] at hc
  simp only [I,Fintype.card_fin] at hc
  have hlt := Nat.mul_lt_mul_of_pos_right (PairSwapCounting.numerical_gap K _ _ hpos hgap)
    (show 0 < (2 * Fintype.card H + 1) ^ Fintype.card (Cross I) by positivity)
  exact (not_lt_of_ge hc) (by simpa only [Nat.mul_assoc] using hlt)

end PointedBlockCounting

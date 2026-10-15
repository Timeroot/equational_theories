import equational_theories.Definability.PointedIdentityCounting

/-! A unary term shared by all elements must equal the common fixed point in
an invariant pointed-block magma. Making two unary terms return that point
therefore supplies freely gluable models of `s(x) = t(y)`. -/
open Law Law.MagmaLaw FORecoveryCompactness PointedBlockCounting
namespace ConstantTermBlockCounting

variable {I H : Type} [DecidableEq I] [Group H]

def sourceLaw (s t : FreeMagma ℕ) : NatMagmaLaw :=
  ⟨FreeMagma.fmapHom (fun _ => 0) s, FreeMagma.fmapHom (fun _ => 1) t⟩

def SourceHolds (s t : FreeMagma ℕ) (p : LocalParam H) : Prop :=
  @FreeMagma.evalInMagma _ _ ⟨localOp p⟩ (fun _ => some 1) s = none ∧
  @FreeMagma.evalInMagma _ _ ⟨localOp p⟩ (fun _ => some 1) t = none

instance [DecidableEq H] (s t : FreeMagma ℕ) (p : LocalParam H) :
    Decidable (SourceHolds s t p) := by unfold SourceHolds; infer_instance

abbrev Choices (s t : FreeMagma ℕ) (H : Type) [Group H] :=
  {p : LocalParam H // SourceHolds s t p}
abbrev Code (s t : FreeMagma ℕ) (I H : Type) [Group H] :=
  (I → Choices s t H) × (Cross I → Option (Bool × H))

def sourceCount [Fintype H] [DecidableEq H] (s t : FreeMagma ℕ) :=
  Fintype.card (Choices s t H)

def codeParams {s t : FreeMagma ℕ} (c : Code s t I H) : Params I H :=
  (fun i => (c.1 i).val, c.2)

lemma eval_zero (c : Params I H) (t : FreeMagma ℕ)
    (ht : ∀ i, @FreeMagma.evalInMagma _ _ ⟨localOp (c.1 i)⟩ (fun _ => some 1) t = none)
    (a : Point I H) :
    @FreeMagma.evalInMagma _ _ ⟨table c⟩ (fun _ => a) t = none := by
  cases a with
  | none => exact eval_root _ _
  | some w =>
    rcases w with ⟨i,b⟩
    change @FreeMagma.evalInMagma _ _ ⟨table c⟩ (fun _ => put i (some b)) t = none
    rw [eval_same]
    have h := congrArg (scale b) (ht i)
    rw [← eval_shift] at h
    have he : @FreeMagma.evalInMagma _ _ ⟨localOp (c.1 i)⟩ (fun _ => some b) t = none := by
      simpa only [scale,Option.map_some,mul_one,Option.map_none] using h
    rw [he]
    rfl

theorem table_law {s t : FreeMagma ℕ} (c : Code s t I H) :
    @satisfies _ (Point I H) ⟨table (codeParams c)⟩ (sourceLaw s t) := by
  letI : Magma (Point I H) := ⟨table (codeParams c)⟩
  intro v
  change @FreeMagma.evalInMagma _ _ ⟨table (codeParams c)⟩ v
      (FreeMagma.fmapHom (fun _ => 0) s) =
    @FreeMagma.evalInMagma _ _ ⟨table (codeParams c)⟩ v
      (FreeMagma.fmapHom (fun _ => 1) t)
  rw [FreeMagma.evalInMagma_fmapHom,FreeMagma.evalInMagma_fmapHom]
  exact (eval_zero _ s (fun i => (c.1 i).property.1) (v 0)).trans
    (eval_zero _ t (fun i => (c.1 i).property.2) (v 1)).symm

def decode {s t : FreeMagma ℕ} (c : Code s t I H) :
    RestrictedTables (sourceLaw s t) (Point I H) Invariant :=
  ⟨table (codeParams c), table_law c, table_invariant _⟩

theorem decode_injective {s t : FreeMagma ℕ} :
    Function.Injective (decode (I := I) (H := H) (s := s) (t := t)) := by
  intro c d h
  have hh := congrArg (fun f : RestrictedTables (sourceLaw s t) (Point I H) Invariant =>
    parameters f.val) h
  change parameters (table (codeParams c)) = parameters (table (codeParams d)) at hh
  rw [parameters_table,parameters_table] at hh
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact congrFun (congrArg Prod.fst hh) i
  · exact congrArg (fun p : Params I H => p.2) hh

theorem source_lower [Fintype I] [Fintype H] [DecidableEq H] (s t : FreeMagma ℕ) :
    sourceCount (H := H) s t ^ Fintype.card I *
      (2 * Fintype.card H + 1) ^ Fintype.card (Cross I) ≤
      Nat.card (RestrictedTables (sourceLaw s t) (Point I H) Invariant) := by
  classical
  have h := Nat.card_le_card_of_injective (decode (I := I) (H := H) (s := s) (t := t)) decode_injective
  simpa only [Nat.card_eq_fintype_card,Code,Fintype.card_prod,Fintype.card_fun,
    Fintype.card_option,Fintype.card_bool,sourceCount] using h

theorem not_structural [Fintype H] [DecidableEq H] [Nontrivial H]
    {s t : FreeMagma ℕ} {B : NatMagmaLaw}
    (hpos : 0 < PointedIdentityCounting.targetCount (H := H) B)
    (hgap : PointedIdentityCounting.targetCount (H := H) B < sourceCount (H := H) s t) :
    ¬ B.StructuralFrom (sourceLaw s t) := by
  intro h
  obtain ⟨K,hK⟩ := bounded_restricted_counts (sourceLaw s t) B h
  let I := Fin (K * PointedIdentityCounting.targetCount (H := H) B + 1)
  have hc := hK (Point I H) Invariant (by
    intro M N q hq hp u
    exact Magma.IsEndo.of_definable hq.definable (hp u))
  have hle := (source_lower (I := I) (H := H) s t).trans
    (hc.trans (Nat.mul_le_mul_left K (PointedIdentityCounting.target_upper (I := I) (H := H) B)))
  simp only [I,Fintype.card_fin] at hle
  have hlt := Nat.mul_lt_mul_of_pos_right (PairSwapCounting.numerical_gap K _ _ hpos hgap)
    (show 0 < (2 * Fintype.card H + 1) ^ Fintype.card (Cross I) by positivity)
  exact (not_lt_of_ge hle) (by simpa only [Nat.mul_assoc] using hlt)

end ConstantTermBlockCounting

/-- info: 'ConstantTermBlockCounting.not_structural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantTermBlockCounting.not_structural

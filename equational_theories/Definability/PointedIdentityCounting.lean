import equational_theories.Definability.PointedBlockCounting

/-! A common right identity permits completely free products between distinct
regular orbits, even for laws involving two variables. Source models are built
from local unary terms that return the common root. Target models are only
bounded above by their restrictions to each orbit and the root. An exponential
local-count gap contradicts compactness for FO-structural recovery. -/

open Law Law.MagmaLaw FORecoveryCompactness PointedBlockCounting
namespace PointedIdentityCounting

variable {I H : Type} [DecidableEq I] [Group H]

/-- The law `x = x * t(y)`, with every leaf of `t` replaced by `y`. -/
def rightRootLaw (t : FreeMagma ℕ) : NatMagmaLaw :=
  ⟨.Leaf 0, .Fork (.Leaf 0) (FreeMagma.fmapHom (fun _ => 1) t)⟩

def SourceHolds (t : FreeMagma ℕ) (p : LocalParam H) : Prop :=
  p.2.1 = some 1 ∧
    @FreeMagma.evalInMagma _ _ ⟨localOp p⟩ (fun _ => some 1) t = none

instance [DecidableEq H] (t : FreeMagma ℕ) (p : LocalParam H) :
    Decidable (SourceHolds t p) := by unfold SourceHolds; infer_instance

/-- Necessary local tests. These cover all assignments for the catalogue targets,
which use at most variables 0, 1, and 2. Completeness is not needed for the upper bound. -/
def TargetHolds (B : NatMagmaLaw) (p : LocalParam H) : Prop :=
  ∀ x y z : Option H, @satisfiesPhi _ (Option H) ⟨localOp p⟩
    (fun k => if k = 0 then x else if k = 1 then y else z) B

instance [Fintype H] [DecidableEq H] (B : NatMagmaLaw) (p : LocalParam H) :
    Decidable (TargetHolds B p) := by
  unfold TargetHolds satisfiesPhi
  infer_instance

abbrev SourceChoices (t : FreeMagma ℕ) (H : Type) [Group H] :=
  {p : LocalParam H // SourceHolds t p}
abbrev TargetChoices (B : NatMagmaLaw) (H : Type) [Group H] :=
  {p : LocalParam H // TargetHolds B p}
abbrev SourceCode (t : FreeMagma ℕ) (I H : Type) [Group H] :=
  (I → SourceChoices t H) × (Cross I → Option (Bool × H))
abbrev TargetCode (B : NatMagmaLaw) (I H : Type) [Group H] :=
  (I → TargetChoices B H) × (Cross I → Option (Bool × H))

def sourceCount [Fintype H] [DecidableEq H] (t : FreeMagma ℕ) :=
  Fintype.card (SourceChoices t H)
def targetCount [Fintype H] [DecidableEq H] (B : NatMagmaLaw) :=
  Fintype.card (TargetChoices B H)

def sourceParams {t : FreeMagma ℕ} (c : SourceCode t I H) : Params I H :=
  (fun i => (c.1 i).val, c.2)

lemma table_right_root {t : FreeMagma ℕ} (c : SourceCode t I H) (x : Point I H) :
    table (sourceParams c) x none = x := by
  cases x with
  | none => rfl
  | some w =>
    rcases w with ⟨i,a⟩
    have h := (c.1 i).property.1
    simpa [table,sourceParams,localOp,scale,put] using congrArg (fun z => put i (scale a z)) h

lemma eval_source {t : FreeMagma ℕ} (c : SourceCode t I H) (y : Point I H) :
    @FreeMagma.evalInMagma _ _ ⟨table (sourceParams c)⟩ (fun _ => y) t = none := by
  cases y with
  | none => exact eval_root _ _
  | some w =>
    rcases w with ⟨i,a⟩
    change @FreeMagma.evalInMagma _ _ ⟨table (sourceParams c)⟩
      (fun _ => put i (some a)) t = none
    rw [eval_same]
    have h := congrArg (scale a) (c.1 i).property.2
    rw [← eval_shift] at h
    have he : @FreeMagma.evalInMagma _ _ ⟨localOp (c.1 i).val⟩
        (fun _ => some a) t = none := by
      simpa only [scale,Option.map_some,mul_one,Option.map_none] using h
    change put i (@FreeMagma.evalInMagma _ _ ⟨localOp (c.1 i).val⟩ _ t) = none
    rw [he]
    rfl

theorem source_law {t : FreeMagma ℕ} (c : SourceCode t I H) :
    @satisfies _ (Point I H) ⟨table (sourceParams c)⟩ (rightRootLaw t) := by
  letI : Magma (Point I H) := ⟨table (sourceParams c)⟩
  intro v
  change v 0 = table (sourceParams c) (v 0)
    (@FreeMagma.evalInMagma _ _ ⟨table (sourceParams c)⟩ v
      (FreeMagma.fmapHom (fun _ => 1) t))
  rw [FreeMagma.evalInMagma_fmapHom]
  change v 0 = table (sourceParams c) (v 0)
    (@FreeMagma.evalInMagma _ _ ⟨table (sourceParams c)⟩ (fun _ => v 1) t)
  rw [eval_source,table_right_root]

def decode {t : FreeMagma ℕ} (c : SourceCode t I H) :
    RestrictedTables (rightRootLaw t) (Point I H) Invariant :=
  ⟨table (sourceParams c), source_law c, table_invariant _⟩

theorem decode_injective {t : FreeMagma ℕ} : Function.Injective (decode (I := I) (H := H) (t := t)) := by
  intro c d h
  have hh := congrArg (fun f : RestrictedTables (rightRootLaw t) (Point I H) Invariant =>
    parameters f.val) h
  change parameters (table (sourceParams c)) = parameters (table (sourceParams d)) at hh
  rw [parameters_table,parameters_table] at hh
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact congrFun (congrArg Prod.fst hh) i
  · exact congrArg (fun p : Params I H => p.2) hh

def encode [Nontrivial H] {B : NatMagmaLaw}
    (f : RestrictedTables B (Point I H) Invariant) : TargetCode B I H :=
  (fun i => ⟨(parameters f.val).1 i,
    fun x y z => local_law f.property.2 f.property.1 i
      (fun k => if k = 0 then x else if k = 1 then y else z)⟩,
   (parameters f.val).2)

theorem encode_injective [Nontrivial H] {B : NatMagmaLaw} :
    Function.Injective (encode (I := I) (H := H) (B := B)) := by
  intro f g h
  have hp : parameters f.val = parameters g.val := by
    apply Prod.ext
    · funext i
      exact congrArg Subtype.val (congrFun (congrArg Prod.fst h) i)
    · exact congrArg (fun p : TargetCode B I H => p.2) h
  apply Subtype.ext
  rw [← reconstruct f.property.2, ← reconstruct g.property.2, hp]

theorem source_lower [Fintype I] [Fintype H] [DecidableEq H] (t : FreeMagma ℕ) :
    sourceCount (H := H) t ^ Fintype.card I *
      (2 * Fintype.card H + 1) ^ Fintype.card (Cross I) ≤
      Nat.card (RestrictedTables (rightRootLaw t) (Point I H) Invariant) := by
  classical
  have h := Nat.card_le_card_of_injective (decode (I := I) (H := H) (t := t)) decode_injective
  simpa only [Nat.card_eq_fintype_card,SourceCode,Fintype.card_prod,Fintype.card_fun,
    Fintype.card_option,Fintype.card_bool,sourceCount] using h

theorem target_upper [Fintype I] [Fintype H] [DecidableEq H] [Nontrivial H] (B : NatMagmaLaw) :
    Nat.card (RestrictedTables B (Point I H) Invariant) ≤
      targetCount (H := H) B ^ Fintype.card I *
        (2 * Fintype.card H + 1) ^ Fintype.card (Cross I) := by
  classical
  have h := Nat.card_le_card_of_injective (encode (I := I) (H := H) (B := B)) encode_injective
  simpa only [Nat.card_eq_fintype_card,TargetCode,Fintype.card_prod,Fintype.card_fun,
    Fintype.card_option,Fintype.card_bool,targetCount] using h

theorem not_structural [Fintype H] [DecidableEq H] [Nontrivial H]
    {t : FreeMagma ℕ} {B : NatMagmaLaw}
    (hpos : 0 < targetCount (H := H) B)
    (hgap : targetCount (H := H) B < sourceCount (H := H) t) :
    ¬ B.StructuralFrom (rightRootLaw t) := by
  intro h
  obtain ⟨K,hK⟩ := bounded_restricted_counts (rightRootLaw t) B h
  let I := Fin (K * targetCount (H := H) B + 1)
  have hc := hK (Point I H) Invariant (by
    intro M N q hq hp s
    exact Magma.IsEndo.of_definable hq.definable (hp s))
  have hle := (source_lower (I := I) (H := H) t).trans
    (hc.trans (Nat.mul_le_mul_left K (target_upper (I := I) (H := H) B)))
  simp only [I,Fintype.card_fin] at hle
  have hlt := Nat.mul_lt_mul_of_pos_right (PairSwapCounting.numerical_gap K _ _ hpos hgap)
    (show 0 < (2 * Fintype.card H + 1) ^ Fintype.card (Cross I) by positivity)
  exact (not_lt_of_ge hle) (by simpa only [Nat.mul_assoc] using hlt)

end PointedIdentityCounting

/-- info: 'PointedIdentityCounting.not_structural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PointedIdentityCounting.not_structural

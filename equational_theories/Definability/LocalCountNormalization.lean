import equational_theories.Definability.PointedIdentityCounting

/-! Normalize the first non-root variable by the regular group action before
counting local target models. This removes repeated assignments from evaluation. -/
open Law Law.MagmaLaw PointedBlockCounting PointedIdentityCounting
namespace LocalCountNormalization
variable {H : Type} [Group H]

lemma eval_scale (p : LocalParam H) (a : H) (v : ℕ → Option H) (t : FreeMagma ℕ) :
    @FreeMagma.evalInMagma _ _ ⟨localOp p⟩ (fun k => scale a (v k)) t =
      scale a (@FreeMagma.evalInMagma _ _ ⟨localOp p⟩ v t) := by
  induction t with
  | Leaf k => rfl
  | Fork l r hl hr =>
    simp only [FreeMagma.evalInMagma, hl, hr]
    exact (local_shift p a _ _).symm

lemma satisfies_scale (p : LocalParam H) (a : H) (v : ℕ → Option H) (B : NatMagmaLaw)
    (h : @satisfiesPhi _ (Option H) ⟨localOp p⟩ v B) :
    @satisfiesPhi _ (Option H) ⟨localOp p⟩ (fun k => scale a (v k)) B := by
  unfold satisfiesPhi at *
  rw [eval_scale,eval_scale,h]

lemma eval_none (p : LocalParam H) (t : FreeMagma ℕ) :
    @FreeMagma.evalInMagma _ _ ⟨localOp p⟩ (fun _ => none) t = none := by
  induction t with
  | Leaf k => rfl
  | Fork l r hl hr => simp only [FreeMagma.evalInMagma,hl,hr]; rfl

abbrev Test (B : NatMagmaLaw) (p : LocalParam H) (x y z : Option H) :=
  @satisfiesPhi _ (Option H) ⟨localOp p⟩
    (fun k => if k = 0 then x else if k = 1 then y else z) B

def Normalized (B : NatMagmaLaw) (p : LocalParam H) : Prop :=
  (∀ y z, Test B p (some 1) y z) ∧
  (∀ z, Test B p none (some 1) z) ∧ Test B p none none (some 1)

lemma scale_test (B : NatMagmaLaw) (p : LocalParam H) (a : H) (x y z : Option H)
    (h : Test B p x y z) : Test B p (scale a x) (scale a y) (scale a z) := by
  have hh := satisfies_scale p a _ B h
  convert hh using 1
  funext k
  split_ifs <;> rfl

@[simp] lemma scale_inverse (a : H) (x : Option H) : scale a (scale a⁻¹ x) = x := by
  rw [scale_scale]
  cases x <;> simp [scale]

@[simp] lemma scale_one (a : H) : scale a (some 1) = some a := by simp [scale]
@[simp] lemma scale_none (a : H) : scale a none = none := rfl

theorem normalized_iff (B : NatMagmaLaw) (p : LocalParam H) :
    TargetHolds B p ↔ Normalized B p := by
  constructor
  · intro h
    exact ⟨fun y z => h _ y z, fun z => h _ _ z, h _ _ _⟩
  · rintro ⟨hx,hy,hz⟩ x y z
    cases x with
    | some a =>
      simpa using scale_test B p a _ _ _ (hx (scale a⁻¹ y) (scale a⁻¹ z))
    | none =>
      cases y with
      | some a => simpa using scale_test B p a _ _ _ (hy (scale a⁻¹ z))
      | none =>
        cases z with
        | some a => simpa using scale_test B p a _ _ _ hz
        | none =>
          simp only [ite_self, satisfiesPhi, eval_none]

instance [Fintype H] [DecidableEq H] (B : NatMagmaLaw) (p : LocalParam H) :
    Decidable (Normalized B p) := by unfold Normalized Test satisfiesPhi; infer_instance

theorem targetCount_eq [Fintype H] [DecidableEq H] (B : NatMagmaLaw) :
    targetCount (H := H) B = Fintype.card {p : LocalParam H // Normalized B p} := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (normalized_iff B)
end LocalCountNormalization

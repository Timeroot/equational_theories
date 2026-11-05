import equational_theories.Parastrophes.TrialityCore
import equational_theories.Parastrophes.FreeGroupFiniteSeparation
import Mathlib.Tactic.Ring

/-! The free-group obstruction to a defining equation for E1525's left
division also works for finite carriers. Finite permutation representations
preserve any prescribed failure of an identity; taking three rotated copies
preserves the automorphism of order three. -/
namespace Parastrophes.TrialityCore
open Law FreeMagma
noncomputable section

variable {H : Type} [Group H]

def tripleRotation : (H × H × H) →* (H × H × H) where
  toFun x := (x.2.1, x.2.2, x.1)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem tripleRotation_three (x : H × H × H) :
    tripleRotation (tripleRotation (tripleRotation x)) = x := rfl

def tripleMap (f : Carrier →* H) : Carrier →* (H × H × H) where
  toFun x := (f x, f (rotation x), f (rotation (rotation x)))
  map_one' := by simp
  map_mul' x y := by simp

theorem tripleMap_rotate (f : Carrier →* H) (x : Carrier) :
    tripleMap f (rotation x) = tripleRotation (tripleMap f x) := by
  simp [tripleMap, tripleRotation, rotation_three]

theorem tripleMap_division (f : Carrier →* H) (x y : Carrier) :
    tripleMap f ((division rotation).op x y) =
      (division tripleRotation).op (tripleMap f x) (tripleMap f y) := by
  change tripleMap f (x * (rotation (rotation y))⁻¹ * x) = _
  simp only [map_mul, map_inv, tripleMap_rotate]
  rfl

theorem tripleMap_eval {A : Type} (f : Carrier →* H) (t : FreeMagma A) (v : A → Carrier) :
    tripleMap f (@evalInMagma _ _ (division rotation) v t) =
      @evalInMagma _ _ (division tripleRotation) (fun i => tripleMap f (v i)) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change tripleMap f ((division rotation).op _ _) = _
    rw [tripleMap_division, ha, hb]
    rfl

theorem tripleMap_term (f : Carrier →* H) (t : FreeMagma (Fin 2)) (x y : Carrier) :
    tripleMap f ((termMagma (division rotation) t).op x y) =
      (termMagma (division tripleRotation) t).op (tripleMap f x) (tripleMap f y) := by
  change tripleMap f (@evalInMagma _ _ (division rotation) (fun i => if i = 0 then x else y) t) = _
  rw [tripleMap_eval]
  congr 1
  funext i
  split_ifs <;> rfl

theorem tripleMap_source (f : Carrier →* H) (x y : Carrier) :
    tripleMap f ((source rotation).op x y) =
      (source tripleRotation).op (tripleMap f x) (tripleMap f y) := by
  change tripleMap f (rotation (x * y⁻¹ * x)) = _
  simp only [tripleMap_rotate, map_mul, map_inv]
  rfl

/-- No fixed inverse term works even on this restricted family of finite
E1525 division images. Each finite member still has some inverse term,
by iterating its bijective rows; the obstruction is to a uniform choice. -/
theorem no_uniform_finite_inverse :
    ¬ ∃ t : FreeMagma (Fin 2), ∀ (B : Type) (_ : Fintype B),
      (termMagma (division (tripleRotation (H := Equiv.Perm B))) t).op =
        (source (tripleRotation (H := Equiv.Perm B))).op := by
  rintro ⟨t, ht⟩
  apply inverse_not_term t
  funext x y
  by_contra he
  obtain ⟨B, hB, f, hf⟩ := FreeGroupFiniteSeparation.separate _ _ he
  have hm := congrArg (fun op => op (tripleMap f x) (tripleMap f y)) (ht B hB)
  change (termMagma (division tripleRotation) t).op (tripleMap f x) (tripleMap f y) =
    (source tripleRotation).op (tripleMap f x) (tripleMap f y) at hm
  rw [← tripleMap_term f t x y, ← tripleMap_source f x y] at hm
  exact hf (congrArg Prod.fst hm)

/-- An identity of all finite division images holds in the free-group image.
The finite approximating group is a triple of finite permutation groups. -/
theorem free_identity {target : NatMagmaLaw}
    (ht : Characterizes .fin Law1525 .left target) :
    @satisfies _ Carrier (division rotation) target := by
  intro v
  by_contra he
  obtain ⟨B, hB, f, hf⟩ := FreeGroupFiniteSeparation.separate _ _ he
  letI : Fintype B := hB
  let K := Equiv.Perm B × Equiv.Perm B × Equiv.Perm B
  let s : K →* K := tripleRotation
  have hs : ∀ x, s (s (s x)) = x := fun _ => rfl
  have hd := isDivision s hs
  have hsrc := source_law s hs
  have hk : @satisfies _ K (division s) target := by
    apply (ht K (division s) (inferInstance : Finite K)).mpr
    exact ⟨source s, (@Law1525.models_iff _ (source s)).mpr hsrc, hd⟩
  have hm := hk (fun i => tripleMap f (v i))
  change @evalInMagma _ _ (division tripleRotation) (fun i => tripleMap f (v i)) target.lhs =
    @evalInMagma _ _ (division tripleRotation) (fun i => tripleMap f (v i)) target.rhs at hm
  rw [← tripleMap_eval f target.lhs v, ← tripleMap_eval f target.rhs v] at hm
  exact hf (congrArg Prod.fst hm)

@[implicit_reducible] private def weighted : Magma Nat := ⟨fun x y => 2*x+y⟩
@[implicit_reducible] private def joinBool : Magma Bool := ⟨(· || ·)⟩

theorem sub_length (x y : Subcarrier) :
    ((subDivision.op x y).val.toWord).length =
      2 * x.val.toWord.length + y.val.toWord.length := by
  change (((division rotation).op x.val y.val).toWord).length = _
  rw [division_word x.2 y.2]
  simp only [List.length_append, FreeGroup.toWord_inv, FreeGroup.invRev_length,
    rotation, word_map rotate rotate_injective, List.length_map]
  omega

theorem eval_length (t : FreeMagma Nat) (v : Nat → Subcarrier) :
    (@evalInMagma _ _ subDivision v t).val.toWord.length =
      @evalInMagma _ _ weighted (fun i => (v i).val.toWord.length) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change ((subDivision.op _ _).val.toWord).length = _
    rw [sub_length, ha, hb]
    rfl

def generatorPower (n : Nat) (hn : 0 < n) : Subcarrier :=
  ⟨FreeGroup.of 0 ^ n, by
    simp [bounded, FreeGroup.toWord_of_pow, List.head?_replicate,
      List.getLast?_replicate, Nat.ne_zero_of_lt hn]⟩

theorem positive_weighted_identity {target : NatMagmaLaw}
    (ht : Characterizes .fin Law1525 .left target)
    (v : Nat → Nat) (hv : ∀ i, 0 < v i) :
    @evalInMagma _ _ weighted v target.lhs = @evalInMagma _ _ weighted v target.rhs := by
  let w := fun i => generatorPower (v i) (hv i)
  have he := free_identity ht (fun i => (w i).val)
  change @evalInMagma _ _ (division rotation) (fun i => (w i).val) target.lhs =
    @evalInMagma _ _ (division rotation) (fun i => (w i).val) target.rhs at he
  rw [← sub_eval target.lhs w, ← sub_eval target.rhs w] at he
  have hl := congrArg (fun x : Carrier => x.toWord.length) he
  change (@evalInMagma _ _ subDivision w target.lhs).val.toWord.length =
    (@evalInMagma _ _ subDivision w target.rhs).val.toWord.length at hl
  rw [eval_length target.lhs w, eval_length target.rhs w] at hl
  simpa only [w, generatorPower, FreeGroup.toWord_of_pow, List.length_replicate] using hl

private theorem eval_add (t : FreeMagma Nat) (v w : Nat → Nat) :
    @evalInMagma _ _ weighted (fun i => v i + w i) t =
      @evalInMagma _ _ weighted v t + @evalInMagma _ _ weighted w t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change 2 * _ + _ = _
    rw [ha, hb]
    change 2 * (_ + _) + (_ + _) = (2 * _ + _) + (2 * _ + _)
    ring

private theorem weighted_identity {target : NatMagmaLaw}
    (ht : Characterizes .fin Law1525 .left target) : @satisfies _ Nat weighted target := by
  intro v
  have hp := positive_weighted_identity ht (fun i => v i + 1) (fun i => Nat.succ_pos _)
  have ho := positive_weighted_identity ht (fun _ => 1) (fun _ => Nat.zero_lt_one)
  rw [eval_add, eval_add, ho] at hp
  exact Nat.add_right_cancel hp

private def positive (n : Nat) : Bool := decide (n ≠ 0)

private theorem positive_weighted (a b : Nat) :
    positive (2*a+b) = (positive a || positive b) := by
  cases a <;> cases b <;> simp [positive]

private theorem eval_positive (t : FreeMagma Nat) (v : Nat → Bool) :
    positive (@evalInMagma _ _ weighted (fun i => if v i then 1 else 0) t) =
      @evalInMagma _ _ joinBool v t := by
  induction t with
  | Leaf i => cases hv : v i <;> simp [evalInMagma, hv, positive]
  | Fork a b ha hb =>
    change positive (2 * _ + _) = (_ || _)
    rw [positive_weighted, ha, hb]

/-- No single identity characterizes even the finite left-division image of
E1525. Length in reduced words gives `2*x+y`; its identities hold in Boolean
join, whose rows need not be bijective. -/
theorem no_singleEquation_fin : ¬ SingleEquation .fin Law1525 .left := by
  rintro ⟨target, ht⟩
  have hj : @satisfies _ Bool joinBool target := by
    intro v
    have he := congrArg positive (weighted_identity ht (fun i => if v i then 1 else 0))
    simpa only [eval_positive] using he
  have hq := characterizes_sideQuasigroup ht Bool joinBool (inferInstance : Finite Bool) hj
  have he := (hq true).1 (a₁ := false) (a₂ := true) rfl
  contradiction

end
end Parastrophes.TrialityCore

namespace Parastrophes.Catalogue
@[parastrophe_result] theorem left_noSingleEquation1525_fin :
    ¬ SingleEquation .fin Law1525 .left := TrialityCore.no_singleEquation_fin
end Parastrophes.Catalogue

import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import equational_theories.Definability.E125Homogeneous
import equational_theories.Definability.CloneTraps
import equational_theories.ManuallyProved.Equation73

/-!
# Unary term endomorphisms in the homogeneous E73 model

A group word commuting with two distinct free generators is trivial. Applied
to the first two values in the E73 greedy seed, this shows that its only
endomorphism given by a unary term is the identity. No separation of the
E63-family classes is asserted here.
-/

namespace FreeGroup

variable {α : Type*} [DecidableEq α]

-- A nonempty reduced word commuting with a generator starts with that generator.
theorem head_name_of_commute {g : FreeGroup α} {a b : α} {s : Bool}
    {L : List (α × Bool)} (hw : g.toWord = (b,s) :: L)
    (hc : Commute g (of a)) : a = b := by
  by_contra hab
  let W := (b,s) :: L
  let e := (W.getLast (by simp [W])).2
  let letter : α × Bool := (a,e)
  have hW : IsReduced W := by simpa [W, hw] using (isReduced_toWord (x := g))
  have hleft : IsReduced (letter :: W) := by
    rw [IsReduced, List.isChain_cons_cons]
    exact ⟨fun h => False.elim (hab h), hW⟩
  have hright : IsReduced (W ++ [letter]) := by
    rw [IsReduced, List.isChain_append]
    refine ⟨hW, List.IsChain.singleton _, ?_⟩
    intro x hx y hy
    have hx' : x = W.getLast (by simp [W]) := by
      have hl : W.getLast? = some (W.getLast (by simp [W])) := List.getLast?_eq_some_getLast _
      rw [hl] at hx
      exact (Option.some.inj hx).symm
    have hy' : y = letter := by simpa using hy.symm
    subst x y
    intro _
    rfl
  have hcomm : g * mk [letter] = mk [letter] * g := by
    dsimp [letter, e]
    cases he : (W.getLast (by simp [W])).2
    · simpa using hc.inv_right.eq
    · exact hc.eq
  have hh := congrArg toWord hcomm
  rw [toWord_mul, toWord_mul, toWord_mk, IsReduced.singleton.reduce_eq,
      hw, hright.reduce_eq] at hh
  change W ++ [letter] = reduce (letter :: W) at hh
  rw [hleft.reduce_eq] at hh
  exact hab (Prod.mk.inj (List.cons.inj hh.symm).1).1

/-- Distinct free generators have trivial common centralizer. -/
theorem eq_one_of_commute_generators {g : FreeGroup α} {a b : α} (hab : a ≠ b)
    (ha : Commute g (of a)) (hb : Commute g (of b)) : g = 1 := by
  cases hw : g.toWord with
  | nil => exact toWord_eq_nil_iff.mp hw
  | cons c L =>
    have h₁ := head_name_of_commute hw ha
    have h₂ := head_name_of_commute hw hb
    exact (hab (h₁.trans h₂.symm)).elim

end FreeGroup

namespace E63Family.Homogeneous

variable {α : Type*} [DecidableEq α]

/-- The two prescribed seed values already rule out every nonidentity
left group translation that is a magma endomorphism. -/
theorem translation_endomorphism_eq_one
    (f : FreeGroup α → FreeGroup α) {a b : α} (hab : a ≠ b)
    (hf : f 1 = FreeGroup.of a) (hf' : f (FreeGroup.of a) = FreeGroup.of b)
    (c : FreeGroup α)
    (hc : ∀ x y, op f (c * x) (c * y) = c * op f x y) : c = 1 := by
  have hca : Commute c (FreeGroup.of a) := by
    have h := hc 1 1
    simpa [op, hf, Commute] using h.symm
  have hcb : Commute c (FreeGroup.of b) := by
    change c * FreeGroup.of b = FreeGroup.of b * c
    calc
      c * FreeGroup.of b = c * op f 1 (FreeGroup.of a) := by simp [op, hf']
      _ = op f c (c * FreeGroup.of a) := by simpa using (hc 1 (FreeGroup.of a)).symm
      _ = op f c (FreeGroup.of a * c) := by rw [hca.eq]
      _ = op f 1 (FreeGroup.of a) * c := by
        simpa using right_equivariant f 1 (FreeGroup.of a) c
      _ = FreeGroup.of b * c := by simp [op, hf']
  exact FreeGroup.eq_one_of_commute_generators hab hca hcb

/-- Every unary term endomorphism of such a seeded homogeneous magma is
exactly the identity, on the entire carrier. -/
theorem unary_endomorphism_identity
    (f : FreeGroup α → FreeGroup α) {a b : α} (hab : a ≠ b)
    (hf : f 1 = FreeGroup.of a) (hf' : f (FreeGroup.of a) = FreeGroup.of b)
    (t : FreeMagma Unit)
    (ht : ∀ x y,
      @FreeMagma.evalInMagma Unit (FreeGroup α) ⟨op f⟩ (fun _ => op f x y) t =
        op f (@FreeMagma.evalInMagma Unit (FreeGroup α) ⟨op f⟩ (fun _ => x) t)
          (@FreeMagma.evalInMagma Unit (FreeGroup α) ⟨op f⟩ (fun _ => y) t)) :
    ∀ x, @FreeMagma.evalInMagma Unit (FreeGroup α) ⟨op f⟩ (fun _ => x) t = x := by
  let c := @FreeMagma.evalInMagma Unit (FreeGroup α) ⟨op f⟩ (fun _ => 1) t
  have hc : c = 1 := translation_endomorphism_eq_one f hab hf hf' c (by
    intro x y
    have h := ht x y
    rw [unary_term f t (op f x y), unary_term f t x, unary_term f t y] at h
    exact h.symm)
  intro x
  rw [unary_term]
  change c * x = x
  rw [hc, one_mul]

end E63Family.Homogeneous

spectrum_assert FreeGroup.eq_one_of_commute_generators complete
spectrum_assert E63Family.Homogeneous.translation_endomorphism_eq_one complete
spectrum_assert E63Family.Homogeneous.unary_endomorphism_identity complete


namespace E63Family.Homogeneous
open FirstOrder
variable {α : Type} [DecidableEq α]

/-- The unary-endomorphism restriction survives even FO interdefinability. -/
theorem structural_unary_endomorphism_identity
    (f : FreeGroup α → FreeGroup α) {a b : α} (hab : a ≠ b)
    (hf : f 1 = FreeGroup.of a) (hf' : f (FreeGroup.of a) = FreeGroup.of b)
    (N : Magma (FreeGroup α))
    (hforward : @Set.Definable _ ∅ MagmaLanguage (Magma.FOStructure (M := ⟨op f⟩)) _ N.Graph)
    (hback : @Set.Definable _ ∅ MagmaLanguage N.FOStructure _ (Magma.Graph ⟨op f⟩))
    (t : FreeMagma Unit)
    (ht : N.IsEndo (fun x => @FreeMagma.evalInMagma Unit _ N (fun _ => x) t)) :
    ∀ x, @FreeMagma.evalInMagma Unit _ N (fun _ => x) t = x := by
  have hright (x y z : FreeGroup α) : N.op (x*z) (y*z) = N.op x y * z := by
    have h := Magma.IsEndo.of_definable hforward (e := Equiv.mulRight z)
      (fun u v => (right_equivariant f u v z).symm)
    exact (h x y).symm
  have hterm (u : FreeMagma Unit) (x : FreeGroup α) :
      @FreeMagma.evalInMagma Unit _ N (fun _ => x) u =
        @FreeMagma.evalInMagma Unit _ N (fun _ => 1) u * x := by
    induction u with
    | Leaf _ => exact (one_mul x).symm
    | Fork v w hv hw =>
      change N.op _ _ = N.op _ _ * x
      rw [hv, hw, hright]
  let c := @FreeMagma.evalInMagma Unit _ N (fun _ => 1) t
  have hcN : N.IsEndo (Equiv.mulLeft c) := by
    intro x y
    have hh := ht x y
    dsimp only at hh
    rw [hterm t (N.op x y), hterm t x, hterm t y] at hh
    exact hh
  have hcM := Magma.IsEndo.of_definable hback hcN
  have hc : c = 1 := translation_endomorphism_eq_one f hab hf hf' c
    (fun x y => (hcM x y).symm)
  intro x
  rw [hterm]
  change c * x = x
  rw [hc, one_mul]

end E63Family.Homogeneous

namespace Eq73.Greedy

lemma unary_endomorphism_identity (e : Extension) (t : FreeMagma Unit)
    (ht : ∀ x y : GreedyMagma e,
      FreeMagma.evalInMagma (fun _ => x ◇ y) t =
        FreeMagma.evalInMagma (fun _ => x) t ◇ FreeMagma.evalInMagma (fun _ => y) t) :
    ∀ x : GreedyMagma e, FreeMagma.evalInMagma (fun _ => x) t = x := by
  apply E63Family.Homogeneous.unary_endomorphism_identity (f e) (a := 1) (b := 2)
      (by decide) ?_ ?_ t ht
  · exact (f_base e (e.2.base (by decide : FreeGroup.of 1 ∈ E0 1))).symm
  · exact (f_base e (e.2.base (by decide : FreeGroup.of 2 ∈ E0 (FreeGroup.of 1)))).symm

end Eq73.Greedy

spectrum_assert E63Family.Homogeneous.structural_unary_endomorphism_identity complete
spectrum_assert Eq73.Greedy.unary_endomorphism_identity complete

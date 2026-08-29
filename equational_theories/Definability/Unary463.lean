import equational_theories.Definability.UnaryCore

/-!
# Source 463: a set with a map of order four

`Equation463`, `x = y ◇ (x ◇ (x ◇ (x ◇ x)))`, pins its models completely. Writing `s v := v ◇ v`,
the derivation below turns the law into the normal form `u ◇ v = s v` together with `s⁴ = id`, so
**the models of `Equation463` are exactly the sets with a map of order dividing four**.

The language therefore names exactly `x, s x, s² x, s³ x, y, s y, s² y, s³ y`; a `∅`-definable
binary operation is a choice among those eight per equality pattern of the octuple -- sixteen
patterns, `530,841,600` operations, all of them `QFOp` decision trees, so `QFOp.definable_graph`
gives the forward half of `StructuralOnMagma` for free.

The reverse half is done by the three-way split of `Definability/UnarySplit463.lean`.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

namespace Unary463

variable {G : Type} (M : Magma G)

/-! ## The normal form

`Equation463` reads `a ◇ F v = v` for `F v := v ◇ (v ◇ (v ◇ v))`, so the left argument is already
irrelevant on the image of `F`; write `φ z` for the common value of `a ◇ z` there. Then `φ ∘ F` is
the identity, and the work is to show `F` is onto.

That is three steps, each one an `F`-preimage read off the previous. Fix `b` and put `A := F b`,
`B := A ◇ (A ◇ b)`, `C := B ◇ b`. Because `A ◇ A = φ A = b`, `B` is literally `F A`; because
`B ◇ B = φ B = A` and `B ◇ A = φ A = b`, `C` is literally `F B`; and then
`C ◇ C = B`, `C ◇ B = A`, `C ◇ A = b` collapse `F C` to `b`. So `b = F C` is in the image after
all, and `a ◇ b = φ b = C` for every `a`. -/

theorem key (h463 : Equation463 G) (a v : G) :
    M.op a (M.op v (M.op v (M.op v v))) = v := (h463 v a).symm

/-- Every product is `s` of its right argument. -/
theorem sop (h463 : Equation463 G) (a b : G) : M.op a b = M.op b b := by
  set A := M.op b (M.op b (M.op b b)) with hAdef
  have hA : ∀ c : G, M.op c A = b := fun c ↦ key M h463 c b
  set B := M.op A (M.op A b) with hBdef
  have hBF : M.op A (M.op A (M.op A A)) = B := by rw [hA A]
  have hB : ∀ c : G, M.op c B = A := by
    intro c
    have h := key M h463 c A
    rwa [hBF] at h
  set C := M.op B b with hCdef
  have hCF : M.op B (M.op B (M.op B B)) = C := by rw [hB B, hA B]
  have hC : ∀ c : G, M.op c C = B := by
    intro c
    have h := key M h463 c B
    rwa [hCF] at h
  have hCC : M.op C (M.op C (M.op C C)) = b := by rw [hC C, hB C, hA C]
  have h1 : ∀ c : G, M.op c b = C := by
    intro c
    have h := key M h463 c C
    rwa [hCC] at h
  rw [h1 a, h1 b]

/-- `s` has order dividing four. -/
theorem sfour (h463 : Equation463 G) (v : G) :
    M.op (M.op (M.op (M.op v v) (M.op v v)) (M.op (M.op v v) (M.op v v)))
        (M.op (M.op (M.op v v) (M.op v v)) (M.op (M.op v v) (M.op v v))) = v := by
  have hs := sop M h463
  have h := key M h463 v v
  rw [hs v (M.op v v), hs v (M.op (M.op v v) (M.op v v)),
    hs v (M.op (M.op (M.op v v) (M.op v v)) (M.op (M.op v v) (M.op v v)))] at h
  exact h

/-! ## Naming the map

Every generated proof opens by naming `s`, which turns the two normal-form lemmas into the pair
`(∀ u v, u ◇ v = s v, ∀ v, s (s (s (s v))) = v)` that `grind` wants. `s` is `obtain`ed rather than
`set`, because `s v = v ◇ v` used as a rewrite rule sends the simp set into
`a → a ◇ a → (a ◇ a) ◇ (a ◇ a) → ⋯`. -/

theorem name_s (h463 : Equation463 G) :
    ∃ s : G → G, (∀ u v : G, M.op u v = s v) ∧ (∀ v : G, s (s (s (s v))) = v) :=
  ⟨fun v ↦ M.op v v, sop M h463, sfour M h463⟩

end Unary463

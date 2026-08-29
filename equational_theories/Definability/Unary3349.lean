import equational_theories.Definability.UnaryCore

/-!
# Source 3349: a set with a map whose cube is itself

`Equation3349`, `x ◇ y = y ◇ (x ◇ (z ◇ y))`, pins its models completely. Writing `s v := v ◇ v`,
the derivation below turns the law into the normal form `u ◇ v = s v` together with `s³ = s`, so
**the models of `Equation3349` are exactly the sets with a map whose cube is itself** -- a map that
is an involution on its image, with an arbitrary collapse onto it.

The language therefore names exactly `x, s x, s² x, y, s y, s² y`; a `∅`-definable binary operation
is a choice among those six per equality pattern of the sextuple -- thirty patterns, and
`QFOp.definable_graph` gives the forward half of `StructuralOnMagma` for free.

Unlike the `s^k = id` sources the patterns can also *test* how far into the image a point is,
`s² x = x` being the "on the image" test, so the trees available here are strictly richer than at
source 62, which is the same `k` with `s³ = id`.

The reverse half is done by the three-way split of `Definability/UnarySplit3349.lean`.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

namespace Unary3349

variable {G : Type} (M : Magma G)

/-! ## The normal form

The law says `x ◇ y = y ◇ (x ◇ (z ◇ y))`, so the right-hand side is independent of `z` -- and the
whole point is to make it independent of `x` as well.

Two instances of the law compose into `key9`, `v ◇ (u ◇ v) = (u ◇ v) ◇ (w ◇ v)`, whose right-hand
side is free in `u`, and `key8`, which is the same trick one level down. Together they give
`key30`: `a ◇ (b ◇ (b ◇ c))` does not depend on `a`. Since the law at `x = y = z = v` says
`v ◇ v = v ◇ (v ◇ (v ◇ v))` -- which *is* of that shape -- `x ◇ (v ◇ v)` does not depend on `x`
either, and comparing it with `x := v` is the normal form. -/

/-- Two instances of the law, composed: the right-hand side no longer mentions `u`. -/
theorem key9 (h : Equation3349 G) (u v w : G) :
    M.op v (M.op u v) = M.op (M.op u v) (M.op w v) := by
  have e := h v (M.op u v) w
  rw [← h w v u] at e
  exact e

/-- The same composition one level down. -/
theorem key8 (h : Equation3349 G) (a b d e : G) :
    M.op a (M.op b (M.op d e)) = M.op (M.op b (M.op d e)) (M.op a (M.op b e)) := by
  have e1 := h a (M.op b (M.op d e)) e
  rw [← h b e d] at e1
  exact e1

/-- `a ◇ (b ◇ (b ◇ c))` does not depend on `a`. -/
theorem key30 (h : Equation3349 G) (a b c : G) :
    M.op a (M.op b (M.op b c)) = M.op (M.op b c) (M.op b (M.op b c)) :=
  (key8 M h a b b c).trans (key9 M h b (M.op b c) a).symm

/-- The law at `x = y = z = v`: `s v` is already of the shape `key30` accepts. -/
theorem key0 (h : Equation3349 G) (v : G) :
    M.op v v = M.op v (M.op v (M.op v v)) := h v v v

/-- Every product with a square on the right is that square's square. -/
theorem key204 (h : Equation3349 G) (x y : G) : M.op x (M.op y y) = M.op y (M.op y y) := by
  have e : M.op x (M.op y (M.op y (M.op y y))) = M.op y (M.op y (M.op y (M.op y y))) :=
    (key30 M h x y (M.op y y)).trans (key30 M h y y (M.op y y)).symm
  rwa [← key0 M h y] at e

/-- Every product is `s` of its right argument. -/
theorem sop (h : Equation3349 G) (a b : G) : M.op a b = M.op b b := by
  have e := h a b b
  rw [key204 M h a b, ← key0 M h b] at e
  exact e

/-- `s` cubed is `s`. -/
theorem scube (h : Equation3349 G) (v : G) :
    M.op (M.op (M.op v v) (M.op v v)) (M.op (M.op v v) (M.op v v)) = M.op v v := by
  have hs := sop M h
  have e := h v v v
  rw [hs v (M.op v v), hs v (M.op (M.op v v) (M.op v v))] at e
  exact e.symm

/-! ## Naming the map

Every generated proof opens by naming `s`, which turns the two normal-form lemmas into the pair
`(∀ u v, u ◇ v = s v, ∀ v, s (s (s v)) = s v)` that `grind` wants. `s` is `obtain`ed rather than
`set`, because `s v = v ◇ v` used as a rewrite rule sends the simp set into
`a → a ◇ a → (a ◇ a) ◇ (a ◇ a) → ⋯`. -/

theorem name_s (h : Equation3349 G) :
    ∃ s : G → G, (∀ u v : G, M.op u v = s v) ∧ (∀ v : G, s (s (s v)) = s v) :=
  ⟨fun v ↦ M.op v v, sop M h, scube M h⟩

end Unary3349

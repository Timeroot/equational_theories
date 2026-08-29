import equational_theories.Definability.UnaryCore

/-!
# Source 62: a set with a map of order three

`Equation62`, `x = y ◇ (x ◇ (x ◇ x))`, pins its models completely. Writing `s v := v ◇ v`, the
derivation below turns the law into the normal form `u ◇ v = s v` together with `s³ = id`, so **the
models of `Equation62` are exactly the sets with a map of order dividing three**.

The language therefore names exactly `x, s x, s² x, y, s y, s² y`; a `∅`-definable binary operation
is a choice among those six per equality pattern of the sextuple -- eight patterns, `5184`
operations, all of them `QFOp` decision trees, so `QFOp.definable_graph` gives the forward half of
`StructuralOnMagma` for free.

Of those, `3696` also define `s` back, and `2688` do so by the cheapest shape there is: their own
diagonal names it, `y □ y = s y`, which makes the reverse half the quantifier-free
`Unary.definable_graph_diag`. Eleven of them settle 105 of source 62's 152 open targets, the
first four covering 89 of the 105:

    x □ y := if y = x then s x else x                                              (`t216`)
    x □ y := if y = x then s x else if y = s x then x else if y = s² x then s² x else y
                                                                                   (`t3525`)
    x □ y := if y = x then s x else if y = s² x then s² x else x                   (`t264`)
    x □ y := if y = x then s x else s² x                                           (`t422`)
    x □ y := if y = s x then x else s x                                            (`t247`)
    x □ y := if y = s² x then s² x else s x                                        (`t343`)
    x □ y := if y = s² x then x else s x                                           (`t295`)
    x □ y := if y = x then s x else if y = s x then x else s² x                    (`t278`)
    x □ y := if y = s² x then x else if y = x ∨ y = s x then s x else y            (`t3549`)
    x □ y := if y = s² x then s² y else s y                                        (`t4294`)
    x □ y := if y = x then s² x else if y = s x then s x else s y                  (`t4414`)

The last has `x □ x = s² x` rather than `s x`, so it goes through `Unary.definable_graph_diag2`.

The generated proofs live in `Unary62_*.lean`.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

namespace Unary62

variable {G : Type} (M : Magma G)

/-! ## The normal form

`Equation62` reads `u ◇ (v ◇ (v ◇ v)) = v`, i.e. `u ◇ s² v = v` for `s² v := v ◇ (v ◇ v)`. That
already makes `s²` a two-sided partner of itself in a weak sense; the work is to show that the
product does not depend on its left argument at all. -/

theorem key (h62 : Equation62 G) (a v : G) : M.op a (M.op v (M.op v v)) = v := (h62 v a).symm

/-- `v ◇ (v ◇ v)` is a two-sided partner of itself. -/
theorem hB (h62 : Equation62 G) (v : G) :
    M.op (M.op v (M.op v v)) (M.op v (M.op v v)) = v :=
  key M h62 _ v

theorem l2 (h62 : Equation62 G) (a v : G) :
    M.op a (M.op (M.op v (M.op v v)) v) = M.op v (M.op v v) := by
  have h := key M h62 a (M.op v (M.op v v))
  rw [hB M h62 v] at h
  exact h

theorem l3 (h62 : Equation62 G) (a b : G) :
    M.op a b = M.op (M.op b (M.op b b)) b := by
  set w := M.op (M.op b (M.op b b)) b with hw
  have e1 : M.op w (M.op b (M.op b b)) = b := key M h62 w b
  have e2 : M.op w w = M.op b (M.op b b) := by rw [hw]; exact l2 M h62 w b
  have e3 : M.op a (M.op w (M.op w w)) = w := key M h62 a w
  rw [e2, e1] at e3
  exact e3

/-- Every product is `s` of its right argument. -/
theorem sop (h62 : Equation62 G) (a b : G) : M.op a b = M.op b b :=
  (l3 M h62 a b).trans (l3 M h62 b b).symm

/-- `s` has order dividing three. -/
theorem scube (h62 : Equation62 G) (v : G) :
    M.op (M.op (M.op v v) (M.op v v)) (M.op (M.op v v) (M.op v v)) = v := by
  have h := hB M h62 v
  rw [sop M h62 v (M.op v v)] at h
  exact h

/-! ## Naming the map

Every generated proof opens by naming `s`, which turns the two normal-form lemmas into the pair
`(∀ u v, u ◇ v = s v, ∀ v, s (s (s v)) = v)` that `grind` wants. `s` is `obtain`ed rather than
`set`, because `s v = v ◇ v` used as a rewrite rule sends the simp set into
`a → a ◇ a → (a ◇ a) ◇ (a ◇ a) → ⋯`. -/

theorem name_s (h62 : Equation62 G) :
    ∃ s : G → G, (∀ u v : G, M.op u v = s v) ∧ (∀ v : G, s (s (s v)) = v) :=
  ⟨fun v ↦ M.op v v, sop M h62, scube M h62⟩

/-! ## The operations

Each tree tests its right argument against `x`, `s x`, `s² x` and returns one of the six named
values `x, s x, s² x, y, s y, s² y`. All but the last have `x □ x = s x`, which is what
`Unary.definable_graph_diag` asks for; `t4414` has `x □ x = s² x` and goes through
`Unary.definable_graph_diag2` instead. -/

/-- `x □ y := if y = x then s x else x`. -/
def t216 : QFOp := .ite (Lf 1) (Lf 0) (.leaf (Lf 0 ⋆ Lf 0)) (.leaf (Lf 0))

/-- `x □ y := if y = x then s x else s² x`. -/
def t422 : QFOp :=
  .ite (Lf 1) (Lf 0) (.leaf (Lf 0 ⋆ Lf 0)) (.leaf ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)))

/-- `x □ y := if y = x then s x else if y = s² x then s² x else x`. -/
def t264 : QFOp :=
  .ite (Lf 1) (Lf 0) (.leaf (Lf 0 ⋆ Lf 0))
    (.ite (Lf 1) ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0))
      (.leaf ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0))) (.leaf (Lf 0)))

/-- `x □ y := if y = x then s x else if y = s x then x else if y = s² x then s² x else y`. -/
def t3525 : QFOp :=
  .ite (Lf 1) (Lf 0) (.leaf (Lf 0 ⋆ Lf 0))
    (.ite (Lf 1) (Lf 0 ⋆ Lf 0) (.leaf (Lf 0))
      (.ite (Lf 1) ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0))
        (.leaf ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0))) (.leaf (Lf 1))))

/-- `x □ y := if y = s x then x else s x`. -/
def t247 : QFOp := .ite (Lf 1) (Lf 0 ⋆ Lf 0) (.leaf (Lf 0)) (.leaf (Lf 0 ⋆ Lf 0))

/-- `x □ y := if y = s² x then s² x else s x`. -/
def t343 : QFOp :=
  .ite (Lf 1) ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) (.leaf ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)))
    (.leaf (Lf 0 ⋆ Lf 0))

/-- `x □ y := if y = s² x then x else s x`. -/
def t295 : QFOp :=
  .ite (Lf 1) ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) (.leaf (Lf 0)) (.leaf (Lf 0 ⋆ Lf 0))

/-- `x □ y := if y = x then s x else if y = s x then x else s² x`. -/
def t278 : QFOp :=
  .ite (Lf 1) (Lf 0) (.leaf (Lf 0 ⋆ Lf 0))
    (.ite (Lf 1) (Lf 0 ⋆ Lf 0) (.leaf (Lf 0)) (.leaf ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0))))

/-- `x □ y := if y = s² x then x else if y = x then s x else if y = s x then s x else y`. -/
def t3549 : QFOp :=
  .ite (Lf 1) ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) (.leaf (Lf 0))
    (.ite (Lf 1) (Lf 0) (.leaf (Lf 0 ⋆ Lf 0))
      (.ite (Lf 1) (Lf 0 ⋆ Lf 0) (.leaf (Lf 0 ⋆ Lf 0)) (.leaf (Lf 1))))

/-- `x □ y := if y = s² x then s² y else s y`. -/
def t4294 : QFOp :=
  .ite (Lf 1) ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) (.leaf ((Lf 1 ⋆ Lf 1) ⋆ (Lf 1 ⋆ Lf 1)))
    (.leaf (Lf 1 ⋆ Lf 1))

/-- `x □ y := if y = x then s² x else if y = s x then s x else s y`. The odd one out: its diagonal
is `s²`, not `s`. -/
def t4414 : QFOp :=
  .ite (Lf 1) (Lf 0) (.leaf ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)))
    (.ite (Lf 1) (Lf 0 ⋆ Lf 0) (.leaf (Lf 0 ⋆ Lf 0)) (.leaf (Lf 1 ⋆ Lf 1)))

open scoped Classical in
theorem t216_apply (a b : G) :
    (t216.magma M).op a b = if b = a then M.op a a else a := by
  show @QFOp.eval _ M t216 ![a, b] = _
  simp only [t216, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t422_apply (a b : G) :
    (t422.magma M).op a b =
      if b = a then M.op a a else M.op (M.op a a) (M.op a a) := by
  show @QFOp.eval _ M t422 ![a, b] = _
  simp only [t422, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t264_apply (a b : G) :
    (t264.magma M).op a b =
      if b = a then M.op a a
      else if b = M.op (M.op a a) (M.op a a) then M.op (M.op a a) (M.op a a) else a := by
  show @QFOp.eval _ M t264 ![a, b] = _
  simp only [t264, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t3525_apply (a b : G) :
    (t3525.magma M).op a b =
      if b = a then M.op a a
      else if b = M.op a a then a
      else if b = M.op (M.op a a) (M.op a a) then M.op (M.op a a) (M.op a a) else b := by
  show @QFOp.eval _ M t3525 ![a, b] = _
  simp only [t3525, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t247_apply (a b : G) :
    (t247.magma M).op a b = if b = M.op a a then a else M.op a a := by
  show @QFOp.eval _ M t247 ![a, b] = _
  simp only [t247, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t343_apply (a b : G) :
    (t343.magma M).op a b =
      if b = M.op (M.op a a) (M.op a a) then M.op (M.op a a) (M.op a a) else M.op a a := by
  show @QFOp.eval _ M t343 ![a, b] = _
  simp only [t343, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t295_apply (a b : G) :
    (t295.magma M).op a b = if b = M.op (M.op a a) (M.op a a) then a else M.op a a := by
  show @QFOp.eval _ M t295 ![a, b] = _
  simp only [t295, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t278_apply (a b : G) :
    (t278.magma M).op a b =
      if b = a then M.op a a
      else if b = M.op a a then a else M.op (M.op a a) (M.op a a) := by
  show @QFOp.eval _ M t278 ![a, b] = _
  simp only [t278, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t3549_apply (a b : G) :
    (t3549.magma M).op a b =
      if b = M.op (M.op a a) (M.op a a) then a
      else if b = a then M.op a a
      else if b = M.op a a then M.op a a else b := by
  show @QFOp.eval _ M t3549 ![a, b] = _
  simp only [t3549, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t4294_apply (a b : G) :
    (t4294.magma M).op a b =
      if b = M.op (M.op a a) (M.op a a) then M.op (M.op b b) (M.op b b) else M.op b b := by
  show @QFOp.eval _ M t4294 ![a, b] = _
  simp only [t4294, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t4414_apply (a b : G) :
    (t4414.magma M).op a b =
      if b = a then M.op (M.op a a) (M.op a a)
      else if b = M.op a a then M.op a a else M.op b b := by
  show @QFOp.eval _ M t4414 ![a, b] = _
  simp only [t4414, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## The diagonals name the map

`x □ x = s x` for the first ten trees. The tests that fire on the diagonal are `y = s y` and
`y = s² y`, and under `s³ = id` each of them forces `s y = y`, so the branch value agrees. -/

theorem t216_diag (_h62 : Equation62 G) (y : G) : (t216.magma M).op y y = M.op y y := by
  classical simp [t216_apply M y y]

theorem t422_diag (_h62 : Equation62 G) (y : G) : (t422.magma M).op y y = M.op y y := by
  classical simp [t422_apply M y y]

theorem t264_diag (_h62 : Equation62 G) (y : G) : (t264.magma M).op y y = M.op y y := by
  classical simp [t264_apply M y y]

theorem t3525_diag (_h62 : Equation62 G) (y : G) : (t3525.magma M).op y y = M.op y y := by
  classical simp [t3525_apply M y y]

theorem t247_diag (h62 : Equation62 G) (y : G) : (t247.magma M).op y y = M.op y y := by
  classical
  obtain ⟨s, hs, hss⟩ := name_s M h62
  simp only [t247_apply M, hs]
  grind

theorem t343_diag (h62 : Equation62 G) (y : G) : (t343.magma M).op y y = M.op y y := by
  classical
  obtain ⟨s, hs, hss⟩ := name_s M h62
  simp only [t343_apply M, hs]
  grind

theorem t295_diag (h62 : Equation62 G) (y : G) : (t295.magma M).op y y = M.op y y := by
  classical
  obtain ⟨s, hs, hss⟩ := name_s M h62
  simp only [t295_apply M, hs]
  grind

theorem t278_diag (_h62 : Equation62 G) (y : G) : (t278.magma M).op y y = M.op y y := by
  classical simp [t278_apply M y y]

theorem t3549_diag (h62 : Equation62 G) (y : G) : (t3549.magma M).op y y = M.op y y := by
  classical
  obtain ⟨s, hs, hss⟩ := name_s M h62
  simp only [t3549_apply M, hs]
  grind

theorem t4294_diag (h62 : Equation62 G) (y : G) : (t4294.magma M).op y y = M.op y y := by
  classical
  obtain ⟨s, hs, hss⟩ := name_s M h62
  simp only [t4294_apply M, hs]
  grind

/-- `t4414`'s diagonal is `s²`, so `s` is the diagonal of the diagonal. -/
theorem t4414_diag2 (h62 : Equation62 G) (y : G) :
    (t4414.magma M).op ((t4414.magma M).op y y) ((t4414.magma M).op y y) = M.op y y := by
  classical
  obtain ⟨s, hs, hss⟩ := name_s M h62
  simp only [t4414_apply M, hs]
  grind

end Unary62

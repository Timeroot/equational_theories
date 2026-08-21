import equational_theories.Definability.CaseSplit

/-!
# The commutative patch

`Definability/CaseSplit.lean` overwrites the diagonal of the source operation,

    x □ y := if x = y then x else x ◇ y,

and gets idempotence for free. Nothing in that construction cares that the off-diagonal value is
`x ◇ y`: any word `w` in the two arguments will do, and the patched operation is *commutative* as
soon as `w` is symmetric.

That pairs with a small piece of arithmetic on the target side. Of the targets the definability
board still has open, exactly six -- `Equation43`, `Equation332`, `Equation3342`, `Equation3545`,
`Equation4343` and `Equation4405` -- are consequences of commutativity together with idempotence;
the middle four are commutativity dressed in squares, `x ◇ y = y ◇ (x ◇ x)` and its relatives.
So a whole rectangle of the board collapses to one question about the *source* alone, with no
reference to the target at all:

> does the source law prove `w(x, y) = w(y, x)` for some word `w`?

Eight of the open sources do, and the words are short: `x ◇ y` for `Equation43` and
`Equation3364`, the source law itself for `Equation4293`, `Equation4321` and `Equation4343`, and
`x ◇ (x ◇ (x ◇ y))` for `Equation546` and `Equation3607`.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw

variable {G : Type}

namespace QFOp

open FreeMagma

/-- `x □ y := if x = y then x else w(x, y)`, the word `w` with its diagonal overwritten. -/
def patch (w : FreeMagma (Fin 2)) : QFOp :=
  .ite (Lf 0) (Lf 1) (.leaf (Lf 0)) (.leaf w)

open scoped Classical in
theorem patch_apply (M : Magma G) (w : FreeMagma (Fin 2)) (a b : G) :
    ((patch w).magma M).op a b = if a = b then a else @evalInMagma _ _ M ![a, b] w := by
  show @eval _ M (patch w) ![a, b] = _
  simp only [patch, eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem patch_diag (M : Magma G) (w : FreeMagma (Fin 2)) (a : G) :
    ((patch w).magma M).op a a = a := by
  classical
  rw [patch_apply]
  simp

/-- Off the diagonal the patched operation is `w`, and on the diagonal it is symmetric already. -/
theorem patch_comm (M : Magma G) (w : FreeMagma (Fin 2))
    (hw : ∀ a b : G, @evalInMagma _ _ M ![a, b] w = @evalInMagma _ _ M ![b, a] w) (a b : G) :
    ((patch w).magma M).op a b = ((patch w).magma M).op b a := by
  classical
  rcases eq_or_ne a b with rfl | hab
  · rfl
  · rw [patch_apply, patch_apply, if_neg hab, if_neg hab.symm, hw]

end QFOp

namespace Law.MagmaLaw

open QFOp FreeMagma

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- Glue: a target that follows from commutativity and idempotence is definable from any source
that proves some word symmetric. -/
theorem definableFrom_of_symmTerm (w : FreeMagma (Fin 2))
    (hw : ∀ {G : Type} (M : Magma G), satisfies G L' →
      ∀ a b : G, @evalInMagma _ _ M ![a, b] w = @evalInMagma _ _ M ![b, a] w)
    (hL : ∀ {G : Type} (N : Magma G), (∀ a : G, N.op a a = a) →
      (∀ a b : G, N.op a b = N.op b a) → @satisfies _ G N L) :
    L.DefinableFrom L' :=
  definableFrom_of_qfOp (patch w) fun M hM ↦
    hL ((patch w).magma M) (patch_diag M w) (patch_comm M w (hw M hM))

/-! ## The targets

Four targets, all of them commutativity with a square or two thrown in. -/

theorem commIdem_332 {G : Type} (N : Magma G) (hi : ∀ a : G, N.op a a = a)
    (hc : ∀ a b : G, N.op a b = N.op b a) : @satisfies _ G N Law332 := by
  rw [@Law332.models_iff G N]
  intro x y
  simp only [hi]
  exact hc x y

theorem commIdem_3342 {G : Type} (N : Magma G) (hi : ∀ a : G, N.op a a = a)
    (hc : ∀ a b : G, N.op a b = N.op b a) : @satisfies _ G N Law3342 := by
  rw [@Law3342.models_iff G N]
  intro x y
  simp only [hi]
  exact hc x y

theorem commIdem_3545 {G : Type} (N : Magma G) (hi : ∀ a : G, N.op a a = a)
    (hc : ∀ a b : G, N.op a b = N.op b a) : @satisfies _ G N Law3545 := by
  rw [@Law3545.models_iff G N]
  intro x y
  simp only [hi]
  exact hc x y

theorem commIdem_4343 {G : Type} (N : Magma G) (hi : ∀ a : G, N.op a a = a)
    (hc : ∀ a b : G, N.op a b = N.op b a) : @satisfies _ G N Law4343 := by
  rw [@Law4343.models_iff G N]
  intro x y
  simp only [hi]
  exact hc x y

/-! ## The words -/

/-- `w(x, y) = x ◇ y`. -/
def symmW1 : FreeMagma (Fin 2) := Lf 0 ⋆ Lf 1

/-- `w(x, y) = x ◇ (x ◇ y)`. -/
def symmW2 : FreeMagma (Fin 2) := Lf 0 ⋆ (Lf 0 ⋆ Lf 1)

/-- `w(x, y) = x ◇ (y ◇ x)`. -/
def symmW3 : FreeMagma (Fin 2) := Lf 0 ⋆ (Lf 1 ⋆ Lf 0)

/-- `w(x, y) = x ◇ (y ◇ y)`. -/
def symmW4 : FreeMagma (Fin 2) := Lf 0 ⋆ (Lf 1 ⋆ Lf 1)

/-- `w(x, y) = x ◇ (x ◇ (x ◇ y))`. -/
def symmW5 : FreeMagma (Fin 2) := Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1))

/-- `w(x, y) = x ◇ (x ◇ (y ◇ y))`. -/
def symmW6 : FreeMagma (Fin 2) := Lf 0 ⋆ (Lf 0 ⋆ (Lf 1 ⋆ Lf 1))

private theorem eval_symmW1 (M : Magma G) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW1 = M.op a b := by
  simp only [symmW1, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem eval_symmW2 (M : Magma G) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW2 = M.op a (M.op a b) := by
  simp only [symmW2, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem eval_symmW3 (M : Magma G) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW3 = M.op a (M.op b a) := by
  simp only [symmW3, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem eval_symmW4 (M : Magma G) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW4 = M.op a (M.op b b) := by
  simp only [symmW4, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem eval_symmW5 (M : Magma G) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW5 = M.op a (M.op a (M.op a b)) := by
  simp only [symmW5, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem eval_symmW6 (M : Magma G) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW6 = M.op a (M.op a (M.op b b)) := by
  simp only [symmW6, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## The sources

For `Equation4293`, `Equation4321` and `Equation4343` the symmetry of the word *is* the source
law. The other four need a derivation. -/

/-- `Equation3364`, `x ◇ y = y ◇ (z ◇ (x ◇ z))`, proves commutativity outright.

The one lemma that does the work is `a ◇ (b ◇ (b ◇ c)) = c ◇ a`, which says that the right-hand
side of the law is independent of `z`; everything else is bookkeeping around the square `x ◇ x`. -/
private theorem symm3364 {G : Type} (M : Magma G)
    (h : ∀ x y z : G, M.op x y = M.op y (M.op z (M.op x z))) (x y : G) :
    M.op x y = M.op y x := by
  have L2 : ∀ a b c : G, M.op a (M.op b (M.op b c)) = M.op c a := by
    intro a b c
    rw [h b (M.op b c) c]
    exact (h c a (M.op b c)).symm
  have hs : M.op x (M.op x (M.op x x)) = M.op x x := L2 x x x
  have hxs : M.op x (M.op x x) = M.op (M.op x x) x := by
    have e := L2 x x (M.op x x)
    rwa [hs] at e
  have h78 : ∀ a : G, M.op a (M.op x (M.op x x)) = M.op (M.op x (M.op x x)) a := by
    intro a
    have e := L2 a x (M.op x (M.op x x))
    rwa [hs] at e
  calc M.op x y
      = M.op y (M.op x (M.op x x)) := h x y x
    _ = M.op y (M.op (M.op x x) x) := by rw [hxs]
    _ = M.op (M.op (M.op x x) x) (M.op x (M.op y x)) := h y (M.op (M.op x x) x) x
    _ = M.op (M.op x (M.op x x)) (M.op x (M.op y x)) := by rw [← hxs]
    _ = M.op (M.op x (M.op y x)) (M.op x (M.op x x)) := (h78 _).symm
    _ = M.op x (M.op x (M.op y x)) := (h x (M.op x (M.op y x)) x).symm
    _ = M.op y x := (h y x x).symm

/-- `Equation546`, `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`, makes `x ◇ (x ◇ (x ◇ y))` symmetric.

Two facts come out of the law immediately: `(a ◇ b) ◇ b = a`, so every right translation is an
involution, and `a ◇ (b ◇ c) = c ◇ (b ◇ a)`. Together they make the fourth power of every left
translation the identity, and then `x ◇ (x ◇ (x ◇ y))` is just `L x⁻¹ y`, which is symmetric
because `L x` and `L y` are inverse to each other on the relevant pair. -/
private theorem symm546 {G : Type} (M : Magma G)
    (h : ∀ x y z : G, x = M.op y (M.op z (M.op x (M.op z y)))) (x y : G) :
    M.op x (M.op x (M.op x y)) = M.op y (M.op y (M.op y x)) := by
  have L2 : ∀ a b : G, M.op (M.op a b) b = a := by
    intro a b
    have e := h a (M.op a b) b
    rw [← h b b a] at e
    exact e.symm
  have P : ∀ a b c : G, M.op a (M.op b c) = M.op c (M.op b a) := by
    intro a b c
    have e := h (M.op a (M.op b c)) c b
    rw [L2 a (M.op b c)] at e
    exact e
  have hB : ∀ a b : G, M.op a (M.op a (M.op a (M.op a b))) = b := by
    intro a b
    rw [P a a (M.op a (M.op a b)), P a a b]
    exact L2 b (M.op a a)
  have h1 : M.op y (M.op y (M.op y (M.op y x))) = x := hB y x
  have h2 : M.op x (M.op y (M.op y (M.op y x))) = y := by
    have e := L2 y (M.op y (M.op y (M.op y x)))
    rwa [h1] at e
  calc M.op x (M.op x (M.op x y))
      = M.op x (M.op x (M.op x (M.op x (M.op y (M.op y (M.op y x)))))) := by rw [h2]
    _ = M.op y (M.op y (M.op y x)) := hB x _

/-- `Equation3607`, `x ◇ y = z ◇ ((y ◇ z) ◇ x)`, makes `x ◇ (x ◇ (x ◇ y))` symmetric: three
applications of the law, with no auxiliary lemma at all. -/
private theorem symm3607 {G : Type} (M : Magma G)
    (h : ∀ x y z : G, M.op x y = M.op z (M.op (M.op y z) x)) (x y : G) :
    M.op x (M.op x (M.op x y)) = M.op y (M.op y (M.op y x)) := by
  calc M.op x (M.op x (M.op x y))
      = M.op y (M.op (M.op (M.op x (M.op x y)) y) x) := h x (M.op x (M.op x y)) y
    _ = M.op y (M.op y (M.op (M.op x y) (M.op (M.op x (M.op x y)) y))) := by
        rw [h (M.op (M.op x (M.op x y)) y) x y]
    _ = M.op y (M.op y (M.op y x)) := by rw [← h y x (M.op x y)]

/-- `Equation4541`, `x ◇ (y ◇ z) = (z ◇ x) ◇ y`, makes `x ◇ (x ◇ (y ◇ y))` symmetric. -/
private theorem symm4541 {G : Type} (M : Magma G)
    (h : ∀ x y z : G, M.op x (M.op y z) = M.op (M.op z x) y) (x y : G) :
    M.op x (M.op x (M.op y y)) = M.op y (M.op y (M.op x x)) := by
  calc M.op x (M.op x (M.op y y))
      = M.op x (M.op (M.op y x) y) := by rw [h x y y]
    _ = M.op (M.op y x) (M.op y x) := h x (M.op y x) y
    _ = M.op (M.op x (M.op y x)) y := h (M.op y x) y x
    _ = M.op (M.op (M.op x x) y) y := by rw [h x y x]
    _ = M.op y (M.op y (M.op x x)) := (h y y (M.op x x)).symm

/-! ## The eight symmetric words, packaged for `definableFrom_of_symmTerm` -/

private theorem hw43 {G : Type} (M : Magma G) (hM : satisfies G Law43) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW1 = @evalInMagma _ _ M ![b, a] symmW1 := by
  rw [eval_symmW1, eval_symmW1]
  exact (@Law43.models_iff G M).mp hM a b

private theorem hw546 {G : Type} (M : Magma G) (hM : satisfies G Law546) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW5 = @evalInMagma _ _ M ![b, a] symmW5 := by
  rw [eval_symmW5, eval_symmW5]
  exact symm546 M ((@Law546.models_iff G M).mp hM) a b

private theorem hw3364 {G : Type} (M : Magma G) (hM : satisfies G Law3364) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW1 = @evalInMagma _ _ M ![b, a] symmW1 := by
  rw [eval_symmW1, eval_symmW1]
  exact symm3364 M ((@Law3364.models_iff G M).mp hM) a b

private theorem hw3607 {G : Type} (M : Magma G) (hM : satisfies G Law3607) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW5 = @evalInMagma _ _ M ![b, a] symmW5 := by
  rw [eval_symmW5, eval_symmW5]
  exact symm3607 M ((@Law3607.models_iff G M).mp hM) a b

private theorem hw4293 {G : Type} (M : Magma G) (hM : satisfies G Law4293) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW2 = @evalInMagma _ _ M ![b, a] symmW2 := by
  rw [eval_symmW2, eval_symmW2]
  exact (@Law4293.models_iff G M).mp hM a b

private theorem hw4321 {G : Type} (M : Magma G) (hM : satisfies G Law4321) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW3 = @evalInMagma _ _ M ![b, a] symmW3 := by
  rw [eval_symmW3, eval_symmW3]
  exact (@Law4321.models_iff G M).mp hM a b

private theorem hw4343 {G : Type} (M : Magma G) (hM : satisfies G Law4343) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW4 = @evalInMagma _ _ M ![b, a] symmW4 := by
  rw [eval_symmW4, eval_symmW4]
  exact (@Law4343.models_iff G M).mp hM a b

private theorem hw4541 {G : Type} (M : Magma G) (hM : satisfies G Law4541) (a b : G) :
    @evalInMagma _ _ M ![a, b] symmW6 = @evalInMagma _ _ M ![b, a] symmW6 := by
  rw [eval_symmW6, eval_symmW6]
  exact symm4541 M ((@Law4541.models_iff G M).mp hM) a b

/-! ## The cells -/

theorem Equation332_definableFrom_Equation43 : Law332.DefinableFrom Law43 :=
  definableFrom_of_symmTerm symmW1 hw43 commIdem_332

theorem Equation3342_definableFrom_Equation43 : Law3342.DefinableFrom Law43 :=
  definableFrom_of_symmTerm symmW1 hw43 commIdem_3342

theorem Equation3545_definableFrom_Equation43 : Law3545.DefinableFrom Law43 :=
  definableFrom_of_symmTerm symmW1 hw43 commIdem_3545

theorem Equation4343_definableFrom_Equation43 : Law4343.DefinableFrom Law43 :=
  definableFrom_of_symmTerm symmW1 hw43 commIdem_4343

theorem Equation332_definableFrom_Equation546 : Law332.DefinableFrom Law546 :=
  definableFrom_of_symmTerm symmW5 hw546 commIdem_332

theorem Equation3342_definableFrom_Equation546 : Law3342.DefinableFrom Law546 :=
  definableFrom_of_symmTerm symmW5 hw546 commIdem_3342

theorem Equation3545_definableFrom_Equation546 : Law3545.DefinableFrom Law546 :=
  definableFrom_of_symmTerm symmW5 hw546 commIdem_3545

theorem Equation332_definableFrom_Equation3364 : Law332.DefinableFrom Law3364 :=
  definableFrom_of_symmTerm symmW1 hw3364 commIdem_332

theorem Equation332_definableFrom_Equation3607 : Law332.DefinableFrom Law3607 :=
  definableFrom_of_symmTerm symmW5 hw3607 commIdem_332

theorem Equation3342_definableFrom_Equation3607 : Law3342.DefinableFrom Law3607 :=
  definableFrom_of_symmTerm symmW5 hw3607 commIdem_3342

theorem Equation3545_definableFrom_Equation3607 : Law3545.DefinableFrom Law3607 :=
  definableFrom_of_symmTerm symmW5 hw3607 commIdem_3545

theorem Equation332_definableFrom_Equation4293 : Law332.DefinableFrom Law4293 :=
  definableFrom_of_symmTerm symmW2 hw4293 commIdem_332

theorem Equation3342_definableFrom_Equation4293 : Law3342.DefinableFrom Law4293 :=
  definableFrom_of_symmTerm symmW2 hw4293 commIdem_3342

theorem Equation3545_definableFrom_Equation4293 : Law3545.DefinableFrom Law4293 :=
  definableFrom_of_symmTerm symmW2 hw4293 commIdem_3545

theorem Equation4343_definableFrom_Equation4293 : Law4343.DefinableFrom Law4293 :=
  definableFrom_of_symmTerm symmW2 hw4293 commIdem_4343

theorem Equation332_definableFrom_Equation4321 : Law332.DefinableFrom Law4321 :=
  definableFrom_of_symmTerm symmW3 hw4321 commIdem_332

theorem Equation3342_definableFrom_Equation4321 : Law3342.DefinableFrom Law4321 :=
  definableFrom_of_symmTerm symmW3 hw4321 commIdem_3342

theorem Equation3545_definableFrom_Equation4321 : Law3545.DefinableFrom Law4321 :=
  definableFrom_of_symmTerm symmW3 hw4321 commIdem_3545

theorem Equation4343_definableFrom_Equation4321 : Law4343.DefinableFrom Law4321 :=
  definableFrom_of_symmTerm symmW3 hw4321 commIdem_4343

theorem Equation332_definableFrom_Equation4343 : Law332.DefinableFrom Law4343 :=
  definableFrom_of_symmTerm symmW4 hw4343 commIdem_332

theorem Equation3342_definableFrom_Equation4343 : Law3342.DefinableFrom Law4343 :=
  definableFrom_of_symmTerm symmW4 hw4343 commIdem_3342

theorem Equation3545_definableFrom_Equation4343 : Law3545.DefinableFrom Law4343 :=
  definableFrom_of_symmTerm symmW4 hw4343 commIdem_3545

theorem Equation332_definableFrom_Equation4541 : Law332.DefinableFrom Law4541 :=
  definableFrom_of_symmTerm symmW6 hw4541 commIdem_332

theorem Equation3342_definableFrom_Equation4541 : Law3342.DefinableFrom Law4541 :=
  definableFrom_of_symmTerm symmW6 hw4541 commIdem_3342

theorem Equation3545_definableFrom_Equation4541 : Law3545.DefinableFrom Law4541 :=
  definableFrom_of_symmTerm symmW6 hw4541 commIdem_3545

theorem Equation4343_definableFrom_Equation4541 : Law4343.DefinableFrom Law4541 :=
  definableFrom_of_symmTerm symmW6 hw4541 commIdem_4343

end Law.MagmaLaw

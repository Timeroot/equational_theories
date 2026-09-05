import equational_theories.Definability.DiagRow

/-!
# The diagonal as the head of a chain

`DiagRow` names `x ◇ x` as *the value the row of `x` misses*, which needs the row to be a
permutation: `∀ x z, ∃ y, x ◇ y = z` and `x ◇ y = x ◇ x → y = x`.  For a source like `1516`,
`x = (y ◇ y) ◇ (x ◇ (x ◇ y))`, neither is available over all magmas -- the law only says that the
rows of the *squares* are onto.  What it does say is exactly enough for a different reading.

Write `S(y) = y ◇ y` and `ψ_y(t) = t ◇ (t ◇ y)`.  The law is `S(y) ◇ ψ_y(t) = t`: every `ψ_y` is
injective and every `L_{S(y)}` is onto, with `ψ_y` for a section.  Now the key point, and the
reason no cancellation is needed:

> for **fixed** `u, w, v`, there is at most one `z` with `z ◇ u = w` and `z ◇ w = v`.

Indeed `ψ_u(z) = z ◇ (z ◇ u) = z ◇ w = v`, so the law at `y := u` gives `z = S(u) ◇ v` outright.
So `S(x)` is pinned as soon as one chain `v, ψ_x(v), ψ_x(ψ_x(v))` can be *written down*: with
`w = ψ_x(a)` and `u = ψ_x(w)`, both `S(x) ◇ w = a` and `S(x) ◇ u = w` are instances of the law,
and no other `z` satisfies the pair.

In the companion `x □ y = if x = y then x else x ◇ y` the chain is a term -- `ψ_x(a) = a □ (a □ x)`
-- provided the two `□` are honest, i.e. `a ≠ x` and `a ≠ a ◇ x`.  That is the whole content of
`Chain`: six disequations that make the six `□` of the chain agree with `◇`, and the two chain
equations.  `hsound` says a chain pins `x ◇ x`; `hcomp` says one exists.

`hcomp` can fail, and exactly one way: the honest reading of `ψ_x` needs points off
`Fix(R_x) = {u : u ◇ x = u}`, so a row of fixed points blinds the chain.  The `fbFormula`
disjunct covers that case -- when *every* `u` has `u □ x = u`, the source usually forces
`x ◇ x = x` and the diagonal is `x` again.  Between them the two disjuncts are a
`StructuralFrom` device, with no `Finite` hypothesis anywhere.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

attribute [local instance] instFOStructure

namespace DiagWit

variable {G : Type}

open DiagRepair (ap)

/-! ## The chain, semantically -/

/-- `ψ_x(a) = a ◇ (a ◇ x)`, read in whatever operation `P` is. -/
def wOf (P : Magma G) (x a : G) : G := P.op a (P.op a x)

/-- `ψ_x(ψ_x(a))`, the third link. -/
def uOf (P : Magma G) (x a : G) : G := wOf P x (wOf P x a)

/-- **The chain at `x` with head `a` and value `z`.**  The first four disequations make the four
`P`-applications that build `ψ_x(a)` and `ψ_x(ψ_x(a))` honest; the next two make the two equations
honest; the last two are the chain itself.  Everything is stated in `P`, because that is what the
formula sees. -/
def Chain (P : Magma G) (x z a : G) : Prop :=
  a ≠ x ∧ a ≠ P.op a x ∧ wOf P x a ≠ x ∧ wOf P x a ≠ P.op (wOf P x a) x ∧
    z ≠ wOf P x a ∧ z ≠ uOf P x a ∧
      P.op z (wOf P x a) = a ∧ P.op z (uOf P x a) = wOf P x a

/-! ## The chain, as a formula -/

/-- the output slot, under one binder -/
private def z1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inl none)
/-- the first argument, under one binder -/
private def x1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inl (some 0))
/-- the binder: the head of the chain -/
private def a1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inr 0)

/-- `ψ_x(a)` as a `□`-term. -/
private def wT (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  ap G a1 (ap G a1 x1)

/-- `ψ_x(ψ_x(a))` as a `□`-term. -/
private def uT (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  ap G (wT G) (ap G (wT G) x1)

/-- The body of `witFormula`: `Chain`, transcribed. -/
private def witBody (G : Type) :
    (MagmaLanguage[[(∅ : Set G)]]).BoundedFormula (Option (Fin 2)) 1 :=
  ∼(Term.bdEqual a1 x1) ⊓ (∼(Term.bdEqual a1 (ap G a1 x1)) ⊓
    (∼(Term.bdEqual (wT G) x1) ⊓ (∼(Term.bdEqual (wT G) (ap G (wT G) x1)) ⊓
      (∼(Term.bdEqual z1 (wT G)) ⊓ (∼(Term.bdEqual z1 (uT G)) ⊓
        (Term.bdEqual (ap G z1 (wT G)) a1 ⊓ Term.bdEqual (ap G z1 (uT G)) (wT G)))))))

/-- `∃ a, chain at x with head a and value z`. -/
def witFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (witBody G)

/-- `∀ u, u □ x = u`: the row of fixed points that blinds the chain. -/
def fbFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.all (Term.bdEqual (ap G a1 x1) a1)

theorem realize_witBody [P : Magma G] (v : Option (Fin 2) → G) (ys : Fin 1 → G) :
    BoundedFormula.Realize (witBody G) v ys ↔ Chain P (v (some 0)) (v none) (ys 0) := by
  simp only [witBody, wT, uT, z1, x1, a1, ap, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, Term.realize_functions_apply₂,
    Magma.FOStructure_funMap', Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr, Chain, wOf, uOf]

theorem realize_witFormula [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (witFormula G) v xs ↔
      ∃ a : G, Chain P (v (some 0)) (v none) a := by
  simp only [witFormula, BoundedFormula.realize_ex, realize_witBody]
  constructor
  · rintro ⟨a, h⟩
    exact ⟨_, h⟩
  · rintro ⟨a, h⟩
    refine ⟨a, ?_⟩
    simpa [Fin.snoc] using h

theorem realize_fbFormula [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (fbFormula G) v xs ↔ ∀ u : G, P.op u (v (some 0)) = u := by
  simp only [fbFormula, BoundedFormula.realize_all, BoundedFormula.realize_bdEqual, a1, x1, ap,
    Term.realize_functions_apply₂, Magma.FOStructure_funMap', Magma.FinArityOp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h u
    simpa [Fin.snoc] using h u
  · intro h u
    simpa [Fin.snoc] using h u

/-! ## The blind fallback

`fbFormula` is a needlessly strong reading of "the chain cannot be written down at `x`": it asks
for the row of `x` to consist entirely of fixed points, when all that matters is that *no* chain
at `x` exists.  Saying that instead needs the chain with its value slot bound, so the six
disequations and two equations are transcribed a second time over two binders. -/

/-- the first argument, under two binders -/
private def x2 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  Term.var (Sum.inl (some 0))
/-- the first binder: the value the chain would name -/
private def w2 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  Term.var (Sum.inr 0)
/-- the second binder: the head of the chain -/
private def a2 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  Term.var (Sum.inr 1)

/-- `ψ_x(a)`, under two binders. -/
private def wT2 (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  ap G a2 (ap G a2 x2)

/-- `ψ_x(ψ_x(a))`, under two binders. -/
private def uT2 (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  ap G (wT2 G) (ap G (wT2 G) x2)

/-- `Chain`, with both the value and the head bound. -/
private def chainBody2 (G : Type) :
    (MagmaLanguage[[(∅ : Set G)]]).BoundedFormula (Option (Fin 2)) 2 :=
  ∼(Term.bdEqual a2 x2) ⊓ (∼(Term.bdEqual a2 (ap G a2 x2)) ⊓
    (∼(Term.bdEqual (wT2 G) x2) ⊓ (∼(Term.bdEqual (wT2 G) (ap G (wT2 G) x2)) ⊓
      (∼(Term.bdEqual w2 (wT2 G)) ⊓ (∼(Term.bdEqual w2 (uT2 G)) ⊓
        (Term.bdEqual (ap G w2 (wT2 G)) a2 ⊓ Term.bdEqual (ap G w2 (uT2 G)) (wT2 G)))))))

/-- `∀ w a, ¬ chain at x with head a and value w`: the chain is unwritable at `x`. -/
def blindFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.all (BoundedFormula.all (∼(chainBody2 G)))

theorem realize_chainBody2 [P : Magma G] (v : Option (Fin 2) → G) (ys : Fin 2 → G) :
    BoundedFormula.Realize (chainBody2 G) v ys ↔ Chain P (v (some 0)) (ys 0) (ys 1) := by
  simp only [chainBody2, wT2, uT2, x2, w2, a2, ap, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, Term.realize_functions_apply₂,
    Magma.FOStructure_funMap', Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr, Chain, wOf, uOf]

theorem realize_blindFormula [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (blindFormula G) v xs ↔
      ∀ w a : G, ¬ Chain P (v (some 0)) w a := by
  simp only [blindFormula, BoundedFormula.realize_all, BoundedFormula.realize_not,
    realize_chainBody2]
  constructor
  · intro h w a
    simpa [Fin.snoc] using h w a
  · intro h w a
    simpa [Fin.snoc] using h w a

/-- the output slot -/
private def z0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl none)
/-- the first argument -/
private def x0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl (some 0))
/-- the second argument -/
private def y0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl (some 1))

/-- The reverse read: `x □ y` off the diagonal, the chain (or its fallback) on it. -/
def witRecFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (∼(Term.bdEqual x0 y0) ⊓ Term.bdEqual z0 (ap G x0 y0)) ⊔
    (Term.bdEqual x0 y0 ⊓ (witFormula G ⊔ (fbFormula G ⊓ Term.bdEqual z0 x0)))

/-- The reverse read, with the *blind* fallback: `x □ y` off the diagonal, the chain on it, and
`x` itself exactly when no chain at `x` can be written down. -/
def witRecFormula' (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (∼(Term.bdEqual x0 y0) ⊓ Term.bdEqual z0 (ap G x0 y0)) ⊔
    (Term.bdEqual x0 y0 ⊓ (witFormula G ⊔ (blindFormula G ⊓ Term.bdEqual z0 x0)))

variable (M : Magma G) (q : QFOp)

/-- **The reverse half.**  A chain names the diagonal, a blinded row falls back on `x`, and the
companion is `◇` everywhere else: that is `M.Graph`, `∅`-definable in the companion. -/
theorem definable_graph_wit
    (hoff : ∀ a b : G, a ≠ b → (q.magma M).op a b = M.op a b)
    (hsound : ∀ x z a : G, Chain (q.magma M) x z a → z = M.op x x)
    (hfb : ∀ x : G, (∀ u : G, (q.magma M).op u x = u) → M.op x x = x)
    (hcomp : ∀ x : G, (∃ a : G, Chain (q.magma M) x (M.op x x) a) ∨
      (∀ u : G, (q.magma M).op u x = u)) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  classical
  refine ⟨witRecFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [Set.mem_setOf_eq, witRecFormula, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, ap, Term.realize_functions_apply₂, Magma.FOStructure_funMap',
    Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one, Term.realize_var, Sum.elim_inl,
    @realize_witFormula _ (q.magma M) v, @realize_fbFormula _ (q.magma M) v]
  by_cases hxy : v (some 0) = v (some 1)
  · rw [← hxy]
    constructor
    · intro h
      refine Or.inr ⟨rfl, ?_⟩
      rcases hcomp (v (some 0)) with ⟨a, ha⟩ | hrow
      · exact Or.inl ⟨a, h ▸ ha⟩
      · exact Or.inr ⟨hrow, h.symm.trans (hfb _ hrow)⟩
    · rintro (⟨hne, -⟩ | ⟨-, ⟨a, ha⟩ | ⟨hrow, hzx⟩⟩)
      · exact absurd rfl hne
      · exact (hsound _ _ _ ha).symm
      · rw [hzx]
        exact hfb _ hrow
  · have hbox : (q.magma M).op (v (some 0)) (v (some 1))
        = M.op (v (some 0)) (v (some 1)) := hoff _ _ hxy
    constructor
    · intro h
      exact Or.inl ⟨hxy, by rw [hbox, h]⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · rw [← hbox, h]
      · exact absurd h hxy

/-- Glue: a target satisfied by the companion, plus the two chain obligations, settle a cell. -/
theorem structuralOnMagma_wit {β : Type*} {L : Law.MagmaLaw β}
    (hoff : ∀ a b : G, a ≠ b → (q.magma M).op a b = M.op a b)
    (hsound : ∀ x z a : G, Chain (q.magma M) x z a → z = M.op x x)
    (hfb : ∀ x : G, (∀ u : G, (q.magma M).op u x = u) → M.op x x = x)
    (hcomp : ∀ x : G, (∃ a : G, Chain (q.magma M) x (M.op x x) a) ∨
      (∀ u : G, (q.magma M).op u x = u))
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_wit M q hoff hsound hfb hcomp⟩

/-! ## The device with the blind fallback

Once the fallback reads "no chain at `x`" rather than "the row of `x` is all fixed points", the
two obligations `hfb` and `hcomp` merge into one.  Soundness already says every chain at `x` names
`x ◇ x`, so *no chain at all* is the same as *no chain naming `x ◇ x`*, and the only thing left to
check is that the diagonal is `x` whenever the chain cannot be written down. -/

/-- **The reverse half, blind fallback.**  Strictly weaker hypotheses than `definable_graph_wit`:
the row-of-fixed-points obligation is gone, and completeness only has to produce a chain when the
diagonal is not already `x`. -/
theorem definable_graph_wit'
    (hoff : ∀ a b : G, a ≠ b → (q.magma M).op a b = M.op a b)
    (hsound : ∀ x z a : G, Chain (q.magma M) x z a → z = M.op x x)
    (hcomp : ∀ x : G, (∃ a : G, Chain (q.magma M) x (M.op x x) a) ∨ M.op x x = x) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  classical
  refine ⟨witRecFormula' G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [Set.mem_setOf_eq, witRecFormula', Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, ap, Term.realize_functions_apply₂, Magma.FOStructure_funMap',
    Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one, Term.realize_var, Sum.elim_inl,
    @realize_witFormula _ (q.magma M) v, @realize_blindFormula _ (q.magma M) v]
  by_cases hxy : v (some 0) = v (some 1)
  · rw [← hxy]
    constructor
    · intro h
      refine Or.inr ⟨rfl, ?_⟩
      rcases hcomp (v (some 0)) with ⟨a, ha⟩ | hgx
      · exact Or.inl ⟨a, h ▸ ha⟩
      · by_cases hch : ∃ w a : G, Chain (q.magma M) (v (some 0)) w a
        · obtain ⟨w, a, ha⟩ := hch
          have hw : w = v none := (hsound _ _ _ ha).trans h
          exact Or.inl ⟨a, hw ▸ ha⟩
        · exact Or.inr ⟨fun w a ha ↦ hch ⟨w, a, ha⟩, h.symm.trans hgx⟩
    · rintro (⟨hne, -⟩ | ⟨-, ⟨a, ha⟩ | ⟨hbl, hzx⟩⟩)
      · exact absurd rfl hne
      · exact (hsound _ _ _ ha).symm
      · rw [hzx]
        rcases hcomp (v (some 0)) with ⟨a, ha⟩ | hgx
        · exact absurd ha (hbl _ _)
        · exact hgx
  · have hbox : (q.magma M).op (v (some 0)) (v (some 1))
        = M.op (v (some 0)) (v (some 1)) := hoff _ _ hxy
    constructor
    · intro h
      exact Or.inl ⟨hxy, by rw [hbox, h]⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · rw [← hbox, h]
      · exact absurd h hxy

/-- Glue for the blind fallback: one soundness obligation and one completeness obligation. -/
theorem structuralOnMagma_wit' {β : Type*} {L : Law.MagmaLaw β}
    (hoff : ∀ a b : G, a ≠ b → (q.magma M).op a b = M.op a b)
    (hsound : ∀ x z a : G, Chain (q.magma M) x z a → z = M.op x x)
    (hcomp : ∀ x : G, (∃ a : G, Chain (q.magma M) x (M.op x x) a) ∨ M.op x x = x)
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_wit' M q hoff hsound hcomp⟩

end DiagWit

import equational_theories.Definability.AutBox

/-!
# The diagonal as the value a row misses

`AutBox` fills the `Equation3` cell of 480 sources on a **finite** carrier: there
`∅`-definable is the same as `Aut`-invariant, so recovering `◇` from the companion
`x □ y = if x = y then A(x) else x ◇ y` is a group-theoretic obligation rather than a formula
problem.  Its cancellative front ends go one better, and their argument is not really about
finiteness at all -- `diagRigid_of_cancelLeft`'s docstring puts it exactly right:

> a left-cancellative operation has **rows that are permutations**, so `u ◇ u` is the single value
> the off-diagonal row `{u ◇ v : v ≠ u}` fails to take.

Finiteness is used only to turn injectivity of `v ↦ u ◇ v` into surjectivity.  Ask the source for
surjectivity outright and the row is a permutation over *every* carrier, so the missing value is
named by a first-order formula in the language of `□`:

    z = x ◇ x   ↔   ∀ y, y = x ∨ z ≠ x □ y.

That is this file.  Two facts about the source are needed, both about all magmas:

* `∀ x z, ∃ y, x ◇ y = z` -- the row is onto, so nothing outside `{x ◇ x}` is missed;
* `∀ x y, x ◇ y = x ◇ x → y = x` -- injectivity *at the diagonal only*, so `x ◇ x` is missed.

Surjectivity is free for the 227 sources whose `DiagFix` proof goes through
`AutBox.cancel_left_of_surj`: that lemma is handed a division term, and a term is a theorem about
every magma.  Only the injectivity half is new, and `RowQG.left`/`RowQG.right` package the pair.

Unlike `DiagRepair`, no word has to be searched for and no guard has to be witnessed, so the
subsingleton carrier is not special: there the quantifier `∀ y, y = x ∨ …` is satisfied by `y = x`
and `z = x ◇ x` holds anyway.  Unlike `AutBox`, there is no `Finite` hypothesis, so these are
`StructuralFrom` cells -- and the `Equation3` cell of a source drags its whole implication cone
with it.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

attribute [local instance] instFOStructure

namespace DiagRow

variable {G : Type}

open DiagRepair (ap)

/-- the output slot -/
private def z0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl none)
/-- the first argument -/
private def x0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl (some 0))
/-- the second argument -/
private def y0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl (some 1))

/-- the output slot, under one binder -/
private def z1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inl none)
/-- the first argument, under one binder -/
private def x1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inl (some 0))
/-- the binder -/
private def b1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inr 0)

/-- `∀ y, y = x ∨ z ≠ x □ y`: `z` is the value the row of `x` misses. -/
def rowFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.all (Term.bdEqual b1 x1 ⊔ ∼(Term.bdEqual z1 (ap G x1 b1)))

/-- `∀ y, y = x ∨ z ≠ y □ x`: `z` is the value the column of `x` misses. -/
def colFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.all (Term.bdEqual b1 x1 ⊔ ∼(Term.bdEqual z1 (ap G b1 x1)))

theorem realize_rowFormula [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (rowFormula G) v xs ↔
      ∀ y : G, y = v (some 0) ∨ v none ≠ P.op (v (some 0)) y := by
  simp only [rowFormula, BoundedFormula.realize_all, BoundedFormula.realize_sup,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, z1, x1, b1, ap,
    Term.realize_functions_apply₂, Magma.FOStructure_funMap', Magma.FinArityOp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h y
    simpa [Fin.snoc] using h y
  · intro h y
    simpa [Fin.snoc] using h y

theorem realize_colFormula [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (colFormula G) v xs ↔
      ∀ y : G, y = v (some 0) ∨ v none ≠ P.op y (v (some 0)) := by
  simp only [colFormula, BoundedFormula.realize_all, BoundedFormula.realize_sup,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, z1, x1, b1, ap,
    Term.realize_functions_apply₂, Magma.FOStructure_funMap', Magma.FinArityOp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h y
    simpa [Fin.snoc] using h y
  · intro h y
    simpa [Fin.snoc] using h y

/-- The reverse read: `x □ y` off the diagonal, the missing value of the row on it. -/
def rowRecFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (∼(Term.bdEqual x0 y0) ⊓ Term.bdEqual z0 (ap G x0 y0)) ⊔
    (Term.bdEqual x0 y0 ⊓ rowFormula G)

/-- The reverse read, column form. -/
def colRecFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (∼(Term.bdEqual x0 y0) ⊓ Term.bdEqual z0 (ap G x0 y0)) ⊔
    (Term.bdEqual x0 y0 ⊓ colFormula G)

variable (M : Magma G) (q : QFOp)

/-- **The reverse half, row form.**  If the row of `x` is onto and misses `x ◇ x`, the graph of
`◇` is `∅`-definable in any companion that agrees with `◇` off the diagonal. -/
theorem definable_graph_row
    (hoff : ∀ a b : G, a ≠ b → (q.magma M).op a b = M.op a b)
    (hinj : ∀ x y : G, M.op x y = M.op x x → y = x)
    (hsurj : ∀ x z : G, ∃ y : G, M.op x y = z) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  classical
  refine ⟨rowRecFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [Set.mem_setOf_eq, rowRecFormula, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, ap, Term.realize_functions_apply₂, Magma.FOStructure_funMap',
    Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one, Term.realize_var, Sum.elim_inl,
    @realize_rowFormula _ (q.magma M) v]
  by_cases hxy : v (some 0) = v (some 1)
  · rw [← hxy]
    constructor
    · intro h
      refine Or.inr ⟨rfl, fun y ↦ ?_⟩
      rcases eq_or_ne y (v (some 0)) with rfl | hy0
      · exact Or.inl rfl
      · refine Or.inr fun hc ↦ hy0 (hinj _ _ ?_)
        rw [← hoff _ _ (Ne.symm hy0), ← hc, h]
    · rintro (⟨hne, -⟩ | ⟨-, hrow⟩)
      · exact absurd rfl hne
      · obtain ⟨y, hy⟩ := hsurj (v (some 0)) (v none)
        rcases eq_or_ne y (v (some 0)) with rfl | hy0
        · exact hy
        · rcases hrow y with h | hne
          · exact absurd h hy0
          · exact absurd ((hoff _ _ (Ne.symm hy0)).trans hy).symm hne
  · have hbox : (q.magma M).op (v (some 0)) (v (some 1))
        = M.op (v (some 0)) (v (some 1)) := hoff _ _ hxy
    constructor
    · intro h
      exact Or.inl ⟨hxy, by rw [hbox, h]⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · rw [← hbox, h]
      · exact absurd h hxy

/-- **The reverse half, column form.** -/
theorem definable_graph_col
    (hoff : ∀ a b : G, a ≠ b → (q.magma M).op a b = M.op a b)
    (hinj : ∀ x y : G, M.op y x = M.op x x → y = x)
    (hsurj : ∀ x z : G, ∃ y : G, M.op y x = z) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  classical
  refine ⟨colRecFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [Set.mem_setOf_eq, colRecFormula, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, ap, Term.realize_functions_apply₂, Magma.FOStructure_funMap',
    Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one, Term.realize_var, Sum.elim_inl,
    @realize_colFormula _ (q.magma M) v]
  by_cases hxy : v (some 0) = v (some 1)
  · rw [← hxy]
    constructor
    · intro h
      refine Or.inr ⟨rfl, fun y ↦ ?_⟩
      rcases eq_or_ne y (v (some 0)) with rfl | hy0
      · exact Or.inl rfl
      · refine Or.inr fun hc ↦ hy0 (hinj _ _ ?_)
        rw [← hoff _ _ hy0, ← hc, h]
    · rintro (⟨hne, -⟩ | ⟨-, hcol⟩)
      · exact absurd rfl hne
      · obtain ⟨y, hy⟩ := hsurj (v (some 0)) (v none)
        rcases eq_or_ne y (v (some 0)) with rfl | hy0
        · exact hy
        · rcases hcol y with h | hne
          · exact absurd h hy0
          · exact absurd ((hoff _ _ hy0).trans hy).symm hne
  · have hbox : (q.magma M).op (v (some 0)) (v (some 1))
        = M.op (v (some 0)) (v (some 1)) := hoff _ _ hxy
    constructor
    · intro h
      exact Or.inl ⟨hxy, by rw [hbox, h]⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · rw [← hbox, h]
      · exact absurd h hxy

end DiagRow

namespace DiagRow

/-! ## The obligation as a property of the source alone

Like `AutBox.DiagFix`, neither half mentions the companion or the target, so a source pays once. -/

/-- Every model of the source has rows that are permutations: onto, and injective at the
diagonal.  Left cancellativity plus left division is the usual way to get it, but only these two
weaker facts are used. -/
abbrev RowQG (L' : Law.MagmaLaw ℕ) : Prop :=
  ∀ {G : Type} (M : Magma G), satisfies G L' →
    (∀ x y : G, M.op x y = M.op x x → y = x) ∧ (∀ x z : G, ∃ y : G, M.op x y = z)

/-- Columns instead of rows. -/
abbrev ColQG (L' : Law.MagmaLaw ℕ) : Prop :=
  ∀ {G : Type} (M : Magma G), satisfies G L' →
    (∀ x y : G, M.op y x = M.op x x → y = x) ∧ (∀ x z : G, ∃ y : G, M.op y x = z)

/-- Identity, so a script can `refine DiagRow.rowQG_of (fun {G} M hM ↦ ⟨?_, ?_⟩)`. -/
theorem rowQG_of {L' : Law.MagmaLaw ℕ}
    (h : ∀ {G : Type} (M : Magma G), satisfies G L' →
      (∀ x y : G, M.op x y = M.op x x → y = x) ∧ (∀ x z : G, ∃ y : G, M.op x y = z)) :
    RowQG L' := h

theorem colQG_of {L' : Law.MagmaLaw ℕ}
    (h : ∀ {G : Type} (M : Magma G), satisfies G L' →
      (∀ x y : G, M.op y x = M.op x x → y = x) ∧ (∀ x z : G, ∃ y : G, M.op y x = z)) :
    ColQG L' := h

/-- `RowQG` is antitone in the law, exactly as `AutBox.diagFix_mono`. -/
theorem rowQG_mono {L L' : Law.MagmaLaw ℕ}
    (h : ∀ {G : Type} (M : Magma G), @satisfies _ G M L → @satisfies _ G M L')
    (hq : RowQG L') : RowQG L :=
  fun M hM ↦ hq M (h M hM)

theorem colQG_mono {L L' : Law.MagmaLaw ℕ}
    (h : ∀ {G : Type} (M : Magma G), @satisfies _ G M L → @satisfies _ G M L')
    (hq : ColQG L') : ColQG L :=
  fun M hM ↦ hq M (h M hM)

/-- Full left cancellativity is more than the row form needs, but it is what a prover usually
proves. -/
theorem rowQG_of_cancel {L' : Law.MagmaLaw ℕ}
    (hc : ∀ {G : Type} (M : Magma G), satisfies G L' → ∀ u v v' : G,
      M.op u v = M.op u v' → v = v')
    (hd : ∀ {G : Type} (M : Magma G), satisfies G L' → ∀ x z : G, ∃ y : G, M.op x y = z) :
    RowQG L' :=
  fun M hM ↦ ⟨fun x y h ↦ hc M hM x y x h, hd M hM⟩

theorem colQG_of_cancel {L' : Law.MagmaLaw ℕ}
    (hc : ∀ {G : Type} (M : Magma G), satisfies G L' → ∀ u v v' : G,
      M.op v u = M.op v' u → v = v')
    (hd : ∀ {G : Type} (M : Magma G), satisfies G L' → ∀ x z : G, ∃ y : G, M.op y x = z) :
    ColQG L' :=
  fun M hM ↦ ⟨fun x y h ↦ hc M hM x y x h, hd M hM⟩

/-! ## The devices -/

/-- **The device, row form.**  A companion agreeing with `◇` off the diagonal, plus permutation
rows on the source, settle a whole `StructuralFrom` cell -- over every carrier. -/
theorem structuralFrom_rowOf {L L' : Law.MagmaLaw ℕ} (q : QFOp)
    (hoff : ∀ {G : Type} (M : Magma G) (a b : G), a ≠ b → (q.magma M).op a b = M.op a b)
    (hq : RowQG L')
    (hL : ∀ {G : Type} (M : Magma G), satisfies G L' → @satisfies _ G (q.magma M) L) :
    L.StructuralFrom L' :=
  fun M hM ↦ ⟨q.magma M, hL M hM, q.definable_graph M,
    definable_graph_row M q (hoff M) (hq M hM).1 (hq M hM).2⟩

/-- **The device, column form.** -/
theorem structuralFrom_colOf {L L' : Law.MagmaLaw ℕ} (q : QFOp)
    (hoff : ∀ {G : Type} (M : Magma G) (a b : G), a ≠ b → (q.magma M).op a b = M.op a b)
    (hq : ColQG L')
    (hL : ∀ {G : Type} (M : Magma G), satisfies G L' → @satisfies _ G (q.magma M) L) :
    L.StructuralFrom L' :=
  fun M hM ↦ ⟨q.magma M, hL M hM, q.definable_graph M,
    definable_graph_col M q (hoff M) (hq M hM).1 (hq M hM).2⟩

open QFOp in
/-- The `idem` companion: the `Equation3` cell of the source, over all magmas. -/
theorem structuralFrom_idem_row {L' : Law.MagmaLaw ℕ} (hq : RowQG L') :
    Law3.StructuralFrom L' :=
  structuralFrom_rowOf idem (fun M a b h ↦ idem_ne M a b h) hq
    (fun M _ ↦ (@Law3.models_iff _ (idem.magma M)).mpr fun x ↦ (idem_diag M x).symm)

open QFOp in
theorem structuralFrom_idem_col {L' : Law.MagmaLaw ℕ} (hq : ColQG L') :
    Law3.StructuralFrom L' :=
  structuralFrom_colOf idem (fun M a b h ↦ idem_ne M a b h) hq
    (fun M _ ↦ (@Law3.models_iff _ (idem.magma M)).mpr fun x ↦ (idem_diag M x).symm)

open QFOp in
/-- **The reuse device.**  Any diagonal word `A` gives another companion, hence another target,
for the same source obligation. -/
theorem structuralFrom_diagOf_row {L L' : Law.MagmaLaw ℕ} (A : FreeMagma (Fin 2)) (hq : RowQG L')
    (hsat : ∀ {G : Type} (M : Magma G), satisfies G L' →
      @satisfies _ G ((diagOf A).magma M) L) :
    L.StructuralFrom L' :=
  structuralFrom_rowOf (diagOf A) (fun M a b h ↦ diagOf_ne A M a b h) hq hsat

open QFOp in
theorem structuralFrom_diagOf_col {L L' : Law.MagmaLaw ℕ} (A : FreeMagma (Fin 2)) (hq : ColQG L')
    (hsat : ∀ {G : Type} (M : Magma G), satisfies G L' →
      @satisfies _ G ((diagOf A).magma M) L) :
    L.StructuralFrom L' :=
  structuralFrom_colOf (diagOf A) (fun M a b h ↦ diagOf_ne A M a b h) hq hsat

end DiagRow

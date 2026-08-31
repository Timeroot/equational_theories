import equational_theories.Definability.CaseSplit

/-!
# Diagonal repair: reading `◇` back out of `□`

`QFOp.diagOf A` overwrites the diagonal of the source operation with a unary `◇`-word,

    x □ y := if x = y then A(x) else x ◇ y,

which is `∅`-definable for free -- `QFOp.definable_graph` is the whole forward half of
`StructuralOnMagma`.  What `□` throws away is exactly the diagonal map `d x = x ◇ x`, and that is
all the reverse half has to recover: off the diagonal `x ◇ y` *is* `x □ y`, so

    x ◇ y = z   ↔   (x ≠ y ∧ z = x □ y) ∨ (x = y ∧ z = d x).

The device therefore lives or dies on whether `d` is `∅`-definable in `□`.  On a finite magma that
is the same as `Aut(□) = Aut(◇)`, which is a decidable screen but not a proof and says nothing
about infinite models.  What this file asks for instead is a *guarded word*: a `□`-word `u(x, a)`
together with a list of disequations between `□`-words, such that

* every `a` satisfying the guards has `u(x, a) = x ◇ x`  (`hsound`), and
* some `a` satisfies the guards                          (`hwit`).

Then `∃ a, guards ∧ z = u(x, a)` defines the diagonal, and both obligations are first-order --
in fact universal-existential -- consequences of the source law, which is what a prover can be
handed.

At `A = Lf 0` -- the `CaseSplit.idem` companion, `x □ x = x` -- an unguarded word is never any use:
`u(x, x)` collapses to `x` and `hsound` would force `x ◇ x = x`, i.e. the source already satisfies
`Equation3` and `□ = ◇`.  There the guards are the whole content.  A longer `A` keeps part of the
diagonal visible in the box, so `x □ x = A(x)` is real information; it also changes the equational
theory of the box, which is what the target half `hL` sees, so a second `A` reaches targets the
first cannot.  The guards still make `hwit` fail on a one-element carrier, so that case is split off
separately; there every law holds and every set is definable.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

attribute [local instance] instFOStructure

namespace QFOp

/-- Off the diagonal `□` is `◇`.  Paired with `idem_diag` this is the whole equational theory of
the companion, and it is what the recovery obligations get proved from: rewriting with these two
never leaves an `if` behind, whereas `idem_apply` does and the leftover conditions are themselves
`if`s that `split_ifs` will not look inside. -/
theorem idem_ne {G : Type} (M : Magma G) (a b : G) (h : a ≠ b) :
    (idem.magma M).op a b = M.op a b := by
  rw [idem_apply]
  exact if_neg h

theorem idem_eq {G : Type} (M : Magma G) (a b : G) (h : a = b) :
    (idem.magma M).op a b = a := by
  rw [idem_apply]
  exact if_pos h

/-- `x □ y := if x = y then A(x) else x ◇ y`, the source operation with its diagonal overwritten by
a word in the first argument.  `A = Lf 0` is `idem`; anything else leaves part of the diagonal
visible in the box, which is exactly what the recovery word has to work with, and changes the
equational theory of the box, which is what the target half sees. -/
def diagOf (A : FreeMagma (Fin 2)) : QFOp :=
  .ite (Lf 0) (Lf 1) (.leaf A) (.leaf (Lf 0 ⋆ Lf 1))

open scoped Classical in
theorem diagOf_apply {G : Type} (A : FreeMagma (Fin 2)) (M : Magma G) (a b : G) :
    ((diagOf A).magma M).op a b = if a = b then @evalInMagma _ _ M ![a, b] A else M.op a b := by
  show @eval _ M (diagOf A) ![a, b] = _
  simp only [diagOf, eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem diagOf_ne {G : Type} (A : FreeMagma (Fin 2)) (M : Magma G) (a b : G) (h : a ≠ b) :
    ((diagOf A).magma M).op a b = M.op a b := by
  rw [diagOf_apply]
  exact if_neg h

theorem diagOf_eq {G : Type} (A : FreeMagma (Fin 2)) (M : Magma G) (a b : G) (h : a = b) :
    ((diagOf A).magma M).op a b = @evalInMagma _ _ M ![a, b] A := by
  rw [diagOf_apply]
  exact if_pos h

end QFOp

namespace DiagRepair

variable {G : Type}

/-- The application of `□` inside a term. -/
def ap (G : Type) {α : Type} (a b : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    (MagmaLanguage[[(∅ : Set G)]]).Term α :=
  Functions.apply₂ (L := MagmaLanguage[[(∅ : Set G)]]) (Sum.inl ()) a b

/-- A `□`-word in two variables, read over an arbitrary pair of terms. -/
def wordOn (G : Type) {α : Type} (f : Fin 2 → (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    FreeMagma (Fin 2) → (MagmaLanguage[[(∅ : Set G)]]).Term α
  | .Leaf a => f a
  | m₁ ⋆ m₂ => ap G (wordOn G f m₁) (wordOn G f m₂)

theorem realize_wordOn [N : Magma G] {α : Type} (w : α → G)
    (f : Fin 2 → (MagmaLanguage[[(∅ : Set G)]]).Term α) (t : FreeMagma (Fin 2)) :
    Term.realize w (wordOn G f t) = t ⬝ fun a ↦ Term.realize w (f a) := by
  induction t with
  | Leaf a => rfl
  | Fork m₁ m₂ ih₁ ih₂ =>
    simp only [wordOn, ap, Term.realize_functions_apply₂, Magma.FOStructure_funMap',
      evalInMagma, ih₁, ih₂]
    rfl

theorem cons_realize [Magma G] {α : Type} (w : α → G)
    (t₀ t₁ : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    (fun a ↦ Term.realize w (![t₀, t₁] a)) = ![Term.realize w t₀, Term.realize w t₁] := by
  funext a
  match a with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- The two terms a word of the diagonal formula is read over: the first argument of the graph, and
the single binder. -/
def xa (G : Type) : Fin 2 → (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  ![Term.var (Sum.inl (some 0)), Term.var (Sum.inr 0)]

/-- The guard: a conjunction of disequations between `□`-words in `x` and the binder. -/
def guardOn (G : Type) : List (FreeMagma (Fin 2) × FreeMagma (Fin 2)) →
    (MagmaLanguage[[(∅ : Set G)]]).BoundedFormula (Option (Fin 2)) 1
  | [] => ⊤
  | pq :: r => (∼(Term.bdEqual (wordOn G (xa G) pq.1) (wordOn G (xa G) pq.2))) ⊓ guardOn G r

theorem realize_guardOn [P : Magma G] (gs : List (FreeMagma (Fin 2) × FreeMagma (Fin 2)))
    (v : Option (Fin 2) → G) (xs : Fin 1 → G) :
    BoundedFormula.Realize (guardOn G gs) v xs ↔
      ∀ pq ∈ gs, pq.1 ⬝ ![v (some 0), xs 0] ≠ pq.2 ⬝ ![v (some 0), xs 0] := by
  induction gs with
  | nil => simp [guardOn]
  | cons pq r ih =>
    have hx : (fun a ↦ Term.realize (Sum.elim v xs) (xa G a)) = ![v (some 0), xs 0] := by
      rw [xa, cons_realize]
      rfl
    simp only [guardOn, BoundedFormula.realize_inf, BoundedFormula.realize_not,
      BoundedFormula.realize_bdEqual, realize_wordOn, hx, ih, List.forall_mem_cons]

/-- `∃ a, guards ∧ z = u(x, a)`: the diagonal of `◇`, written in the language of `□`. -/
def diagFormula (G : Type) (u : FreeMagma (Fin 2))
    (gs : List (FreeMagma (Fin 2) × FreeMagma (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex
    (guardOn G gs ⊓ Term.bdEqual (Term.var (Sum.inl none)) (wordOn G (xa G) u))

theorem realize_diagFormula [P : Magma G] (u : FreeMagma (Fin 2))
    (gs : List (FreeMagma (Fin 2) × FreeMagma (Fin 2))) (v : Option (Fin 2) → G)
    (xs : Fin 0 → G) :
    BoundedFormula.Realize (diagFormula G u gs) v xs ↔
      ∃ a : G, (∀ pq ∈ gs, pq.1 ⬝ ![v (some 0), a] ≠ pq.2 ⬝ ![v (some 0), a]) ∧
        v none = u ⬝ ![v (some 0), a] := by
  have key : ∀ ys : Fin 1 → G,
      BoundedFormula.Realize
        (guardOn G gs ⊓ Term.bdEqual (Term.var (Sum.inl none)) (wordOn G (xa G) u))
        v ys ↔
      (∀ pq ∈ gs, pq.1 ⬝ ![v (some 0), ys 0] ≠ pq.2 ⬝ ![v (some 0), ys 0]) ∧
        v none = u ⬝ ![v (some 0), ys 0] := by
    intro ys
    have hx : (fun a ↦ Term.realize (Sum.elim v ys) (xa G a)) = ![v (some 0), ys 0] := by
      rw [xa, cons_realize]
      rfl
    simp only [BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual, realize_guardOn,
      realize_wordOn, hx, Term.realize_var, Sum.elim_inl]
  simp only [diagFormula, BoundedFormula.realize_ex, key]
  constructor
  · rintro ⟨a, h⟩
    exact ⟨_, h⟩
  · rintro ⟨a, h⟩
    refine ⟨a, ?_⟩
    simpa [Fin.snoc] using h

/-- the output slot -/
private def z0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl none)
/-- the first argument -/
private def x0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl (some 0))
/-- the second argument -/
private def y0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl (some 1))

/-- The reverse read in full: `x □ y` off the diagonal, the guarded word on it. -/
def recFormula (G : Type) (u : FreeMagma (Fin 2))
    (gs : List (FreeMagma (Fin 2) × FreeMagma (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (∼(Term.bdEqual x0 y0) ⊓ Term.bdEqual z0 (ap G x0 y0)) ⊔
    (Term.bdEqual x0 y0 ⊓ diagFormula G u gs)

variable (M : Magma G) (q : QFOp) (u : FreeMagma (Fin 2))
  (gs : List (FreeMagma (Fin 2) × FreeMagma (Fin 2)))

open QFOp in
/-- **The reverse half.**  If the guarded word names the diagonal of `◇` and the guards are
satisfiable, `M.Graph` is `∅`-definable in the repaired operation.

Nothing here is about `idem` in particular.  The companion may be any decision tree that agrees
with `◇` off the diagonal (`hoff`); what it puts *on* the diagonal is exactly what the guarded word
has to undo, and `A(x) = x` is only the simplest choice. -/
theorem definable_graph_rec
    (hoff : ∀ a b : G, a ≠ b → (q.magma M).op a b = M.op a b)
    (hsound : ∀ x a : G, (∀ pq ∈ gs, @evalInMagma _ _ (q.magma M) ![x, a] pq.1
          ≠ @evalInMagma _ _ (q.magma M) ![x, a] pq.2) →
        @evalInMagma _ _ (q.magma M) ![x, a] u = M.op x x)
    (hwit : ∀ x : G, ∃ a : G, ∀ pq ∈ gs, @evalInMagma _ _ (q.magma M) ![x, a] pq.1
          ≠ @evalInMagma _ _ (q.magma M) ![x, a] pq.2) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  classical
  refine ⟨recFormula G u gs, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [Set.mem_setOf_eq, recFormula, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, ap, Term.realize_functions_apply₂, Magma.FOStructure_funMap',
    Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one, Term.realize_var, Sum.elim_inl,
    @realize_diagFormula _ (q.magma M) u gs v]
  by_cases hxy : v (some 0) = v (some 1)
  · obtain ⟨a, ha⟩ := hwit (v (some 0))
    have hd : M.op (v (some 0)) (v (some 0)) = M.op (v (some 0)) (v (some 1)) := by rw [hxy]
    constructor
    · intro h
      exact Or.inr ⟨hxy, a, ha, by rw [hsound _ _ ha, hd, h]⟩
    · rintro (⟨hne, -⟩ | ⟨-, b, hb, hbv⟩)
      · exact absurd hxy hne
      · rw [hbv, hsound _ _ hb, hd]
  · have hbox : (q.magma M).op (v (some 0)) (v (some 1))
        = M.op (v (some 0)) (v (some 1)) := hoff _ _ hxy
    constructor
    · intro h
      exact Or.inl ⟨hxy, by rw [hbox, h]⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · rw [← hbox, h]
      · exact absurd h hxy

open QFOp in
/-- Glue: a target satisfied by the repaired operation, plus a guarded word that names the
diagonal, settles the cell. -/
theorem structuralOnMagma_rec {β : Type*} {L : Law.MagmaLaw β}
    (hoff : ∀ a b : G, a ≠ b → (q.magma M).op a b = M.op a b)
    (hsound : ∀ x a : G, (∀ pq ∈ gs, @evalInMagma _ _ (q.magma M) ![x, a] pq.1
          ≠ @evalInMagma _ _ (q.magma M) ![x, a] pq.2) →
        @evalInMagma _ _ (q.magma M) ![x, a] u = M.op x x)
    (hwit : ∀ x : G, ∃ a : G, ∀ pq ∈ gs, @evalInMagma _ _ (q.magma M) ![x, a] pq.1
          ≠ @evalInMagma _ _ (q.magma M) ![x, a] pq.2)
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_rec M q u gs hoff hsound hwit⟩

/-! ## The one-element carrier

`hwit` can never hold on a subsingleton -- every `□`-word in `x` and `a` is `x` -- so that case has
to be handled outright.  It is free: on a subsingleton every law holds and every set is cut out by
`z = x ◇ y`. -/

/-- Every law is structural on a subsingleton magma. -/
theorem structuralOnMagma_of_subsingleton {β : Type*} {L : Law.MagmaLaw β} [Subsingleton G]
    (M : Magma G) : L.StructuralOnMagma M := by
  refine ⟨M, ?_, ?_, ?_⟩
  · intro _
    exact Subsingleton.elim _ _
  · exact ⟨QFOp.toFormula G (.leaf (Lf 0 ⋆ Lf 1)), Set.ext fun v ↦ by
      simp only [Set.mem_setOf_eq]
      exact iff_of_true (Subsingleton.elim _ _) (by
        simp [QFOp.toFormula, Formula.realize_equal, FreeMagma.realize_toTerm₂]
        exact Subsingleton.elim _ _)⟩
  · exact ⟨QFOp.toFormula G (.leaf (Lf 0 ⋆ Lf 1)), Set.ext fun v ↦ by
      simp only [Set.mem_setOf_eq]
      exact iff_of_true (Subsingleton.elim _ _) (by
        simp [QFOp.toFormula, Formula.realize_equal, FreeMagma.realize_toTerm₂]
        exact Subsingleton.elim _ _)⟩

/-! ## The guard that needs no witness

`hwit` asks for an `a` satisfying the guards, uniformly in `x`, and for a guard like `x ≠ a □ x`
there is no term to point at.  The one guard that supplies its own witness is `a ≠ x`: on any
carrier with two points such an `a` exists.  It is also, empirically, the guard nearly every
recovery uses, so this specialisation is the device in practice. -/

/-- The only guard is `a ≠ x`. -/
def neGuard : List (FreeMagma (Fin 2) × FreeMagma (Fin 2)) := [(Lf 1, Lf 0)]

theorem neGuard_iff [Magma G] (x a : G) :
    (∀ pq ∈ neGuard, pq.1 ⬝ ![x, a] ≠ pq.2 ⬝ ![x, a]) ↔ a ≠ x := by
  simp only [neGuard, List.mem_singleton, forall_eq]
  exact Iff.rfl

open QFOp in
/-- The device on one magma: a `□`-word that names the diagonal off the diagonal. -/
theorem structuralOnMagma_neOf {β : Type*} {L : Law.MagmaLaw β} [Nontrivial G]
    (M : Magma G) (q : QFOp) (u : FreeMagma (Fin 2))
    (hoff : ∀ a b : G, a ≠ b → (q.magma M).op a b = M.op a b)
    (hsound : ∀ x a : G, a ≠ x → @evalInMagma _ _ (q.magma M) ![x, a] u = M.op x x)
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  structuralOnMagma_rec M q u neGuard hoff
    (fun x a hg ↦ hsound x a ((@neGuard_iff _ (q.magma M) x a).mp hg))
    (fun x ↦ (exists_ne x).imp fun a ha ↦ (@neGuard_iff _ (q.magma M) x a).mpr ha) hL

open QFOp in
/-- **The device.**  One companion, one word and two obligations settle a whole cell: the companion
has to agree with `◇` off the diagonal and satisfy the target, and the word has to name `x ◇ x` at
every `a ≠ x`. -/
theorem structuralFrom_neOf {β : Type*} {L L' : Law.MagmaLaw β} (q : QFOp)
    (u : FreeMagma (Fin 2))
    (hoff : ∀ {G : Type} (M : Magma G) (a b : G), a ≠ b → (q.magma M).op a b = M.op a b)
    (hsound : ∀ {G : Type} (M : Magma G), satisfies G L' → ∀ x a : G, a ≠ x →
        @evalInMagma _ _ (q.magma M) ![x, a] u = M.op x x)
    (hL : ∀ {G : Type} (M : Magma G), satisfies G L' → @satisfies _ G (q.magma M) L) :
    L.StructuralFrom L' := by
  intro G M hM
  rcases subsingleton_or_nontrivial G with hs | hn
  · exact structuralOnMagma_of_subsingleton M
  · exact structuralOnMagma_neOf M q u (hoff M) (hsound M hM) (hL M hM)

open QFOp in
/-- The `idem` companion, which is `A(x) = x`. -/
theorem structuralOnMagma_ne {β : Type*} {L : Law.MagmaLaw β} [Nontrivial G]
    (M : Magma G) (u : FreeMagma (Fin 2))
    (hsound : ∀ x a : G, a ≠ x → @evalInMagma _ _ (idem.magma M) ![x, a] u = M.op x x)
    (hL : @satisfies _ G (idem.magma M) L) : L.StructuralOnMagma M :=
  structuralOnMagma_neOf M idem u (fun a b h ↦ idem_ne M a b h) hsound hL

open QFOp in
theorem structuralFrom_ne {β : Type*} {L L' : Law.MagmaLaw β} (u : FreeMagma (Fin 2))
    (hsound : ∀ {G : Type} (M : Magma G), satisfies G L' → ∀ x a : G, a ≠ x →
        @evalInMagma _ _ (idem.magma M) ![x, a] u = M.op x x)
    (hL : ∀ {G : Type} (M : Magma G), satisfies G L' → @satisfies _ G (idem.magma M) L) :
    L.StructuralFrom L' :=
  structuralFrom_neOf idem u (fun M a b h ↦ idem_ne M a b h) hsound hL

end DiagRepair

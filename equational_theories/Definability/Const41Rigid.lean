import equational_theories.Definability.Const41

/-!
# Source 41: the seven targets an idempotent tree is needed for

`Definability/Const41.lean` settles 178 of source 41's 188 open targets with five decision trees,
all of which share the reverse definition `x ◇ y := x □ x`: they send every square to the constant
`c`, so the source is read straight back off the diagonal.

Seven targets resist that, and they resist it for a reason. Each of

    x = (x ◇ x) ◇ (x ◇ y)              x = (x ◇ x) ◇ (y ◇ x)
    x = (x ◇ x) ◇ (x ◇ (x ◇ y))        x = (x ◇ x) ◇ (x ◇ (y ◇ x))
    x = (x ◇ x) ◇ ((y ◇ x) ◇ x)        x = (x ◇ x) ◇ ((y ◇ x) ◇ y)
    x = (x ◇ y) ◇ ((y ◇ z) ◇ x)

has `x` alone on the left, so no operation with a constant diagonal can satisfy it: put `y := x`
and the right-hand side becomes a value of the constant, the same for every `x`. Of the
twenty-four `∅`-definable operations on a constant magma the ones that survive are therefore
**idempotent** off `c`, and then `c` is no longer a `□`-term. It is still first-order, though:

    tC   x □ y := if y = c then x else if y = x then x else c        `c` is the only right identity
    tB   x □ y := if x = c then c else if y = c then x else y        `c` is the only left zero

and one universal quantifier says so. That is `ridFormula` / `lzeroFormula` below.

The uniqueness fails on a two-element carrier -- both trees degenerate to the left projection
there, which has no definable point at all -- so the argument splits, and the failure of
uniqueness is itself the branch condition: an element that is a right identity and is not `c`
*exhibits* the carrier as `{c, d}`. On such a carrier the source has no automorphism to respect,
and a hand-built two-valued operation finishes the job.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

attribute [local instance] instFOStructure

namespace Const41

variable {G : Type} (M : Magma G)

/-! ## The two idempotent trees -/

/-- `x □ y := if y = c then x else if y = x then x else c`, i.e. `x` when `y ∈ {c, x}` and `c`
otherwise. -/
def tC : QFOp :=
  .ite (Lf 1 ⋆ Lf 1) (Lf 1) (.leaf (Lf 0))
    (.ite (Lf 1) (Lf 0) (.leaf (Lf 0)) (.leaf (Lf 0 ⋆ Lf 0)))

/-- `x □ y := if x = c then c else if y = c then x else y`. -/
def tB : QFOp :=
  .ite (Lf 0 ⋆ Lf 0) (Lf 0) (.leaf (Lf 0 ⋆ Lf 0))
    (.ite (Lf 1 ⋆ Lf 1) (Lf 1) (.leaf (Lf 0)) (.leaf (Lf 1)))

open scoped Classical in
theorem tC_apply (c a b : G) (hc : ∀ u v : G, M.op u v = c) :
    (tC.magma M).op a b = if b = c then a else if b = a then a else c := by
  show @QFOp.eval _ M tC ![a, b] = _
  simp only [tC, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  rcases eq_or_ne b c with h | h
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

open scoped Classical in
theorem tB_apply (c a b : G) (hc : ∀ u v : G, M.op u v = c) :
    (tB.magma M).op a b = if a = c then c else if b = c then a else b := by
  show @QFOp.eval _ M tB ![a, b] = _
  simp only [tB, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  rcases eq_or_ne a c with h | h
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]
    rcases eq_or_ne b c with h' | h'
    · rw [if_pos h'.symm, if_pos h']
    · rw [if_neg (Ne.symm h'), if_neg h']

/-! ## Naming the constant with one quantifier -/

/-- The application of `□` inside a term of the magma language. -/
private def ap (G : Type) {α : Type} (a b : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    (MagmaLanguage[[(∅ : Set G)]]).Term α :=
  Functions.apply₂ (L := MagmaLanguage[[(∅ : Set G)]]) (Sum.inl ()) a b

/-- `∀ p, p □ z = p`: the output slot is a right identity of `□`. -/
def ridFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  ∀' Term.bdEqual (ap G (Term.var (Sum.inr 0)) (Term.var (Sum.inl none)))
      (Term.var (Sum.inr 0))

/-- `∀ p, z □ p = z`: the output slot is a left zero of `□`. -/
def lzeroFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  ∀' Term.bdEqual (ap G (Term.var (Sum.inl none)) (Term.var (Sum.inr 0)))
      (Term.var (Sum.inl none))

private theorem snoc_zero {G : Type} (a : G) :
    (Fin.snoc (default : Fin 0 → G) a : Fin 1 → G) 0 = a := rfl

theorem realize_ridFormula [N : Magma G] (w : Option (Fin 2) → G) :
    (ridFormula G).Realize w ↔ ∀ p : G, N.op p (w none) = p := by
  simp only [ridFormula, ap, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_bdEqual, Term.realize_functions_apply₂, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, snoc_zero, Magma.FOStructure_funMap', Magma.FinArityOp,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem realize_lzeroFormula [N : Magma G] (w : Option (Fin 2) → G) :
    (lzeroFormula G).Realize w ↔ ∀ p : G, N.op (w none) p = w none := by
  simp only [lzeroFormula, ap, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_bdEqual, Term.realize_functions_apply₂, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, snoc_zero, Magma.FOStructure_funMap', Magma.FinArityOp,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The reverse half, for a tree whose unique right identity is the source constant. -/
theorem definable_graph_rid (q : QFOp)
    (hun : ∀ z u v : G, (∀ p : G, (q.magma M).op p z = p) ↔ z = M.op u v) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  refine ⟨ridFormula G, Set.ext fun w ↦ ?_⟩
  rw [Set.mem_setOf_eq, @realize_ridFormula _ (q.magma M) w]
  show M.op (w (some 0)) (w (some 1)) = w none ↔ _
  rw [hun (w none) (w (some 0)) (w (some 1))]
  exact eq_comm

/-- The reverse half, for a tree whose unique left zero is the source constant. -/
theorem definable_graph_lzero (q : QFOp)
    (hun : ∀ z u v : G, (∀ p : G, (q.magma M).op z p = z) ↔ z = M.op u v) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  refine ⟨lzeroFormula G, Set.ext fun w ↦ ?_⟩
  rw [Set.mem_setOf_eq, @realize_lzeroFormula _ (q.magma M) w]
  show M.op (w (some 0)) (w (some 1)) = w none ↔ _
  rw [hun (w none) (w (some 0)) (w (some 1))]
  exact eq_comm

/-- Glue, for a tree whose unique right identity is the source constant. -/
theorem structuralOn_rid {β : Type*} {L : Law.MagmaLaw β} (q : QFOp)
    (hun : ∀ z u v : G, (∀ p : G, (q.magma M).op p z = p) ↔ z = M.op u v)
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_rid M q hun⟩

/-- Glue, for a tree whose unique left zero is the source constant. -/
theorem structuralOn_lzero {β : Type*} {L : Law.MagmaLaw β} (q : QFOp)
    (hun : ∀ z u v : G, (∀ p : G, (q.magma M).op z p = z) ↔ z = M.op u v)
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_lzero M q hun⟩

/-! ## Where uniqueness fails, the carrier has two points

`tC` sends `p □ z` to `p` exactly when `z ∈ {c, p}`, so a right identity other than `c` can only
be the whole carrier minus `c`; `tB` behaves the same way on the other side. -/

theorem two_of_rid (h41 : Equation41 G) (z u v : G)
    (hz : ∀ p : G, (tC.magma M).op p z = p) (hne : z ≠ M.op u v) (w : G) :
    w = M.op u v ∨ w = z := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : G, ∀ p q : G, M.op p q = c := ⟨M.op u v, const_of_41 M h41 u v⟩
  rw [hc u v] at hne ⊢
  have h := hz w
  rw [tC_apply M c w z hc] at h
  split_ifs at h with h1 h2
  · exact absurd h1 hne
  · exact Or.inr h2.symm
  · exact Or.inl h.symm

theorem two_of_lzero (h41 : Equation41 G) (z u v : G)
    (hz : ∀ p : G, (tB.magma M).op z p = z) (hne : z ≠ M.op u v) (w : G) :
    w = M.op u v ∨ w = z := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : G, ∀ p q : G, M.op p q = c := ⟨M.op u v, const_of_41 M h41 u v⟩
  rw [hc u v] at hne ⊢
  have h := hz w
  rw [tB_apply M c z w hc] at h
  split_ifs at h with h1 h2
  · exact absurd h1 hne
  · exact Or.inl h2
  · exact Or.inr h

/-! ## The two-element carrier

On `{c, d}` the source magma is rigid -- `c` is fixed because it is `x ◇ x`, and `d` is then the
only other point -- so *every* operation is definable, not just the twenty-four. The two used here
are chosen by their value set: each returns `c` on one part of the square and `d` on the other, so
one formula shape covers both.

    twoA   x □ y := if x = c ∧ y = c then d else c
    twoX   x □ y := if x = y then c else d
-/

open scoped Classical in
/-- `x □ y := if x = c ∧ y = c then d else c`. -/
@[implicit_reducible]
noncomputable def twoA (c d : G) : Magma G := ⟨fun x y ↦ if x = c ∧ y = c then d else c⟩

open scoped Classical in
/-- `x □ y := if x = y then c else d`. -/
@[implicit_reducible]
noncomputable def twoX (c d : G) : Magma G := ⟨fun x y ↦ if x = y then c else d⟩

open scoped Classical in
theorem twoA_apply (c d a b : G) : (twoA c d).op a b = if a = c ∧ b = c then d else c := rfl

open scoped Classical in
theorem twoX_apply (c d a b : G) : (twoX c d).op a b = if a = b then c else d := rfl

/-- `z = x □ x` when `P`, and `z ≠ x □ x` otherwise: on a two-point carrier this pins `z`. -/
def pickFormula (G : Type) (P : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (P ⟹ Term.bdEqual (Term.var (Sum.inl none))
        (ap G (Term.var (Sum.inl (some 0))) (Term.var (Sum.inl (some 0))))) ⊓
    (∼P ⟹ ∼(Term.bdEqual (Term.var (Sum.inl none))
        (ap G (Term.var (Sum.inl (some 0))) (Term.var (Sum.inl (some 0))))))

theorem realize_pickFormula [N : Magma G]
    (P : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) (w : Option (Fin 2) → G) :
    (pickFormula G P).Realize w ↔
      ((P.Realize w → w none = N.op (w (some 0)) (w (some 0))) ∧
        (¬P.Realize w → w none ≠ N.op (w (some 0)) (w (some 0)))) := by
  simp only [pickFormula, ap, Formula.Realize, BoundedFormula.realize_inf,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    Term.realize_functions_apply₂, Term.realize_var, Sum.elim_inl, Magma.FOStructure_funMap',
    Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- On a two-point carrier a two-valued operation is definable: the formula says which of the two
values comes out, and `x ◇ x` names the other. -/
theorem definable_graph_pick (N : Magma G) [A : Magma G] (c d : G)
    (P : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (hcc : ∀ u v : G, A.op u v = c) (hd : d ≠ c) (htwo : ∀ w : G, w = c ∨ w = d)
    (hP : ∀ w : Option (Fin 2) → G, P.Realize w ↔ N.op (w (some 0)) (w (some 1)) = c) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage A.FOStructure _ N.Graph := by
  classical
  refine ⟨pickFormula G P, Set.ext fun w ↦ ?_⟩
  show N.op (w (some 0)) (w (some 1)) = w none ↔ _
  rw [Set.mem_setOf_eq, @realize_pickFormula _ A P w, hcc (w (some 0)) (w (some 0))]
  have hp := hP w
  constructor
  · intro he
    exact ⟨fun h ↦ he.symm.trans (hp.mp h), fun h he' ↦ h (hp.mpr (he.trans he'))⟩
  · rintro ⟨h1, h2⟩
    rcases htwo (N.op (w (some 0)) (w (some 1))) with h | h
    · exact h.trans (h1 (hp.mpr h)).symm
    · have hnp : ¬P.Realize w := fun hx ↦ hd (h.symm.trans (hp.mp hx))
      rcases htwo (w none) with h' | h'
      · exact absurd h' (h2 hnp)
      · exact h.trans h'.symm

/-- The reverse half on the two-point carrier: a `□`-term that is constantly `c`. -/
theorem definable_graph_back (N : Magma G) (q : QFOp)
    (hb : ∀ a b : G, (q.magma N).op a b = M.op a b) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage N.FOStructure _ M.Graph := by
  have h : q.magma N = M := by
    obtain ⟨f⟩ := M
    exact congrArg Magma.mk (funext fun a ↦ funext fun b ↦ hb a b)
  rw [← h]
  exact QFOp.definable_graph N q

/-- Glue for the two-point carrier. -/
theorem structuralOn_two {β : Type*} {L : Law.MagmaLaw β} (N : Magma G) [A : Magma G] (c d : G)
    (P : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) (q : QFOp)
    (hcc : ∀ u v : G, A.op u v = c) (hd : d ≠ c) (htwo : ∀ w : G, w = c ∨ w = d)
    (hP : ∀ w : Option (Fin 2) → G, P.Realize w ↔ N.op (w (some 0)) (w (some 1)) = c)
    (hb : ∀ a b : G, (q.magma N).op a b = A.op a b)
    (hL : @satisfies _ G N L) : L.StructuralOnMagma A :=
  ⟨N, hL, definable_graph_pick (A := A) N c d P hcc hd htwo hP, definable_graph_back A N q hb⟩

/-! ### The two concrete choices -/

/-- `¬(x = x ◇ x ∧ y = y ◇ y)`, the test that picks out `twoA`'s `c` values. -/
def notBoth (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  ∼(Term.bdEqual (Term.var (Sum.inl (some 0)))
        (ap G (Term.var (Sum.inl (some 0))) (Term.var (Sum.inl (some 0)))) ⊓
      Term.bdEqual (Term.var (Sum.inl (some 1)))
        (ap G (Term.var (Sum.inl (some 1))) (Term.var (Sum.inl (some 1)))))

/-- `x = y`, the test that picks out `twoX`'s `c` values. -/
def eqArgs (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  Term.bdEqual (Term.var (Sum.inl (some 0))) (Term.var (Sum.inl (some 1)))

theorem realize_notBoth [A : Magma G] (c : G) (hcc : ∀ u v : G, A.op u v = c)
    (w : Option (Fin 2) → G) :
    (notBoth G).Realize w ↔ ¬(w (some 0) = c ∧ w (some 1) = c) := by
  simp only [notBoth, ap, Formula.Realize, BoundedFormula.realize_not, BoundedFormula.realize_inf,
    BoundedFormula.realize_bdEqual, Term.realize_functions_apply₂, Term.realize_var,
    Sum.elim_inl, Magma.FOStructure_funMap', Magma.FinArityOp, Matrix.cons_val_zero,
    Matrix.cons_val_one, hcc]

theorem realize_eqArgs [A : Magma G] (w : Option (Fin 2) → G) :
    (eqArgs G).Realize w ↔ w (some 0) = w (some 1) := Iff.rfl

/-- `x ◇ y := x □ (x □ x)`, the term that reads `c` back off `twoA`. -/
def backA : QFOp := .leaf (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))

/-- `x ◇ y := x □ x`, the term that reads `c` back off `twoX`. -/
def backX : QFOp := .leaf (Lf 0 ⋆ Lf 0)

theorem twoA_back (c d : G) (hd : d ≠ c) (a b : G) :
    (backA.magma (twoA c d)).op a b = c := by
  classical
  show (twoA c d).op a ((twoA c d).op a a) = c
  simp only [twoA_apply]
  by_cases h : a = c
  · simp [h, hd]
  · simp [h]

theorem twoX_back (c d : G) (a b : G) : (backX.magma (twoX c d)).op a b = c := by
  classical
  show (twoX c d).op a a = c
  simp [twoX_apply]

theorem twoA_pick [A : Magma G] (c d : G) (hcc : ∀ u v : G, A.op u v = c) (hd : d ≠ c)
    (w : Option (Fin 2) → G) :
    (notBoth G).Realize w ↔ (twoA c d).op (w (some 0)) (w (some 1)) = c := by
  classical
  rw [realize_notBoth c hcc w, twoA_apply]
  split_ifs with h <;> simp_all

theorem twoX_pick [A : Magma G] (c d : G) (hd : d ≠ c) (w : Option (Fin 2) → G) :
    (eqArgs G).Realize w ↔ (twoX c d).op (w (some 0)) (w (some 1)) = c := by
  classical
  rw [realize_eqArgs (A := A) w, twoX_apply]
  split_ifs with h <;> simp_all

/-! ## The four entry points a target uses -/

theorem tC_rid (h41 : Equation41 G) (u v p : G) : (tC.magma M).op p (M.op u v) = p := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op u v, const_of_41 M h41 u v⟩
  rw [tC_apply M c p (M.op u v) hc, hc u v]
  simp

theorem tB_lzero (h41 : Equation41 G) (u v p : G) :
    (tB.magma M).op (M.op u v) p = M.op u v := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : G, ∀ a b : G, M.op a b = c := ⟨M.op u v, const_of_41 M h41 u v⟩
  rw [tB_apply M c (M.op u v) p hc, hc u v]
  simp

/-- The positive branch: `c` is `tC`'s only right identity, so it is `∅`-definable in `tC`. -/
theorem structuralOn_tC {β : Type*} {L : Law.MagmaLaw β} (h41 : Equation41 G)
    (h3 : ∀ z u v : G, (∀ p : G, (tC.magma M).op p z = p) → z = M.op u v)
    (hL : @satisfies _ G (tC.magma M) L) : L.StructuralOnMagma M :=
  structuralOn_rid M tC
    (fun z u v ↦ ⟨h3 z u v, fun hz ↦ hz ▸ fun p ↦ tC_rid M h41 u v p⟩) hL

/-- The positive branch: `c` is `tB`'s only left zero. -/
theorem structuralOn_tB {β : Type*} {L : Law.MagmaLaw β} (h41 : Equation41 G)
    (h3 : ∀ z u v : G, (∀ p : G, (tB.magma M).op z p = z) → z = M.op u v)
    (hL : @satisfies _ G (tB.magma M) L) : L.StructuralOnMagma M :=
  structuralOn_lzero M tB
    (fun z u v ↦ ⟨h3 z u v, fun hz ↦ hz ▸ fun p ↦ tB_lzero M h41 u v p⟩) hL

/-- The two-element branch, through `twoA`. -/
theorem structuralOn_twoA {β : Type*} {L : Law.MagmaLaw β} (c z : G)
    (hc : ∀ a b : G, M.op a b = c) (hzc : z ≠ c) (htwo : ∀ w : G, w = c ∨ w = z)
    (hL : @satisfies _ G (twoA c z) L) : L.StructuralOnMagma M :=
  structuralOn_two (A := M) (twoA c z) c z (notBoth G) backA hc hzc htwo
    (twoA_pick (A := M) c z hc hzc)
    (fun a b ↦ (twoA_back c z hzc a b).trans (hc a b).symm) hL

/-- The two-element branch, through `twoX`. -/
theorem structuralOn_twoX {β : Type*} {L : Law.MagmaLaw β} (c z : G)
    (hc : ∀ a b : G, M.op a b = c) (hzc : z ≠ c) (htwo : ∀ w : G, w = c ∨ w = z)
    (hL : @satisfies _ G (twoX c z) L) : L.StructuralOnMagma M :=
  structuralOn_two (A := M) (twoX c z) c z (eqArgs G) backX hc hzc htwo
    (twoX_pick (A := M) c z hzc)
    (fun a b ↦ (twoX_back c z a b).trans (hc a b).symm) hL

end Const41

import equational_theories.Definability.DiagRepair
import equational_theories.Definability.FiniteBridge

/-!
# Diagonal repair without a recovery word

`DiagRepair` recovers `x ◇ x` from `x □ y = if x = y then A x else x ◇ y` by exhibiting a `□`-word
that names the diagonal.  That is a *uniform* recovery, and it is far stronger than the definition
of `StructuralOnMagma` asks for: the recovery only has to be a first-order formula, and the formula
may depend on the magma.  Measured on the 597 sources whose diagonal is recoverable at all, only 47
have such a word, and none of the 123 conjectures those words generate is a theorem -- the words are
true on every finite model the screen can build and false in the free algebra.

On a **finite** carrier the recovery can be dropped altogether.  `Magma.definable_of_aut_invariant`
says `∅`-definable is the same as `Aut`-invariant there, so the reverse half of `StructuralOnMagma`
is not a formula problem but a group-theoretic one:

    `M.Graph` is `∅`-definable in `□`   ↔   `Aut(□) ⊆ Aut(◇)`.

Since `□` agrees with `◇` off the diagonal, `Aut(◇) ⊆ Aut(□)` is automatic, and the whole cell
reduces to the single implication

    σ bijective,  σ (a ◇ b) = σ a ◇ σ b for `a ≠ b`   ⊢   σ (x ◇ x) = σ x ◇ σ x,

a first-order consequence of the source law with no existential and no word to search for.  This is
what `DiagRepair`'s own docstring calls "a decidable screen but not a proof": it *is* a proof, as
soon as the carrier is finite, and it is one a superposition prover can find -- 29% of the sources
in the `Equation3` cone discharge it in under 40 s, against 0% for the word obligation.

The price is the `Finite` hypothesis, so this device fills `StructuralFromFin` cells only.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

attribute [local instance] instFOStructure

namespace AutBox

variable {G : Type}

/-- The reverse half of `StructuralOnMagma` for a companion that agrees with `◇` off the diagonal:
on a finite carrier it is enough that every off-diagonal automorphism respects the diagonal. -/
theorem definable_graph_aut [Finite G] (M : Magma G) (q : QFOp)
    (hoff : ∀ a b : G, a ≠ b → (q.magma M).op a b = M.op a b)
    (hdiag : ∀ σ : G → G, Function.Bijective σ →
      (∀ a b : G, a ≠ b → σ (M.op a b) = M.op (σ a) (σ b)) →
      ∀ x : G, σ (M.op x x) = M.op (σ x) (σ x)) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  refine Magma.definable_of_aut_invariant (q.magma M) M.Graph ?_
  intro σ hbij hhom v hv
  have hne : ∀ a b : G, a ≠ b → σ (M.op a b) = M.op (σ a) (σ b) := by
    intro a b hab
    have h1 := hhom a b
    rwa [hoff a b hab, hoff (σ a) (σ b) (fun hc ↦ hab (hbij.1 hc))] at h1
  have hall : ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b) := by
    intro a b
    rcases eq_or_ne a b with rfl | hab
    · exact hdiag σ hbij hne a
    · exact hne a b hab
  show M.op (σ (v (some 0))) (σ (v (some 1))) = σ (v none)
  rw [← hall]
  exact congrArg σ hv

/-- The device on one finite magma. -/
theorem structuralOnMagma_aut {β : Type*} {L : Law.MagmaLaw β} [Finite G]
    (M : Magma G) (q : QFOp)
    (hoff : ∀ a b : G, a ≠ b → (q.magma M).op a b = M.op a b)
    (hdiag : ∀ σ : G → G, Function.Bijective σ →
      (∀ a b : G, a ≠ b → σ (M.op a b) = M.op (σ a) (σ b)) →
      ∀ x : G, σ (M.op x x) = M.op (σ x) (σ x))
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_aut M q hoff hdiag⟩

/-- **The device.**  A companion that agrees with `◇` off the diagonal and satisfies the target,
plus the automorphism obligation, settle a whole `StructuralFromFin` cell.  No case split on the
size of the carrier is needed: unlike `DiagRepair.structuralFrom_neOf` there is no witness to
produce, so the subsingleton carrier is not special. -/
theorem structuralFromFin_autOf {β : Type*} {L L' : Law.MagmaLaw β} (q : QFOp)
    (hoff : ∀ {G : Type} (M : Magma G) (a b : G), a ≠ b → (q.magma M).op a b = M.op a b)
    (hdiag : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' → ∀ σ : G → G,
      Function.Bijective σ → (∀ a b : G, a ≠ b → σ (M.op a b) = M.op (σ a) (σ b)) →
      ∀ x : G, σ (M.op x x) = M.op (σ x) (σ x))
    (hL : ∀ {G : Type} (M : Magma G), satisfies G L' → @satisfies _ G (q.magma M) L) :
    L.StructuralFromFin L' :=
  fun M hM ↦ structuralOnMagma_aut M q (hoff M) (hdiag M hM) (hL M hM)

open QFOp in
/-- The `idem` companion `x □ y = if x = y then x else x ◇ y`, which satisfies `Equation3` for
free, so the target obligation is discharged once and for all. -/
theorem structuralFromFin_idem {L' : Law.MagmaLaw ℕ}
    (hdiag : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' → ∀ σ : G → G,
      Function.Bijective σ → (∀ a b : G, a ≠ b → σ (M.op a b) = M.op (σ a) (σ b)) →
      ∀ x : G, σ (M.op x x) = M.op (σ x) (σ x)) :
    Law3.StructuralFromFin L' :=
  structuralFromFin_autOf idem (fun M a b h ↦ idem_ne M a b h) (fun M hM ↦ hdiag M hM)
    (fun M _ ↦ (@Law3.models_iff _ (idem.magma M)).mpr fun x ↦ (idem_diag M x).symm)

/-! ## Cancellation from a solving word

A law of the shape `x = W(x, y⃗)` in which `x` occurs once says that a chain of translations
composes to the identity, so the innermost translation is injective and the outermost is
surjective.  On a finite carrier surjective is injective, so *either* end of the chain yields a
cancellation law -- and when the relevant sibling is a bare variable the cancellation holds at
every element, which is what the device needs. -/

/-- On a finite carrier a left-solvable translation is left cancellative. -/
theorem cancel_left_of_surj [Finite G] (M : Magma G) (u : G) (g : G → G)
    (h : ∀ z : G, M.op u (g z) = z) : ∀ v v' : G, M.op u v = M.op u v' → v = v' :=
  (Finite.injective_iff_surjective (f := fun w : G ↦ M.op u w)).mpr (fun z ↦ ⟨g z, h z⟩)

/-- On a finite carrier a right-solvable translation is right cancellative. -/
theorem cancel_right_of_surj [Finite G] (M : Magma G) (u : G) (g : G → G)
    (h : ∀ z : G, M.op (g z) u = z) : ∀ v v' : G, M.op v u = M.op v' u → v = v' :=
  (Finite.injective_iff_surjective (f := fun w : G ↦ M.op w u)).mpr (fun z ↦ ⟨g z, h z⟩)

/-! ## Rigidity: the obligation with the automorphism eliminated

The automorphism obligation is awkward for a prover -- `σ` and its inverse are extra function
symbols, and the off-diagonal homomorphism axiom is a two-literal clause, so every proof of it is
an AVATAR split with nothing for `superpose` to replay.  Pushing `M` forward along `σ` turns it
into a statement about two magmas and no maps at all:

    two models of the law on one carrier that agree off the diagonal agree on it

-- rigidity of the diagonal.  This is `diagdet.py`'s screen, and it is what makes the DiagRepair
companion faithful; the difference is that here the second model is required only to *exist*, so
the statement is first-order in a two-operation language, purely equational apart from the
disequality guard, and both `grind` and a `superpose` chain can reach it.

Rigidity is strictly stronger than the automorphism obligation -- it does not ask the two models to
be isomorphic -- so `structuralFromFin_cancel` is not subsumed by it.
-/

/-- **The rigid device.**  If two models of the source on one carrier that agree off the diagonal
agree on the diagonal, then every off-diagonal automorphism is an automorphism, and the `idem`
companion settles the whole `Equation3` cell. -/
theorem structuralFromFin_rigid {L' : Law.MagmaLaw ℕ}
    (hrig : ∀ {G : Type} [Finite G] (M N : Magma G), @satisfies _ G M L' → @satisfies _ G N L' →
      (∀ a b : G, a ≠ b → M.op a b = N.op a b) → ∀ x : G, M.op x x = N.op x x) :
    Law3.StructuralFromFin L' := by
  refine structuralFromFin_idem (fun {G} _ M hM σ hbij hne x ↦ ?_)
  classical
  let e : G ≃ G := Equiv.ofBijective σ hbij
  let N : Magma G := ⟨fun a b ↦ σ (M.op (e.symm a) (e.symm b))⟩
  have hea : ∀ a : G, e.symm (σ a) = a := fun a ↦ e.symm_apply_apply a
  have hmap : ∀ a b : G, σ (M.op a b) = N.op (σ a) (σ b) := by
    intro a b
    show σ (M.op a b) = σ (M.op (e.symm (σ a)) (e.symm (σ b)))
    rw [hea, hea]
  have hiso : @MagmaEquiv G G M N :=
    @MagmaEquiv.mk G G M N e hmap
  have hN : @satisfies _ G N L' := (@satisfies_equiv _ G G M N hiso L').mp hM
  have hoff : ∀ a b : G, a ≠ b → M.op a b = N.op a b := by
    intro a b hab
    have h1 : e.symm a ≠ e.symm b := fun h ↦ hab (by
      have h2 := congrArg e h
      rwa [e.apply_symm_apply, e.apply_symm_apply] at h2)
    have h2 := hne (e.symm a) (e.symm b) h1
    show M.op a b = σ (M.op (e.symm a) (e.symm b))
    rw [h2]
    show M.op a b = M.op (e (e.symm a)) (e (e.symm b))
    rw [e.apply_symm_apply, e.apply_symm_apply]
  have key := hrig M N hM hN hoff (σ x)
  have hNx : N.op (σ x) (σ x) = σ (M.op x x) := by
    show σ (M.op (e.symm (σ x)) (e.symm (σ x))) = σ (M.op x x)
    rw [hea]
  rw [key, hNx]

/-! ## The cancellative template

Left cancellativity is the whole device.  On a finite carrier a left-cancellative operation has
**rows that are permutations**, so `u ◇ u` is the single value the off-diagonal row `{u ◇ v : v ≠ u}`
fails to take -- the diagonal is not merely definable from the rest of the table, it is forced by
it.  Two models of the law that agree off the diagonal therefore agree everywhere, which is exactly
`structuralFromFin_rigid`'s hypothesis, and no property of the law beyond cancellation is used.

This replaces the earlier `Equation8`-plus-cancellation reading: `Equation8` was doing nothing that
the missing-value argument does not do on its own.
-/

/-- **The cancellative device, left form.**  If every finite model of the source is left
cancellative, the source is `Equation3`-structural on all of them. -/
theorem structuralFromFin_cancelLeft {L' : Law.MagmaLaw ℕ}
    (hc : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      ∀ u v v' : G, M.op u v = M.op u v' → v = v') :
    Law3.StructuralFromFin L' := by
  refine structuralFromFin_rigid (fun {G} _ M N hM hN hoff x ↦ ?_)
  have hsur : Function.Surjective (fun w : G ↦ M.op x w) :=
    Finite.injective_iff_surjective.mp (fun a b h ↦ hc M hM x a b h)
  obtain ⟨v, hv⟩ := hsur (N.op x x)
  replace hv : M.op x v = N.op x x := hv
  rcases eq_or_ne v x with rfl | hvx
  · exact hv
  · exact absurd (hc N hN x v x (by rw [← hoff x v (Ne.symm hvx), hv])) hvx

/-- **The cancellative device, right form.**  Columns instead of rows. -/
theorem structuralFromFin_cancelRight {L' : Law.MagmaLaw ℕ}
    (hc : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      ∀ u v v' : G, M.op v u = M.op v' u → v = v') :
    Law3.StructuralFromFin L' := by
  refine structuralFromFin_rigid (fun {G} _ M N hM hN hoff x ↦ ?_)
  have hsur : Function.Surjective (fun w : G ↦ M.op w x) :=
    Finite.injective_iff_surjective.mp (fun a b h ↦ hc M hM x a b h)
  obtain ⟨v, hv⟩ := hsur (N.op x x)
  replace hv : M.op v x = N.op x x := hv
  rcases eq_or_ne v x with rfl | hvx
  · exact hv
  · exact absurd (hc N hN x v x (by rw [← hoff v x hvx, hv])) hvx

/-! ## A general off-diagonal word

Nothing in the device forces the companion to agree with `◇` off the diagonal.  For any `◇`-word
`W(x, y)` the tree

    x □ y := if x = y then x else W(x, y)

is idempotent whatever `W` is, so the target half is free, and its graph is quantifier-free
definable, so the forward half is free too.  Only the reverse half moves: an automorphism of `□`
is a bijection respecting `W` off the diagonal, and the obligation is that such a bijection
respects `◇` everywhere.  That is a different first-order problem for every `W`, and the screen
finds sources that no plain box reaches but some word does.
-/

open QFOp FreeMagma in
/-- `x □ y := if x = y then x else W(x, y)`.  `W = x ◇ y` is `QFOp.idem`. -/
def boxOf (W : FreeMagma (Fin 2)) : QFOp :=
  .ite (Lf 0) (Lf 1) (.leaf (Lf 0)) (.leaf W)

open scoped Classical in
theorem boxOf_apply (W : FreeMagma (Fin 2)) (M : Magma G) (a b : G) :
    ((boxOf W).magma M).op a b = if a = b then a else @evalInMagma _ _ M ![a, b] W := by
  show @QFOp.eval _ M (boxOf W) ![a, b] = _
  simp only [boxOf, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem boxOf_ne (W : FreeMagma (Fin 2)) (M : Magma G) (a b : G) (h : a ≠ b) :
    ((boxOf W).magma M).op a b = @evalInMagma _ _ M ![a, b] W := by
  classical
  rw [boxOf_apply]
  exact if_neg h

theorem boxOf_diag (W : FreeMagma (Fin 2)) (M : Magma G) (a : G) :
    ((boxOf W).magma M).op a a = a := by
  classical
  rw [boxOf_apply]
  simp

/-- **The device with a general off-diagonal word.**  The inverse of `σ` is handed over as a
function with its two equations, and the off-diagonal hypothesis as a disjunction, because that is
the shape a saturation prover -- and `grind` -- can use: neither has to discharge a disequality
side condition to instantiate it. -/
theorem structuralFromFin_boxOf {L' : Law.MagmaLaw ℕ} (W : FreeMagma (Fin 2))
    (hdiag : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      ∀ σ τ : G → G, (∀ a : G, τ (σ a) = a) → (∀ a : G, σ (τ a) = a) →
      (∀ a b : G, a = b ∨
        σ (@evalInMagma _ _ M ![a, b] W) = @evalInMagma _ _ M ![σ a, σ b] W) →
      ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b)) :
    Law3.StructuralFromFin L' := by
  intro G _ M hM
  classical
  refine ⟨(boxOf W).magma M, (@Law3.models_iff _ ((boxOf W).magma M)).mpr
      (fun x ↦ (boxOf_diag W M x).symm), (boxOf W).definable_graph M, ?_⟩
  refine Magma.definable_of_aut_invariant ((boxOf W).magma M) M.Graph ?_
  intro σ hbij hhom v hv
  let e : G ≃ G := Equiv.ofBijective σ hbij
  have hall : ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b) := by
    refine hdiag M hM σ e.symm (fun a ↦ e.symm_apply_apply a) (fun a ↦ e.apply_symm_apply a) ?_
    intro a b
    rcases eq_or_ne a b with rfl | hab
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h1 := hhom a b
      rwa [boxOf_ne W M a b hab, boxOf_ne W M (σ a) (σ b) (fun hc ↦ hab (hbij.1 hc))] at h1
  show M.op (σ (v (some 0))) (σ (v (some 1))) = σ (v none)
  rw [← hall]
  exact congrArg σ hv

/-! ## A word the source law already makes idempotent

The diagonal patch is only there to force the target law.  When the source law proves `W(x, x) = x`
the word is idempotent on its own, and the companion can be the bare word

    x □ y := W(x, y)

with no case split.  Two things get cheaper.  The companion's graph is a single equation rather
than a decision tree, and -- what matters in practice -- the automorphism hypothesis is the
unconditional `σ (W a b) = W (σ a) (σ b)` instead of `boxOf`'s two-literal clause, so a saturation
prover has no split to make and the derivation replays as plain superposition.
-/

open QFOp in
/-- `x □ y := W(x, y)`, with no case split. -/
def wordOf (W : FreeMagma (Fin 2)) : QFOp := .leaf W

theorem wordOf_apply (W : FreeMagma (Fin 2)) (M : Magma G) (a b : G) :
    ((wordOf W).magma M).op a b = @evalInMagma _ _ M ![a, b] W := by
  show @QFOp.eval _ M (wordOf W) ![a, b] = _
  rfl

/-- **The device with an idempotent word.**  `hidem` is the target half, and it is a consequence of
the source law rather than a property of the companion's shape; `haut` is the reverse half. -/
theorem structuralFromFin_wordOf {L' : Law.MagmaLaw ℕ} (W : FreeMagma (Fin 2))
    (hidem : ∀ {G : Type} (M : Magma G), satisfies G L' →
      ∀ x : G, @evalInMagma _ _ M ![x, x] W = x)
    (haut : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      ∀ σ τ : G → G, (∀ a : G, τ (σ a) = a) → (∀ a : G, σ (τ a) = a) →
      (∀ a b : G, σ (@evalInMagma _ _ M ![a, b] W) = @evalInMagma _ _ M ![σ a, σ b] W) →
      ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b)) :
    Law3.StructuralFromFin L' := by
  intro G _ M hM
  classical
  refine ⟨(wordOf W).magma M, (@Law3.models_iff _ ((wordOf W).magma M)).mpr
      (fun x ↦ ((wordOf_apply W M x x).trans (hidem M hM x)).symm),
      (wordOf W).definable_graph M, ?_⟩
  refine Magma.definable_of_aut_invariant ((wordOf W).magma M) M.Graph ?_
  intro σ hbij hhom v hv
  let e : G ≃ G := Equiv.ofBijective σ hbij
  have hall : ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b) := by
    refine haut M hM σ e.symm (fun a ↦ e.symm_apply_apply a) (fun a ↦ e.apply_symm_apply a) ?_
    intro a b
    have h1 := hhom a b
    rwa [wordOf_apply W M a b, wordOf_apply W M (σ a) (σ b)] at h1
  show M.op (σ (v (some 0))) (σ (v (some 1))) = σ (v none)
  rw [← hall]
  exact congrArg σ hv

end AutBox

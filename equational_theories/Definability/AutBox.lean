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

/-! ## The diagonal obligation as a property of the source alone

`structuralFromFin_autOf`'s `hdiag` mentions neither the companion nor the target: it says only
that a bijection of a finite model of `L'` which respects `◇` off the diagonal respects it on.
Naming it makes it reusable.  Every companion agreeing with `◇` off the diagonal asks for the *same*
proof, so a source that has paid for `hdiag` once -- and 450 of them have, for `Equation3` -- gets
every other target the companion happens to satisfy for free. -/

/-- The diagonal obligation for a source: off-diagonal automorphisms of a finite model are
automorphisms.  The one hard half of every companion that agrees with `◇` off the diagonal. -/
abbrev DiagFix (L' : Law.MagmaLaw ℕ) : Prop :=
  ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' → ∀ σ : G → G,
    Function.Bijective σ → (∀ a b : G, a ≠ b → σ (M.op a b) = M.op (σ a) (σ b)) →
    ∀ x : G, σ (M.op x x) = M.op (σ x) (σ x)

/-- Rigidity of the diagonal: two finite models on one carrier agreeing off the diagonal agree on
it.  Strictly stronger than `DiagFix` -- it does not ask the two models to be isomorphic -- but
free of the maps, hence far easier for a prover. -/
abbrev DiagRigid (L' : Law.MagmaLaw ℕ) : Prop :=
  ∀ {G : Type} [Finite G] (M N : Magma G), @satisfies _ G M L' → @satisfies _ G N L' →
    (∀ a b : G, a ≠ b → M.op a b = N.op a b) → ∀ x : G, M.op x x = N.op x x

/-- Left cancellativity on every finite model. -/
abbrev CancelLeft (L' : Law.MagmaLaw ℕ) : Prop :=
  ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
    ∀ u v v' : G, M.op u v = M.op u v' → v = v'

/-- Right cancellativity on every finite model. -/
abbrev CancelRight (L' : Law.MagmaLaw ℕ) : Prop :=
  ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
    ∀ u v v' : G, M.op v u = M.op v' u → v = v'

/-- Identity, so that a proof script can `refine AutBox.diagFix_of (fun {G} _ M hM σ hb hne x ↦ ?_)`
and land on the unfolded goal. -/
theorem diagFix_of {L' : Law.MagmaLaw ℕ}
    (h : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' → ∀ σ : G → G,
      Function.Bijective σ → (∀ a b : G, a ≠ b → σ (M.op a b) = M.op (σ a) (σ b)) →
      ∀ x : G, σ (M.op x x) = M.op (σ x) (σ x)) : DiagFix L' := h

/-- `DiagFix` is antitone in the law: it quantifies over the models of `L'`, so a *stronger* law has
fewer of them and a correspondingly weaker obligation.  Every source that implies one of the sources
whose diagonal obligation is already proved inherits it for nothing. -/
theorem diagFix_mono {L L' : Law.MagmaLaw ℕ}
    (h : ∀ {G : Type} (M : Magma G), @satisfies _ G M L → @satisfies _ G M L') (hd : DiagFix L') :
    DiagFix L :=
  fun M hM ↦ hd M (h M hM)

open QFOp in
/-- The `idem` companion `x □ y = if x = y then x else x ◇ y`, which satisfies `Equation3` for
free, so the target obligation is discharged once and for all. -/
theorem structuralFromFin_idem {L' : Law.MagmaLaw ℕ} (hdiag : DiagFix L') :
    Law3.StructuralFromFin L' :=
  structuralFromFin_autOf idem (fun M a b h ↦ idem_ne M a b h) (fun M hM ↦ hdiag M hM)
    (fun M _ ↦ (@Law3.models_iff _ (idem.magma M)).mpr fun x ↦ (idem_diag M x).symm)

open QFOp in
/-- **The reuse device.**  Given the source's diagonal obligation -- which is target-free, so it may
have been proved for some entirely different cell -- any word `A` gives a companion
`x □ y = if x = y then A(x, y) else x ◇ y`, and every law that companion satisfies is another cell.

On the diagonal `y` *is* `x`, so the companion depends on `A` only through the unary term
`d(x) = A(x, x)`; those are few, and each gives the box a different equational theory. -/
theorem structuralFromFin_diagOf {L L' : Law.MagmaLaw ℕ} (A : FreeMagma (Fin 2))
    (hdiag : DiagFix L')
    (hsat : ∀ {G : Type} (M : Magma G), satisfies G L' →
      @satisfies _ G ((diagOf A).magma M) L) :
    L.StructuralFromFin L' :=
  structuralFromFin_autOf (diagOf A) (fun M a b h ↦ diagOf_ne A M a b h)
    (fun M hM ↦ hdiag M hM) hsat

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

/-- If two models of the source on one carrier that agree off the diagonal agree on the diagonal,
then every off-diagonal automorphism is an automorphism. -/
theorem diagFix_of_rigid {L' : Law.MagmaLaw ℕ} (hrig : DiagRigid L') : DiagFix L' := by
  refine diagFix_of (fun {G} _ M hM σ hbij hne x ↦ ?_)
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
cancellative, its diagonal is rigid. -/
theorem diagRigid_of_cancelLeft {L' : Law.MagmaLaw ℕ} (hc : CancelLeft L') : DiagRigid L' := by
  intro G _ M N hM hN hoff x
  have hsur : Function.Surjective (fun w : G ↦ M.op x w) :=
    Finite.injective_iff_surjective.mp (fun a b h ↦ hc M hM x a b h)
  obtain ⟨v, hv⟩ := hsur (N.op x x)
  replace hv : M.op x v = N.op x x := hv
  rcases eq_or_ne v x with rfl | hvx
  · exact hv
  · exact absurd (hc N hN x v x (by rw [← hoff x v (Ne.symm hvx), hv])) hvx

/-- **The cancellative device, right form.**  Columns instead of rows. -/
theorem diagRigid_of_cancelRight {L' : Law.MagmaLaw ℕ} (hc : CancelRight L') : DiagRigid L' := by
  intro G _ M N hM hN hoff x
  have hsur : Function.Surjective (fun w : G ↦ M.op w x) :=
    Finite.injective_iff_surjective.mp (fun a b h ↦ hc M hM x a b h)
  obtain ⟨v, hv⟩ := hsur (N.op x x)
  replace hv : M.op v x = N.op x x := hv
  rcases eq_or_ne v x with rfl | hvx
  · exact hv
  · exact absurd (hc N hN x v x (by rw [← hoff v x hvx, hv])) hvx

/-- Left cancellativity gives the diagonal obligation outright. -/
theorem diagFix_of_cancelLeft {L' : Law.MagmaLaw ℕ} (hc : CancelLeft L') : DiagFix L' :=
  diagFix_of_rigid (diagRigid_of_cancelLeft hc)

/-- Right cancellativity gives the diagonal obligation outright. -/
theorem diagFix_of_cancelRight {L' : Law.MagmaLaw ℕ} (hc : CancelRight L') : DiagFix L' :=
  diagFix_of_rigid (diagRigid_of_cancelRight hc)

/-! ### Front ends kept for the generated files

The 450 `Equation3` cells already in the library call these directly; they are now one composition
deep. -/

/-- **The rigid device.** -/
theorem structuralFromFin_rigid {L' : Law.MagmaLaw ℕ} (hrig : DiagRigid L') :
    Law3.StructuralFromFin L' :=
  structuralFromFin_idem (diagFix_of_rigid hrig)

/-- **The cancellative device, left form.** -/
theorem structuralFromFin_cancelLeft {L' : Law.MagmaLaw ℕ} (hc : CancelLeft L') :
    Law3.StructuralFromFin L' :=
  structuralFromFin_rigid (diagRigid_of_cancelLeft hc)

/-- **The cancellative device, right form.** -/
theorem structuralFromFin_cancelRight {L' : Law.MagmaLaw ℕ} (hc : CancelRight L') :
    Law3.StructuralFromFin L' :=
  structuralFromFin_rigid (diagRigid_of_cancelRight hc)

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

/-! ### Any target, not just `Equation3`

Nothing in the reverse half mentions the target.  `haut` below is verbatim the hypothesis of
`structuralFromFin_wordOf`, so one proof of it serves *every* law the companion happens to satisfy,
and the target only enters through `hsat` -- which is the plain equational question of whether the
source law forces `L` to hold of `W`.  That is the cheap half: it has no `σ` in it, and it is often
already in the implication graph.

So the unit of work is a pair `(source, W)` rather than a cell, and a source that discharges `haut`
for some `W` closes its whole `hsat`-satisfiable column at once. -/
theorem structuralFromFin_word {L L' : Law.MagmaLaw ℕ} (W : FreeMagma (Fin 2))
    (hsat : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      @satisfies _ G ((wordOf W).magma M) L)
    (haut : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      ∀ σ τ : G → G, (∀ a : G, τ (σ a) = a) → (∀ a : G, σ (τ a) = a) →
      (∀ a b : G, σ (@evalInMagma _ _ M ![a, b] W) = @evalInMagma _ _ M ![σ a, σ b] W) →
      ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b)) :
    L.StructuralFromFin L' := by
  intro G _ M hM
  classical
  refine ⟨(wordOf W).magma M, hsat M hM, (wordOf W).definable_graph M, ?_⟩
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

/-! ### Eliminating the map from the word obligation

`boxOf`'s hypothesis is the honest statement of what has to be proved, and Vampire proves it; but it
carries two function symbols `σ`, `τ` with `τ ∘ σ = σ ∘ τ = id`, and those give `grind` the
E-matching patterns `[σ #0]` and `[τ #0]`, which it uses to build unbounded towers `σ (σ (σ …))`
until the term-generation limit stops it.  Vampire's proofs of these goals introduce Skolem
functions and are not replayable either, so the obligation as stated is a dead end in Lean.

`DiagRigid` already shows the way out for the diagonal: transport the model along the bijection and
compare two models on one carrier, so that no map survives in the statement.  `WordRigid` is the
same trick for a general word.  Given `σ`, put `N x y := σ (M.op (τ x) (τ y))`; then `σ : M ≃◇ N`,
so `N` models `L'` too, and for `x ≠ y`

    W_N(x, y) = σ (W_M(τ x, τ y)) = W_M(σ (τ x), σ (τ y)) = W_M(x, y),

the middle step being exactly the off-diagonal hypothesis.  So `M` and `N` agree through `W` off the
diagonal, and rigidity forces `M.op = N.op`, which unfolds to `σ (M.op a b) = M.op (σ a) (σ b)`.

What is left is an equational problem in two magma operations with a single disequality guard -- no
maps, no towers -- which is the shape both `grind` and a superposition replay chain can reach. -/

/-- Rigidity through a word: two finite models of the source on one carrier whose `W`-values agree
off the diagonal are the same model.  `W = x ⋆ y` is `DiagRigid`. -/
abbrev WordRigid (W : FreeMagma (Fin 2)) (L' : Law.MagmaLaw ℕ) : Prop :=
  ∀ {G : Type} [Finite G] (M N : Magma G), @satisfies _ G M L' → @satisfies _ G N L' →
    (∀ a b : G, a ≠ b → @evalInMagma _ _ M ![a, b] W = @evalInMagma _ _ N ![a, b] W) →
    ∀ a b : G, M.op a b = N.op a b

/-- Identity, so that a proof script can `refine AutBox.wordRigid_of W (fun {G} _ M N hM hN hoff a b
↦ ?_)` and land on the unfolded goal. -/
theorem wordRigid_of {L' : Law.MagmaLaw ℕ} (W : FreeMagma (Fin 2))
    (h : ∀ {G : Type} [Finite G] (M N : Magma G), @satisfies _ G M L' → @satisfies _ G N L' →
      (∀ a b : G, a ≠ b → @evalInMagma _ _ M ![a, b] W = @evalInMagma _ _ N ![a, b] W) →
      ∀ a b : G, M.op a b = N.op a b) : WordRigid W L' := h

/-- Rigidity through `W` off the diagonal supplies the box device's obligation. -/
theorem diag_of_wordRigid {L' : Law.MagmaLaw ℕ} (W : FreeMagma (Fin 2)) (hrig : WordRigid W L') :
    ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      ∀ σ τ : G → G, (∀ a : G, τ (σ a) = a) → (∀ a : G, σ (τ a) = a) →
      (∀ a b : G, a = b ∨
        σ (@evalInMagma _ _ M ![a, b] W) = @evalInMagma _ _ M ![σ a, σ b] W) →
      ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b) := by
  intro G _ M hM σ τ h1 h2 hw a b
  classical
  let e : G ≃ G := ⟨σ, τ, h1, h2⟩
  let N : Magma G := ⟨fun x y ↦ σ (M.op (τ x) (τ y))⟩
  have hmap : ∀ x y : G, σ (M.op x y) = N.op (σ x) (σ y) := by
    intro x y
    show σ (M.op x y) = σ (M.op (τ (σ x)) (τ (σ y)))
    rw [h1, h1]
  let hiso : @MagmaEquiv G G M N := @MagmaEquiv.mk G G M N e hmap
  have hcoe : ⇑hiso = σ := rfl
  have hN : @satisfies _ G N L' := (@satisfies_equiv _ G G M N hiso L').mp hM
  have hoff : ∀ x y : G, x ≠ y →
      @evalInMagma _ _ M ![x, y] W = @evalInMagma _ _ N ![x, y] W := by
    intro x y hxy
    have hne : τ x ≠ τ y := fun h ↦ hxy (by rw [← h2 x, ← h2 y, h])
    have hpush := @evalInMagma_equiv _ G G M N ![τ x, τ y] hiso W
    have hfun : (⇑hiso ∘ ![τ x, τ y]) = (![x, y] : Fin 2 → G) := by
      rw [hcoe]
      funext i
      match i with
      | 0 => exact h2 x
      | 1 => exact h2 y
    rw [hfun] at hpush
    have hdiag := (hw (τ x) (τ y)).resolve_left hne
    have hsig : σ (@evalInMagma _ _ M ![τ x, τ y] W) = @evalInMagma _ _ M ![x, y] W := by
      rw [hdiag, h2, h2]
    rw [← hpush, hcoe, hsig]
  exact (hmap a b).trans (hrig M N hM hN hoff (σ a) (σ b)).symm

/-- **The word device with the automorphism eliminated**: rigidity through `W` gives `Equation3`
structurality over `L'` on finite magmas. -/
theorem structuralFromFin_wordRigid {L' : Law.MagmaLaw ℕ} (W : FreeMagma (Fin 2))
    (hrig : WordRigid W L') : Law3.StructuralFromFin L' :=
  structuralFromFin_boxOf W (diag_of_wordRigid W hrig)

/-- **The box device for a general target.**  `structuralFromFin_boxOf` is the case `L = Law3`,
where the companion's idempotence makes the target half free; for any other law the companion
happens to satisfy, the reverse half is the same obligation, unchanged. -/
theorem structuralFromFin_box {L L' : Law.MagmaLaw ℕ} (W : FreeMagma (Fin 2))
    (hsat : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      @satisfies _ G ((boxOf W).magma M) L)
    (hdiag : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      ∀ σ τ : G → G, (∀ a : G, τ (σ a) = a) → (∀ a : G, σ (τ a) = a) →
      (∀ a b : G, a = b ∨
        σ (@evalInMagma _ _ M ![a, b] W) = @evalInMagma _ _ M ![σ a, σ b] W) →
      ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b)) :
    L.StructuralFromFin L' := by
  intro G _ M hM
  classical
  refine ⟨(boxOf W).magma M, hsat M hM, (boxOf W).definable_graph M, ?_⟩
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

/-- **The box device, map-free.**  The companion is `x □ y = if x = y then x else W(x, y)`, which
is idempotent whatever `W` is, and the source half is rigidity through `W` *off the diagonal* --
weaker than `WordRigidFull`, since the two models are allowed to disagree on their diagonals. -/
theorem structuralFromFin_boxRigid {L L' : Law.MagmaLaw ℕ} (W : FreeMagma (Fin 2))
    (hsat : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      @satisfies _ G ((boxOf W).magma M) L)
    (hrig : WordRigid W L') : L.StructuralFromFin L' :=
  structuralFromFin_box W hsat (diag_of_wordRigid W hrig)

/-! ### The same elimination for a general target

`structuralFromFin_word`'s `haut` is the off-diagonal obligation without the disjunct, so the same
transport works and is even shorter: the two models agree through `W` on *every* pair, not just off
the diagonal, and no case split survives.  Since `haut` is the only half of the word device that
mentions a map, this makes the whole device reachable from a map-free, purely equational
hypothesis -- and `haut` was exactly the half Vampire could prove and Lean could not replay. -/

/-- Rigidity through a word, on the nose: two finite models of the source on one carrier with the
same `W`-table are the same model. -/
abbrev WordRigidFull (W : FreeMagma (Fin 2)) (L' : Law.MagmaLaw ℕ) : Prop :=
  ∀ {G : Type} [Finite G] (M N : Magma G), @satisfies _ G M L' → @satisfies _ G N L' →
    (∀ a b : G, @evalInMagma _ _ M ![a, b] W = @evalInMagma _ _ N ![a, b] W) →
    ∀ a b : G, M.op a b = N.op a b

/-- Identity, so that a proof script can `refine AutBox.wordRigidFull_of W (fun {G} _ M N hM hN
hall a b ↦ ?_)` and land on the unfolded goal. -/
theorem wordRigidFull_of {L' : Law.MagmaLaw ℕ} (W : FreeMagma (Fin 2))
    (h : ∀ {G : Type} [Finite G] (M N : Magma G), @satisfies _ G M L' → @satisfies _ G N L' →
      (∀ a b : G, @evalInMagma _ _ M ![a, b] W = @evalInMagma _ _ N ![a, b] W) →
      ∀ a b : G, M.op a b = N.op a b) : WordRigidFull W L' := h

/-- Rigidity through `W` supplies `structuralFromFin_word`'s automorphism half. -/
theorem aut_of_wordRigidFull {L' : Law.MagmaLaw ℕ} (W : FreeMagma (Fin 2))
    (hrig : WordRigidFull W L') :
    ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      ∀ σ τ : G → G, (∀ a : G, τ (σ a) = a) → (∀ a : G, σ (τ a) = a) →
      (∀ a b : G, σ (@evalInMagma _ _ M ![a, b] W) = @evalInMagma _ _ M ![σ a, σ b] W) →
      ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b) := by
  intro G _ M hM σ τ h1 h2 hw a b
  classical
  let e : G ≃ G := ⟨σ, τ, h1, h2⟩
  let N : Magma G := ⟨fun x y ↦ σ (M.op (τ x) (τ y))⟩
  have hmap : ∀ x y : G, σ (M.op x y) = N.op (σ x) (σ y) := by
    intro x y
    show σ (M.op x y) = σ (M.op (τ (σ x)) (τ (σ y)))
    rw [h1, h1]
  let hiso : @MagmaEquiv G G M N := @MagmaEquiv.mk G G M N e hmap
  have hcoe : ⇑hiso = σ := rfl
  have hN : @satisfies _ G N L' := (@satisfies_equiv _ G G M N hiso L').mp hM
  have hall : ∀ x y : G, @evalInMagma _ _ M ![x, y] W = @evalInMagma _ _ N ![x, y] W := by
    intro x y
    have hpush := @evalInMagma_equiv _ G G M N ![τ x, τ y] hiso W
    have hfun : (⇑hiso ∘ ![τ x, τ y]) = (![x, y] : Fin 2 → G) := by
      rw [hcoe]
      funext i
      match i with
      | 0 => exact h2 x
      | 1 => exact h2 y
    rw [hfun] at hpush
    have hsig : σ (@evalInMagma _ _ M ![τ x, τ y] W) = @evalInMagma _ _ M ![x, y] W := by
      rw [hw, h2, h2]
    rw [← hpush, hcoe, hsig]
  exact (hmap a b).trans (hrig M N hM hN hall (σ a) (σ b)).symm

/-- **The word device, map-free**: the target half is the plain equational question of whether the
companion `x □ y = W(x, y)` models `L`, and the source half is rigidity through `W`. -/
theorem structuralFromFin_wordRigidFull {L L' : Law.MagmaLaw ℕ} (W : FreeMagma (Fin 2))
    (hsat : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
      @satisfies _ G ((wordOf W).magma M) L)
    (hrig : WordRigidFull W L') : L.StructuralFromFin L' :=
  structuralFromFin_word W hsat (aut_of_wordRigidFull W hrig)

/-! ## A guarded off-diagonal companion

Every word companion has the same blind spot.  `boxOf W` throws the diagonal map `d x = x ◇ x`
away, so any bijection that respects `W` off the diagonal without commuting with `d` survives it,
and a screen over the banked models kills the whole word family for most sources.  The recipes that
do repair those magmas -- `defwork/idemrec.py` measures it -- are not words but *guarded* ones:
they overwrite the single off-diagonal cell the diagonal map points at, which no `FreeMagma` term
can express.

`QFOp` already nests, so the companion

    x □ y := if x = y then x else (if P(x, y) = Q(x, y) then A(x, y) else B(x, y))

costs nothing new on the definability side, and it is still idempotent, so the target half stays
free.  Only the automorphism obligation changes, and it changes into the shape a saturation prover
wants: the guarded value is a fresh function symbol `k` with its two defining clauses.
-/
open QFOp FreeMagma in
/-- `x □ y := if x = y then D(x, y) else (if P(x, y) = Q(x, y) then A(x, y) else B(x, y))`.  The
diagonal value is a parameter so that one proof of the automorphism obligation serves every target:
off the diagonal `D` does not appear, and off the diagonal is where the obligation lives. -/
def boxIteD (D P Q A B : FreeMagma (Fin 2)) : QFOp :=
  .ite (Lf 0) (Lf 1) (.leaf D) (.ite P Q (.leaf A) (.leaf B))

open QFOp FreeMagma in
/-- `x □ y := if x = y then x else (if P(x, y) = Q(x, y) then A(x, y) else B(x, y))`.  Taking
`P = Q` (or `A = B`) recovers `boxOf`. -/
abbrev boxIte (P Q A B : FreeMagma (Fin 2)) : QFOp := boxIteD (Lf 0) P Q A B

open scoped Classical in
theorem boxIteD_apply (D P Q A B : FreeMagma (Fin 2)) (M : Magma G) (a b : G) :
    ((boxIteD D P Q A B).magma M).op a b =
      if a = b then @evalInMagma _ _ M ![a, b] D else
        if @evalInMagma _ _ M ![a, b] P = @evalInMagma _ _ M ![a, b] Q then
          @evalInMagma _ _ M ![a, b] A else @evalInMagma _ _ M ![a, b] B := by
  show @QFOp.eval _ M (boxIteD D P Q A B) ![a, b] = _
  simp only [boxIteD, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem boxIteD_ne (D P Q A B : FreeMagma (Fin 2)) (M : Magma G) (a b : G) (h : a ≠ b) :
    ((boxIteD D P Q A B).magma M).op a b =
      if @evalInMagma _ _ M ![a, b] P = @evalInMagma _ _ M ![a, b] Q then
        @evalInMagma _ _ M ![a, b] A else @evalInMagma _ _ M ![a, b] B := by
  rw [boxIteD_apply]
  exact if_neg h

theorem boxIteD_diag (D P Q A B : FreeMagma (Fin 2)) (M : Magma G) (a : G) :
    ((boxIteD D P Q A B).magma M).op a a = @evalInMagma _ _ M ![a, a] D := by
  classical
  rw [boxIteD_apply]
  exact if_pos rfl

theorem boxIte_diag (P Q A B : FreeMagma (Fin 2)) (M : Magma G) (a : G) :
    ((boxIte P Q A B).magma M).op a a = a := by
  classical
  rw [show boxIte P Q A B = boxIteD (FreeMagma.Leaf 0) P Q A B from rfl, boxIteD_apply]
  simp [evalInMagma]

/-- The guarded companion's automorphism obligation, as a property of the source alone: it mentions
neither the diagonal value nor the target.  The guarded value is handed over as a function `k` with
its two defining clauses rather than as an `if`, so that the hypothesis is a set of Horn clauses --
that is what a superposition proof of it looks like, and what its replay can use without ever
splitting on the guard itself. -/
abbrev GuardFix (P Q A B : FreeMagma (Fin 2)) (L' : Law.MagmaLaw ℕ) : Prop :=
  ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
    ∀ σ τ : G → G, (∀ a : G, τ (σ a) = a) → (∀ a : G, σ (τ a) = a) →
    ∀ k : G → G → G,
      (∀ a b : G, @evalInMagma _ _ M ![a, b] P = @evalInMagma _ _ M ![a, b] Q →
        k a b = @evalInMagma _ _ M ![a, b] A) →
      (∀ a b : G, @evalInMagma _ _ M ![a, b] P ≠ @evalInMagma _ _ M ![a, b] Q →
        k a b = @evalInMagma _ _ M ![a, b] B) →
      (∀ a b : G, a = b ∨ σ (k a b) = k (σ a) (σ b)) →
    ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b)

/-- Identity, so that a script can `refine AutBox.guardFix_of P Q A B (fun {G} _ M hM σ τ h1 h2 k
hthen helse hoff a b ↦ ?_)` and land on the unfolded goal. -/
theorem guardFix_of (P Q A B : FreeMagma (Fin 2)) {L' : Law.MagmaLaw ℕ}
    (h : GuardFix P Q A B L') : GuardFix P Q A B L' := h

/-- `GuardFix` is antitone in the law, exactly as `DiagFix` is: a stronger source has fewer models
and inherits the obligation. -/
theorem guardFix_mono {L L' : Law.MagmaLaw ℕ} (P Q A B : FreeMagma (Fin 2))
    (h : ∀ {G : Type} (M : Magma G), @satisfies _ G M L → @satisfies _ G M L')
    (hg : GuardFix P Q A B L') : GuardFix P Q A B L :=
  fun M hM ↦ hg M (h M hM)

/-- **The guarded reuse device.**  Given the source's guarded obligation -- target-free, so it may
have been proved for some entirely different cell -- any diagonal word `D` gives a companion
`x □ y = if x = y then D(x, y) else k(x, y)`, and every law that companion satisfies is a cell. -/
theorem structuralFromFin_guardOf {L L' : Law.MagmaLaw ℕ} (D P Q A B : FreeMagma (Fin 2))
    (hg : GuardFix P Q A B L')
    (hsat : ∀ {G : Type} (M : Magma G), satisfies G L' →
      @satisfies _ G ((boxIteD D P Q A B).magma M) L) :
    L.StructuralFromFin L' := by
  intro G _ M hM
  classical
  refine ⟨(boxIteD D P Q A B).magma M, hsat M hM, (boxIteD D P Q A B).definable_graph M, ?_⟩
  refine Magma.definable_of_aut_invariant ((boxIteD D P Q A B).magma M) M.Graph ?_
  intro σ hbij hhom v hv
  let e : G ≃ G := Equiv.ofBijective σ hbij
  set k : G → G → G := fun a b ↦
    if @evalInMagma _ _ M ![a, b] P = @evalInMagma _ _ M ![a, b] Q then
      @evalInMagma _ _ M ![a, b] A else @evalInMagma _ _ M ![a, b] B with hk
  have hall : ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b) := by
    refine hg M hM σ e.symm (fun a ↦ e.symm_apply_apply a) (fun a ↦ e.apply_symm_apply a) k
      (fun a b h ↦ by rw [hk]; exact if_pos h) (fun a b h ↦ by rw [hk]; exact if_neg h) ?_
    intro a b
    rcases eq_or_ne a b with rfl | hab
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h1 := hhom a b
      rwa [boxIteD_ne D P Q A B M a b hab,
        boxIteD_ne D P Q A B M (σ a) (σ b) (fun hc ↦ hab (hbij.1 hc))] at h1
  show M.op (σ (v (some 0))) (σ (v (some 1))) = σ (v none)
  rw [← hall]
  exact congrArg σ hv

/-- The `Equation3` cell of the guarded device: the diagonal value is `x`, so the companion is
idempotent and the target half is free. -/
theorem structuralFromFin_boxIte {L' : Law.MagmaLaw ℕ} (P Q A B : FreeMagma (Fin 2))
    (hdiag : GuardFix P Q A B L') : Law3.StructuralFromFin L' :=
  structuralFromFin_guardOf (FreeMagma.Leaf 0) P Q A B hdiag
    (fun M _ ↦ (@Law3.models_iff _ ((boxIte P Q A B).magma M)).mpr
      (fun x ↦ (boxIte_diag P Q A B M x).symm))

/-- Identity, so that a script can `refine AutBox.boxIte_of P Q A B (fun {G} _ M hM σ τ h1 h2 k
hthen helse hoff a b ↦ ?_)` and land on the unfolded goal. -/
theorem boxIte_of {L' : Law.MagmaLaw ℕ} (P Q A B : FreeMagma (Fin 2))
    (hdiag : GuardFix P Q A B L') : Law3.StructuralFromFin L' :=
  structuralFromFin_boxIte P Q A B hdiag

end AutBox

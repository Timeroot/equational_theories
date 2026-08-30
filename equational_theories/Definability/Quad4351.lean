import equational_theories.Definability.Quad4374

/-!
# The square-column family: `T` shrunk to the squares

Equation `4351` is `x ◇ (y ◇ y) = z ◇ (y ◇ y)`: a product depends only on its right argument as
soon as that argument is a *square*. Writing `D := {y ◇ y : y}` and `S := G ∖ D`, a model is

* a set `G`, a subset `D`, a map `γ : D → D` and a completely free `h : G × S → G`,
* the operation `x ◇ y = γ y` for `y ∈ D` and `x ◇ y = h x y` for `y ∈ S`,

subject only to `γ(D) ∪ {h y y : y ∈ S} = D`, which is what makes `D` the square set.

`4374 ⊢ 4351` (put `z = y`), so this is the *weaker* law and its family is the larger one: seventy
eight open sources of the board imply `4351` up to duality, against `4374`'s thirty one.

Nothing in `Quad4374`'s reverse reads mentions the hub. They are stated for an abstract `t : G → Prop`
with `hin : ∀ a b, t b → M.op a b = M.op b b`, and that is exactly what `D` supplies here, so the
whole of `Quad4374.Reverse` is reused verbatim. Two things change, and both are improvements:

* `D` is named by `∃ p, p □ p = y`, and every read below keeps `□`'s diagonal equal to the source's,
  so the description is free — no `q_ty` lemma per operation, which is the bulk of what `gemit.py`
  has to prove for `4374`;
* `D` is *not* closed under `◇`, so an operation's values need not land in `D`. That is why the
  image-based `gker_image` has no counterpart here — and why it is not needed.

## Main results

* `Quad4351.DKer`: the structure of a model of `4351`.
* `Quad4351.dkernel`: reading it off the law.
* `Quad4351.structuralOn_selfGammaD` and friends: the four reads, with `D` named for free.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma Quad4274 Quad4374

universe u

variable {G : Type}

namespace Quad4351

/-- The `MagmaLanguage` structure of the ambient magma, as an instance. -/
local instance instFOStructure [M : Magma G] : MagmaLanguage.Structure G := M.FOStructure

/-! ### The structure of a model of `4351` -/

/-- The data a model of `4351` amounts to: the square set `d`, and the one fact that says a
product's left argument is forgotten as soon as its right argument is a square. -/
structure DKer (M : Magma G) where
  /-- the set of squares -/
  d : G → Prop
  /-- every square is in it -/
  dsq : ∀ a : G, d (M.op a a)
  /-- and conversely -/
  dex : ∀ y : G, d y → ∃ a : G, M.op a a = y
  /-- on the squares the left argument is forgotten, so the value is the right argument's square -/
  hin : ∀ a b : G, d b → M.op a b = M.op b b

/-- Reading the kernel off the law. -/
def dkernel (M : Magma G) (h : ∀ x y z : G, M.op x (M.op y y) = M.op z (M.op y y)) : DKer M where
  d y := ∃ a : G, M.op a a = y
  dsq a := ⟨a, rfl⟩
  dex _ hy := hy
  hin a b := by
    rintro ⟨p, rfl⟩
    exact h a p (M.op p p)

/-! ### Naming `D`

One binder is enough: `y` is a square exactly when `∃ p, p □ p = y`. -/

section Reverse

/-- the first argument, one binder in -/
private def x1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inl (some 0))
/-- the second argument, one binder in -/
private def y1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inl (some 1))
/-- the only binder -/
private def p1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inr 0)

/-- `y` is a square. -/
def sqY : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (Term.bdEqual (ap G p1 p1) y1)

theorem realize_sqY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (sqY (G := G)) v xs ↔ ∃ p : G, P.op p p = v (some 1) := by
  simp only [sqY, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual,
    p1, y1, realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, h⟩; exact ⟨_, h⟩
  · rintro ⟨p, h⟩; exact ⟨p, by simpa [Fin.snoc] using h⟩

/-- `x` is a square: the same description, read in the first argument. -/
def sqX : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (Term.bdEqual (ap G p1 p1) x1)

theorem realize_sqX [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (sqX (G := G)) v xs ↔ ∃ p : G, P.op p p = v (some 0) := by
  simp only [sqX, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual,
    p1, x1, realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, h⟩; exact ⟨_, h⟩
  · rintro ⟨p, h⟩; exact ⟨p, by simpa [Fin.snoc] using h⟩

end Reverse

/-! ### Packaging

Every read below is the identity on the diagonal: on `D` because `γ y = y ◇ y` is what the read
keeps there, and off `D` because the off-`D` clause copies the source cell and at `x = y` that cell
*is* the diagonal one. So `∃ p, p □ p = y` cuts out `D` in the new magma with no work per
operation, which is the whole point of the hub. -/

section Ops

variable (M : Magma G) (K : DKer M)

include K in
/-- `D` is the square set of any operation that keeps the source's diagonal. -/
theorem dker_sq {P : Magma G} (hd : ∀ y : G, P.op y y = M.op y y) (y : G) :
    (∃ p : G, P.op p p = y) ↔ K.d y := by
  constructor
  · rintro ⟨p, rfl⟩
    exact (hd p) ▸ K.dsq p
  · rintro hy
    obtain ⟨p, hp⟩ := K.dex y hy
    exact ⟨p, (hd p).trans hp⟩

include K in
/-- The source itself on the columns of `S`. -/
theorem structuralOn_selfGammaD (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hg : ∀ y : G, K.d y → (q.magma M).op y y = M.op y y)
    (hout : ∀ x y : G, ¬ K.d y → (q.magma M).op x y = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have hd : ∀ y : G, (q.magma M).op y y = M.op y y :=
    fun y ↦ if hy : K.d y then hg y hy else hout y y hy
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_selfGammaG sqY
      (fun v xs ↦ (realize_sqY (P := q.magma M) v xs).trans (dker_sq M K hd _)) K.hin hg hout⟩

include K in
/-- The source transposed on the columns of `S`. -/
theorem structuralOn_swapGammaD (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hg : ∀ y : G, K.d y → (q.magma M).op y y = M.op y y)
    (hout : ∀ x y : G, ¬ K.d y → (q.magma M).op y x = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have hd : ∀ y : G, (q.magma M).op y y = M.op y y :=
    fun y ↦ if hy : K.d y then hg y hy else hout y y hy
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_swapGammaG sqY
      (fun v xs ↦ (realize_sqY (P := q.magma M) v xs).trans (dker_sq M K hd _)) K.hin hg hout⟩

include K in
/-- Transposed on `D × S`, direct on `S × S`. -/
theorem structuralOn_splitGammaD (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hg : ∀ y : G, K.d y → (q.magma M).op y y = M.op y y)
    (hts : ∀ x y : G, K.d x → ¬ K.d y → (q.magma M).op y x = M.op x y)
    (hss : ∀ x y : G, ¬ K.d x → ¬ K.d y → (q.magma M).op x y = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have hd : ∀ y : G, (q.magma M).op y y = M.op y y :=
    fun y ↦ if hy : K.d y then hg y hy else hss y y hy hy
  have hsq := dker_sq M K hd
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_splitGammaG sqY sqX
      (fun v xs ↦ (realize_sqY (P := q.magma M) v xs).trans (hsq _))
      (fun v xs ↦ (realize_sqX (P := q.magma M) v xs).trans (hsq _)) K.hin hg hts hss⟩

include K in
/-- Direct on `D × S`, transposed on `S × S`. -/
theorem structuralOn_splitGammaD' (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hg : ∀ y : G, K.d y → (q.magma M).op y y = M.op y y)
    (hts : ∀ x y : G, K.d x → ¬ K.d y → (q.magma M).op x y = M.op x y)
    (hss : ∀ x y : G, ¬ K.d x → ¬ K.d y → (q.magma M).op y x = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have hd : ∀ y : G, (q.magma M).op y y = M.op y y :=
    fun y ↦ if hy : K.d y then hg y hy else hss y y hy hy
  have hsq := dker_sq M K hd
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_splitGammaG' sqY sqX
      (fun v xs ↦ (realize_sqY (P := q.magma M) v xs).trans (hsq _))
      (fun v xs ↦ (realize_sqX (P := q.magma M) v xs).trans (hsq _)) K.hin hg hts hss⟩

/-- `D` is the square set, as a rewrite for the `apply` lemmas. -/
theorem dsqex (w : G) : (∃ p : G, M.op p p = w) ↔ K.d w :=
  ⟨fun ⟨p, e⟩ ↦ e ▸ K.dsq p, K.dex w⟩

end Ops

end Quad4351

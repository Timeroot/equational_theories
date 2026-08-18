import equational_theories.Definability.Basic

/-!
# The finite-magma flavour of the definability relations

`Definability/Basic.lean` quantifies each of the four relations over every magma. Each also has a
finite flavour, got by restricting to finite carriers, and the board tracks both columns.

Until now only the negative side of the finite column was expressible: a refutation whose witness
magma is finite refutes the finite flavour, and that is read off the carrier of the witness. The
positive side had no statement at all, so a definition that exists on every *finite* model of the
source but not on every model could not be recorded.

Such definitions are real. The standard source of them is that on a finite carrier a surjective map
is injective, so if a law `x = w(x, y, …)` presents the identity as a composite `g_k ∘ ⋯ ∘ g_1` of
unary polynomials, every `g_i` is a bijection and every cyclic rotation of the composite is also the
identity. Those rotations are fresh equations, valid in exactly the magmas this file quantifies
over, and terms built with them define laws that no uniform term reaches.

The four relations here stand in the same hierarchy as their unrestricted counterparts, and each is
implied by it -- a definition that works for every magma in particular works for every finite one.

Note the argument order inherited from `Basic.lean`: `L.TermDefinableFromFin L'` says that `L` is
term-definable on every finite magma satisfying `L'`.
-/

namespace Law.MagmaLaw

variable {β : Type*} {L L' L₁ L₂ L₃ : Law.MagmaLaw β}

/-- `L` is definable from `L'` over finite magmas: `L` is `DefinableOnMagma` on every finite magma
satisfying `L'`. -/
def DefinableFromFin (L L' : Law.MagmaLaw β) : Prop :=
  ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' → DefinableOnMagma L M

/-- `L` is term-definable from `L'` over finite magmas: `L` is `TermDefinableOnMagma` on every
finite magma satisfying `L'`. -/
def TermDefinableFromFin (L L' : Law.MagmaLaw β) : Prop :=
  ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' → TermDefinableOnMagma L M

/-- `L` is structural from `L'` over finite magmas. -/
def StructuralFromFin (L L' : Law.MagmaLaw β) : Prop :=
  ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' → StructuralOnMagma L M

/-- `L` is term-structural from `L'` over finite magmas. -/
def TermStructuralFromFin (L L' : Law.MagmaLaw β) : Prop :=
  ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' → TermStructuralOnMagma L M

section hierarchy
open FirstOrder FirstOrder.Language

/-! ### Each relation is implied by its unrestricted counterpart -/

theorem definableFin_of_definable (h : L.DefinableFrom L') : L.DefinableFromFin L' :=
  fun M hGL ↦ h M hGL

theorem termDefinableFin_of_termDefinable (h : L.TermDefinableFrom L') :
    L.TermDefinableFromFin L' :=
  fun M hGL ↦ h M hGL

theorem structuralFin_of_structural (h : L.StructuralFrom L') : L.StructuralFromFin L' :=
  fun M hGL ↦ h M hGL

theorem termStructuralFin_of_termStructural (h : L.TermStructuralFrom L') :
    L.TermStructuralFromFin L' :=
  fun M hGL ↦ h M hGL

/-! ### The same hierarchy as in `Basic.lean`, one carrier at a time -/

theorem structuralFin_of_termStructuralFin (h : L'.TermStructuralFromFin L) :
    L'.StructuralFromFin L := by
  intro G _ M hGL
  obtain ⟨M', h2, h3, h4⟩ := h M hGL
  use M', h2
  constructor
  · let _ := M.FOStructure; exact h3.definable_tupleGraph
  · let _ := M'.FOStructure; exact h4.definable_tupleGraph

theorem termDefinableFin_of_termStructuralFin (h : L'.TermStructuralFromFin L) :
    L'.TermDefinableFromFin L := by
  intro G _ M hGL
  obtain ⟨M', h2, _, _⟩ := h M hGL
  use M', h2

theorem definableFin_of_structuralFin (h : L'.StructuralFromFin L) : L'.DefinableFromFin L := by
  intro G _ M hGL
  obtain ⟨M', h2, _, _⟩ := h M hGL
  use M', h2

theorem definableFin_of_termDefinableFin (h : L'.TermDefinableFromFin L) :
    L'.DefinableFromFin L := by
  intro G _ M hGL
  obtain ⟨M', h2, h3⟩ := h M hGL
  exact ⟨M', h2, let _ := M.FOStructure; h3.definable_tupleGraph⟩

end hierarchy

section preorder
open FirstOrder FirstOrder.Language

/-! ### Each finite relation is again a preorder

Transitivity reuses the fixed-carrier lemmas of `Basic.lean` verbatim: the intermediate magma lives
on the same carrier, so it is finite whenever the original is. -/

@[simp]
theorem TermStructuralFin.refl : L₁.TermStructuralFromFin L₁ :=
  termStructuralFin_of_termStructural TermStructural.refl

@[simp]
theorem TermDefinableFin.refl : L₁.TermDefinableFromFin L₁ :=
  termDefinableFin_of_termDefinable TermDefinable.refl

@[simp]
theorem StructuralFin.refl : L₁.StructuralFromFin L₁ :=
  structuralFin_of_structural Structural.refl

@[simp]
theorem DefinableFin.refl : L₁.DefinableFromFin L₁ :=
  definableFin_of_definable Definable.refl

theorem TermDefinableFin.trans (h₁₂ : L₂.TermDefinableFromFin L₁)
    (h₂₃ : L₃.TermDefinableFromFin L₂) : L₃.TermDefinableFromFin L₁ := by
  intro G _ M hGL₁
  obtain ⟨M₂, hGL₂, hA⟩ := h₁₂ M hGL₁
  obtain ⟨M₃, hGL₃, hB⟩ := h₂₃ M₂ hGL₂
  exact ⟨M₃, hGL₃, TermDefinable.trans_aux hA hB⟩

theorem TermStructuralFin.trans (h₁₂ : L₂.TermStructuralFromFin L₁)
    (h₂₃ : L₃.TermStructuralFromFin L₂) : L₃.TermStructuralFromFin L₁ := by
  intro G _ M hGL₁
  obtain ⟨M₂, hGL₂, hA1, hA2⟩ := h₁₂ M hGL₁
  obtain ⟨M₃, hGL₃, hB1, hB2⟩ := h₂₃ M₂ hGL₂
  exact ⟨M₃, hGL₃, TermDefinable.trans_aux hA1 hB1, TermDefinable.trans_aux hB2 hA2⟩

theorem DefinableFin.trans (h₁₂ : L₂.DefinableFromFin L₁) (h₂₃ : L₃.DefinableFromFin L₂) :
    L₃.DefinableFromFin L₁ := by
  intro G _ M hGL₁
  obtain ⟨M₂, hGL₂, hA⟩ := h₁₂ M hGL₁
  obtain ⟨M₃, hGL₃, hB⟩ := h₂₃ M₂ hGL₂
  exact ⟨M₃, hGL₃, Definable.trans_aux hA hB⟩

theorem StructuralFin.trans (h₁₂ : L₂.StructuralFromFin L₁) (h₂₃ : L₃.StructuralFromFin L₂) :
    L₃.StructuralFromFin L₁ := by
  intro G _ M hGL₁
  obtain ⟨M₂, hGL₂, hA1, hA2⟩ := h₁₂ M hGL₁
  obtain ⟨M₃, hGL₃, hB1, hB2⟩ := h₂₃ M₂ hGL₂
  exact ⟨M₃, hGL₃, Definable.trans_aux hA1 hB1, Definable.trans_aux hB2 hA2⟩

end preorder

end Law.MagmaLaw

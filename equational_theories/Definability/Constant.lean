import equational_theories.Definability.Clone
import equational_theories.Equations.All

/-!
# The constant magma

The poorest clone there is. If `x ⋄ y = a` for a fixed `a`, then every composite `M.op f g` is
again the constant `a`, so the clone closes after one step: it is exactly `{π₁, π₂, const a}`.
Nothing in the bank of magmas harvested from the ETP refutation files is this poor — the smallest
clone there has three elements too, but it belongs to the two-element semilattice, whose third
member `x ⊓ y` is not constant.

That makes the constant magma the sharpest available certificate against **rigid** targets, the
laws with a bare variable on one side. A rigid law asks the new operation to recover `x` from a
word in `x` and `y`, which a constant operation obviously cannot do, and which the projections
cannot do either unless the word happens to collapse to the right variable. `Law1519`
`x = (y ⋄ y) ⋄ (x ⋄ (y ⋄ y))` defeats all three at once.

The sources below are precisely the laws with a compound term on both sides, which the constant
magma therefore models. Their duals, against the dual target `Law2128`, follow by symmetry.
-/

open Law Law.MagmaLaw

namespace Magma

variable {G : Type}

/-- The constant magma `x ⋄ y = a`. -/
@[implicit_reducible]
def const (a : G) : Magma G := ⟨fun _ _ ↦ a⟩

/-- The three operations term-definable from `Magma.const a`: the two projections and `const a`
itself. -/
@[implicit_reducible]
def constClone (a : G) : Fin 3 → Magma G := ![⟨fun x _ ↦ x⟩, ⟨fun _ y ↦ y⟩, const a]

/-- Every composite of two members lands on `const a`, so the family is closed. -/
theorem const_isCloneFamily (a : G) :
    (const a).IsCloneFamily (constClone a) 0 1 (fun _ _ ↦ 2) where
  fst _ _ := rfl
  snd _ _ := rfl
  comp _ _ _ _ := rfl

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- **Constant-magma obstruction.** If the constant magma on `G` models `L'`, and `L` holds for
none of the first projection, the second projection and the constant operation, then `L` is not
term-definable from `L'`. -/
theorem not_termDefinableFrom_of_const {G : Type} (a : G) (hM : @satisfies _ G (Magma.const a) L')
    (h₁ : ¬ @satisfies _ G ⟨fun x _ ↦ x⟩ L) (h₂ : ¬ @satisfies _ G ⟨fun _ y ↦ y⟩ L)
    (h₃ : ¬ @satisfies _ G (Magma.const a) L) :
    ¬ L.TermDefinableFrom L' :=
  not_termDefinableFrom_of_clone _ hM (Magma.const_isCloneFamily a) fun i ↦ by
    fin_cases i <;> assumption

end Law.MagmaLaw

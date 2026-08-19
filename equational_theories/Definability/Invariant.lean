import equational_theories.Definability.Clone

/-!
# The clone obstruction for infinite magmas

`Definability/Clone.lean` refutes term-definability by *listing* the clone of a magma: the
certificate is a finite family `C : Fin k → Magma G` closed under composition, and every hypothesis
is then decidable. That is exactly the right shape when `G` is small, and useless when it is not.

Many of the strongest certificates are infinite. In `(ℤ, x ◇ y = a * x + b * y)`, for instance,
every binary term is `α * x + β * y` for integers `α, β` with `α + β ≡ 1 (mod a + b - 1)` — an
infinite clone, described exactly by a *predicate* rather than by a list. This file generalizes
`Magma.IsCloneFamily` to that setting: `Magma.IsCloneInvariant M P` says that `P` holds of the two
projections and is preserved by composition with `M.op`, i.e. that `P` cuts out a superset of the
clone of `M`. Refuting the target for every operation satisfying `P` then refutes term-definability.

Nothing here is decidable, by design: an invariant certificate is discharged by algebra. The
finite case remains available and is strictly faster when it applies —
`Magma.IsCloneFamily.isCloneInvariant` records that it is a special case.

As with the finite clone obstruction this refutes term-definability only, and — since the model may
be infinite — only over all magmas, not over the finite ones.
-/

open FirstOrder Law Law.MagmaLaw

namespace Magma

variable {G : Type} {M : Magma G}

/-- `M.IsCloneInvariant P` says that the predicate `P` holds of the two projections and is closed
under composition with `M.op`. Such a `P` holds of every operation term-definable from `M`. -/
structure IsCloneInvariant (M : Magma G) (P : (G → G → G) → Prop) : Prop where
  /-- `P` holds of the first projection. -/
  fst : P fun x _ ↦ x
  /-- `P` holds of the second projection. -/
  snd : P fun _ y ↦ y
  /-- `P` is preserved by composition along `M.op`. -/
  comp : ∀ f g, P f → P g → P fun x y ↦ M.op (f x y) (g x y)

/-- Every two-variable term of `M` satisfies a clone invariant of `M`: the projections are the
variables and `IsCloneInvariant.comp` is the induction step. -/
theorem IsCloneInvariant.realize {P : (G → G → G) → Prop} (hP : M.IsCloneInvariant P)
    (t : MagmaLanguage.Term (Fin 2)) :
    P fun x y ↦ @Language.Term.realize _ _ M.FOStructure _ ![x, y] t := by
  induction t with
  | var v =>
    fin_cases v
    · exact hP.fst
    · exact hP.snd
  | func F ts ih =>
    obtain rfl := MagmaLanguage.arity_eq_two F
    refine cast (congrArg P (funext fun x ↦ funext fun y ↦ ?_)) (hP.comp _ _ (ih 0) (ih 1))
    simp [Language.Term.realize, Magma.FinArityOp]

/-- A clone invariant holds of any operation term-definable from `M`. -/
theorem IsCloneInvariant.of_termDefinable {P : (G → G → G) → Prop} (hP : M.IsCloneInvariant P)
    {M' : Magma G} (h : @Set.TermDefinable G ∅ MagmaLanguage M.FOStructure (Fin 2) M'.FinArityOp) :
    P M'.op := by
  letI := M.FOStructure
  rw [Set.termDefinable_empty_iff] at h
  obtain ⟨t, ht⟩ := h
  obtain ⟨op⟩ := M'
  have he : (fun x y ↦ @Language.Term.realize _ _ M.FOStructure _ ![x, y] t) = op := by
    funext x y
    exact (congrFun ht ![x, y]).symm
  exact he ▸ hP.realize t

/-- A finite clone family is a clone invariant: take `P` to be membership in the family. -/
theorem IsCloneFamily.isCloneInvariant {ι : Type*} {C : ι → Magma G} {i₁ i₂ : ι}
    {c : ι → ι → ι} (hC : M.IsCloneFamily C i₁ i₂ c) :
    M.IsCloneInvariant fun f ↦ ∃ i, (C i).op = f where
  fst := ⟨i₁, funext fun x ↦ funext fun y ↦ hC.fst x y⟩
  snd := ⟨i₂, funext fun x ↦ funext fun y ↦ hC.snd x y⟩
  comp := fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ ↦
    ⟨c i j, by funext x y; rw [hC.comp, hi, hj]⟩

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- **Invariant clone obstruction.** If `L'` has a model `M` admitting a clone invariant `P`, and
no operation satisfying `P` satisfies `L`, then `L` is not term-definable from `L'`.

This is `not_termDefinableFrom_of_clone` with the finite family replaced by a predicate, which is
what infinite models need. -/
theorem not_termDefinableFrom_of_invariant {G : Type} (M : Magma G) (hM : @satisfies _ G M L')
    {P : (G → G → G) → Prop} (hP : M.IsCloneInvariant P)
    (hL : ∀ op, P op → ¬ @satisfies _ G (Magma.mk op) L) :
    ¬ L.TermDefinableFrom L' := fun h ↦
  let ⟨M', hM', hd⟩ := h M hM
  hL M'.op (hP.of_termDefinable hd) hM'

end Law.MagmaLaw

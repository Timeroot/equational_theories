import equational_theories.DecideBang
import equational_theories.Definability.Negative

/-!
# The clone obstruction

`Definability/Negative.lean` refutes definability by *symmetry*: the new operation inherits every
endomorphism of the old one. That argument is often much weaker than the truth, because it only
sees the operations preserved by `M.endos`, whereas the operations term-definable from `M` are
exactly the ones in the **clone** of `M` — the closure of the two projections under composition
with `M.op`. When the clone happens to be small, listing it outright is both a stronger and a
cheaper certificate: `L` is term-definable from `L'` only if *some member of the clone* satisfies
`L`, and for a clone of a dozen operations that is a finite check.

`Law.MagmaLaw.not_termDefinableFrom_of_clone` is the obstruction. Its hypotheses are stated over
raw data — the list of operations, the indices of the two projections, and the composition table —
so that on `Fin n` every one of them is `Decidable` and discharged by `decide`.

Unlike the symmetry certificates this refutes term-definability only. A first-order definable
operation need not lie in the clone: it need not even be preserved by the non-invertible
endomorphisms, let alone be a term.
-/

open FirstOrder Law Law.MagmaLaw

namespace Magma

variable {G : Type} {M : Magma G} {ι : Type*} {C : ι → Magma G}

/-- `M.IsCloneFamily C i₁ i₂ c` says that the operations `C` contain the two projections, at the
indices `i₁` and `i₂`, and are closed under composition with `M.op`, with `c` recording where each
composite lands. Any such family contains every operation term-definable from `M`.

The index type `ι` is arbitrary. Nothing in the proofs below needs it to be finite, or even to have
decidable equality: `i₁`, `i₂` and `c` are used only as data. Taking `ι = Fin k` gives the listed
certificates of `Definability/CloneCerts.lean`; taking `ι` to be a function type gives the
translation-invariant families of `Definability/Regular.lean`, which are far too large to list. -/
structure IsCloneFamily (M : Magma G) (C : ι → Magma G) (i₁ i₂ : ι)
    (c : ι → ι → ι) : Prop where
  /-- `C i₁` is the first projection. -/
  fst : ∀ x y, (C i₁).op x y = x
  /-- `C i₂` is the second projection. -/
  snd : ∀ x y, (C i₂).op x y = y
  /-- `C (c i j)` is the composite of `C i` and `C j` along `M.op`. -/
  comp : ∀ i j x y, (C (c i j)).op x y = M.op ((C i).op x y) ((C j).op x y)

/-- Every two-variable term of `M` is realized by a member of a clone family: the projections are
the variables and `IsCloneFamily.comp` is the induction step. -/
theorem IsCloneFamily.exists_op_eq_realize {i₁ i₂ c} (hC : M.IsCloneFamily C i₁ i₂ c)
    (t : MagmaLanguage.Term (Fin 2)) :
    ∃ i, (C i).op = fun x y ↦ @Language.Term.realize _ _ M.FOStructure _ ![x, y] t := by
  induction t with
  | var v =>
    fin_cases v
    · exact ⟨i₁, funext fun x ↦ funext fun y ↦ hC.fst x y⟩
    · exact ⟨i₂, funext fun x ↦ funext fun y ↦ hC.snd x y⟩
  | func F ts ih =>
    obtain rfl := MagmaLanguage.arity_eq_two F
    obtain ⟨a, ha⟩ := ih 0
    obtain ⟨b, hb⟩ := ih 1
    refine ⟨c a b, ?_⟩
    funext x y
    rw [hC.comp, congrFun (congrFun ha x) y, congrFun (congrFun hb x) y]
    simp [Language.Term.realize, Magma.FinArityOp]

/-- The clone family contains any operation term-definable from `M`. -/
theorem IsCloneFamily.exists_eq {i₁ i₂ c} (hC : M.IsCloneFamily C i₁ i₂ c) {M' : Magma G}
    (h : @Set.TermDefinable G ∅ MagmaLanguage M.FOStructure (Fin 2) M'.FinArityOp) :
    ∃ i, C i = M' := by
  letI := M.FOStructure
  rw [Set.termDefinable_empty_iff] at h
  obtain ⟨t, ht⟩ := h
  obtain ⟨i, hi⟩ := hC.exists_op_eq_realize t
  obtain ⟨op⟩ := M'
  refine ⟨i, congrArg Magma.mk ?_⟩
  funext x y
  rw [hi]
  exact (congrFun ht ![x, y]).symm

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- **Clone obstruction.** If `L'` has a model `M` whose clone is contained in the family `C`, and
no member of `C` satisfies `L`, then `L` is not term-definable from `L'`. -/
theorem not_termDefinableFrom_of_clone {G : Type} (M : Magma G) (hM : @satisfies _ G M L')
    {ι : Type*} {C : ι → Magma G} {i₁ i₂ : ι} {c : ι → ι → ι}
    (hC : M.IsCloneFamily C i₁ i₂ c) (hL : ∀ i, ¬ @satisfies _ G (C i) L) :
    ¬ L.TermDefinableFrom L' := fun h ↦
  let ⟨_, hM', hd⟩ := h M hM
  let ⟨i, hi⟩ := hC.exists_eq hd
  hL i (hi ▸ hM')

end Law.MagmaLaw

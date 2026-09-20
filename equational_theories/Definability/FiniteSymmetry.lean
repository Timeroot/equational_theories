import equational_theories.Definability.ExactAut

/-! Finite orbit charts built from words in a small list of permutations.
The finite data prove coverage; a prescribed pattern of additional automorphisms
then obstructs mutual first-order definability. -/

open Law Law.MagmaLaw

namespace Magma.FiniteSymmetry

variable {n g k m h q : ℕ}

/-- Apply a word directly, avoiding chains of freshly allocated composed equivalences. -/
def wordForward (generators : Fin g → Equiv.Perm (Fin n)) :
    List (Fin g) → Fin n → Fin n
  | [], x => x
  | i :: w, x => generators i (wordForward generators w x)

def wordBackward (generators : Fin g → Equiv.Perm (Fin n)) :
    List (Fin g) → Fin n → Fin n
  | [], x => x
  | i :: w, x => wordBackward generators w ((generators i).symm x)

theorem backward_forward (generators : Fin g → Equiv.Perm (Fin n))
    (w : List (Fin g)) (x : Fin n) :
    wordBackward generators w (wordForward generators w x) = x := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa only [wordForward, wordBackward, Equiv.symm_apply_apply] using ih

theorem forward_backward (generators : Fin g → Equiv.Perm (Fin n))
    (w : List (Fin g)) (x : Fin n) :
    wordForward generators w (wordBackward generators w x) = x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih => simp only [wordForward, wordBackward, ih, Equiv.apply_symm_apply]

@[inline] def wordPerm (generators : Fin g → Equiv.Perm (Fin n))
    (w : List (Fin g)) : Equiv.Perm (Fin n) :=
  ⟨wordForward generators w, wordBackward generators w,
    backward_forward generators w, forward_backward generators w⟩

theorem word_endo (M : Magma (Fin n)) (generators : Fin g → Equiv.Perm (Fin n))
    (hg : ∀ i, M.IsEndo (generators i)) (w : List (Fin g)) :
    M.IsEndo (wordPerm generators w) := by
  induction w with
  | nil => exact Magma.isEndo_id M
  | cons i w ih => exact (hg i).comp ih

@[implicit_reducible] def family (generators : Fin g → Equiv.Perm (Fin n)) (words : Fin k → List (Fin g))
    (tr : Fin n → Fin n → Fin m × Fin k) (sizes : Fin m → ℕ)
    (values : (i : Fin m) → Fin (sizes i) → Fin n)
    (p : (i : Fin m) → Fin (sizes i)) : Magma (Fin n) :=
  ⟨Magma.transport (fun i => wordPerm generators (words i)) tr (fun i => values i (p i))⟩

theorem classification
    (generators : Fin g → Equiv.Perm (Fin n)) (words : Fin k → List (Fin g))
    (rep : Fin m → Fin n × Fin n) (tr : Fin n → Fin n → Fin m × Fin k)
    (sizes : Fin m → ℕ) (values : (i : Fin m) → Fin (sizes i) → Fin n)
    (stabilizers : Fin m → Fin h → Fin k)
    (htr : ∀ x y,
      wordPerm generators (words (tr x y).2) (rep (tr x y).1).1 = x ∧
      wordPerm generators (words (tr x y).2) (rep (tr x y).1).2 = y)
    (hfix : ∀ i j,
      wordPerm generators (words (stabilizers i j)) (rep i).1 = (rep i).1 ∧
      wordPerm generators (words (stabilizers i j)) (rep i).2 = (rep i).2)
    (hvalues : ∀ i x,
      (∀ j, wordPerm generators (words (stabilizers i j)) x = x) →
      ∃ a, values i a = x)
    (N : Magma (Fin n)) (hg : ∀ i, N.IsEndo (generators i)) :
    ∃ p, family generators words tr sizes values p = N := by
  have he : ∀ i, N.IsEndo (wordPerm generators (words i)) :=
    fun i => word_endo N generators hg _
  have hv : ∀ i, ∃ a, values i a = N.op (rep i).1 (rep i).2 := fun i =>
    Magma.exists_val_of_isEndo (idx := stabilizers i) he (hfix i) (hvalues i)
  choose p hp using hv
  refine ⟨p, ?_⟩
  have ht := Magma.op_eq_transport (rep := rep) (tr := tr) he htr
  apply congrArg Magma.mk
  change Magma.transport _ tr (fun i => values i (p i)) = N.op
  rw [funext hp, ← ht]

def Pattern (M : Magma (Fin n)) (probes : Fin q → Equiv.Perm (Fin n))
    (pattern : Fin q → Bool) : Prop :=
  ∀ i, M.IsEndo (probes i) ↔ pattern i = true

instance (M : Magma (Fin n)) (probes : Fin q → Equiv.Perm (Fin n))
    (pattern : Fin q → Bool) : Decidable (Pattern M probes pattern) := by
  unfold Pattern
  infer_instance

theorem not_structuralFromFin {L L' : NatMagmaLaw}
    (M : Magma (Fin n)) (generators : Fin g → Equiv.Perm (Fin n))
    (probes : Fin q → Equiv.Perm (Fin n)) (pattern : Fin q → Bool)
    {P : Type} (F : P → Magma (Fin n))
    (hcoverage : ∀ N : Magma (Fin n), (∀ i, N.IsEndo (generators i)) → ∃ p, F p = N)
    (hsource : @satisfies _ (Fin n) M L')
    (hg : ∀ i, M.IsEndo (generators i)) (hpattern : Pattern M probes pattern)
    (htarget : ∀ p, @satisfies _ (Fin n) (F p) L → ¬ Pattern (F p) probes pattern) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨N, hN, hf, hb⟩ := h M hsource
  have hgN : ∀ i, N.IsEndo (generators i) := fun i =>
    Magma.IsEndo.of_definable hf (hg i)
  obtain ⟨p, rfl⟩ := hcoverage N hgN
  apply htarget p hN
  intro i
  constructor
  · intro hi
    exact (hpattern i).mp (Magma.IsEndo.of_definable hb hi)
  · intro hi
    exact Magma.IsEndo.of_definable hf ((hpattern i).mpr hi)

end Magma.FiniteSymmetry

/-- info: 'Magma.FiniteSymmetry.classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.FiniteSymmetry.classification
/-- info: 'Magma.FiniteSymmetry.not_structuralFromFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.FiniteSymmetry.not_structuralFromFin

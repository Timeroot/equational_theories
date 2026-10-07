import Mathlib.Dynamics.PeriodicPts.Defs
import equational_theories.Definability.DiagRow
import equational_theories.Definability.E63Malcev

/-!
# Recovering an erased diagonal from a finite column cycle

Suppose every column is injective and its diagonal point lies on a cycle
of a fixed positive length `k`. Replace `x*x` by `x`, leaving all other
entries unchanged. The erased square is the unique value omitted by the
off-diagonal column that reaches `x` after `k-1` steps in the new column.
Both conditions are first-order. Surjectivity of the column is unnecessary.
-/

namespace EraseCycle
variable {G : Type*}
open scoped Classical in
noncomputable def erase (f : G → G) (a : G) (x : G) := if x = a then a else f x

lemma iterate_erase_fixed (f : G → G) (a : G) (n : ℕ) : (erase f a)^[n] a = a := by
  apply Function.IsFixedPt.iterate
  simp [Function.IsFixedPt, erase]

lemma erase_hits (f : G → G) (a z : G) (n : ℕ) (h : f^[n] z = a) :
    (erase f a)^[n] z = a := by
  induction n generalizing z with
  | zero => simpa using h
  | succ n ih =>
    by_cases hz : z = a
    · subst z; exact iterate_erase_fixed f a _
    · rw [Function.iterate_succ_apply] at h ⊢
      rw [erase, if_neg hz]
      exact ih (f z) h

lemma hits_of_erase_hits (f : G → G) (a z : G) (n : ℕ)
    (h : (erase f a)^[n] z = a) : ∃ m, f^[m] z = a := by
  induction n generalizing z with
  | zero => exact ⟨0, h⟩
  | succ n ih =>
    by_cases hz : z = a
    · exact ⟨0, hz⟩
    · rw [Function.iterate_succ_apply, erase, if_neg hz] at h
      obtain ⟨m, hm⟩ := ih (f z) h
      exact ⟨m+1, by simpa [Function.iterate_succ_apply] using hm⟩

lemma recover (f : G → G) (hf : Function.Injective f) (a z : G)
    (k : ℕ) (hk : 0 < k) (hcycle : f^[k] a = a) :
    z = f a ↔ (erase f a)^[k-1] z = a ∧ ∀ u, u = a ∨ z ≠ erase f a u := by
  constructor
  · rintro rfl
    constructor
    · apply erase_hits
      have hk' : k - 1 + 1 = k := by omega
      rw [← Function.iterate_succ_apply]
      simpa only [Nat.succ_eq_add_one, hk'] using hcycle
    · intro u
      by_cases hu : u = a
      · exact Or.inl hu
      · exact Or.inr (by simpa [erase, hu] using fun h => hu (hf h.symm))
  · rintro ⟨hz, hmiss⟩
    obtain ⟨m, hm⟩ := hits_of_erase_hits f a z (k-1) hz
    have hper : f^[k] z = z := by
      apply hf.iterate m
      calc
        f^[m] (f^[k] z) = f^[k] (f^[m] z) := by rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]
        _ = a := by rw [hm, hcycle]
        _ = f^[m] z := hm.symm
    let u := f^[k-1] z
    have hu : f u = z := by
      have hk' : k - 1 + 1 = k := by omega
      simpa [u, ← Function.iterate_succ_apply', hk'] using hper
    rcases hmiss u with h | h
    · simpa [h] using hu.symm
    · by_cases hua : u = a
      · simpa [hua] using hu.symm
      · exact (h (by simpa [erase, hua] using hu.symm)).elim
end EraseCycle

open FirstOrder FirstOrder.Language Law Law.MagmaLaw

attribute [local instance] instFOStructure

namespace DiagonalCycle

open DiagRepair (ap)

private abbrev T (G : Type) :=
  (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0)
private def x (G : Type) : T G := Term.var (Sum.inl (some 0))
private def y (G : Type) : T G := Term.var (Sum.inl (some 1))
private def z (G : Type) : T G := Term.var (Sum.inl none)

/-- Iterate the column through the first input, starting at the output slot. -/
def colIter (G : Type) : ℕ → T G
  | 0 => z G
  | n+1 => ap G (colIter G n) (x G)

lemma realize_colIter {G : Type} [P : Magma G] (v : Option (Fin 2) → G)
    (xs : Fin 0 → G) (n : ℕ) :
    Term.realize (Sum.elim v xs) (colIter G n) =
      (fun u => P.op u (v (some 0)))^[n] (v none) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [colIter, ap, Term.realize_functions_apply₂, Magma.FOStructure_funMap',
      Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one, ih, x,
      Term.realize_var, Sum.elim_inl, Function.iterate_succ_apply']

/-- The missing value must also lie on the broken diagonal cycle. -/
def diagFormula (G : Type) (k : ℕ) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  Term.bdEqual (colIter G (k-1)) (x G) ⊓ DiagRow.colFormula G

def recFormula (G : Type) (k : ℕ) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (∼(Term.bdEqual (x G) (y G)) ⊓ Term.bdEqual (z G) (ap G (x G) (y G))) ⊔
    (Term.bdEqual (x G) (y G) ⊓ diagFormula G k)

lemma column_erase {G : Type} (M : Magma G) (a : G) :
    (fun u => (QFOp.idem.magma M).op u a) = EraseCycle.erase (fun u => M.op u a) a := by
  classical
  funext u
  by_cases h : u = a
  · subst u
    simp [EraseCycle.erase, QFOp.idem_diag]
  · rw [QFOp.idem_ne M u a h]
    simp [EraseCycle.erase, h]

theorem definable_graph {G : Type} (M : Magma G) (k : ℕ) (hk : 0 < k)
    (hinj : ∀ a, Function.Injective (fun u => M.op u a))
    (hcycle : ∀ a, (fun u => M.op u a)^[k] a = a) :
    @Set.Definable G ∅ MagmaLanguage (QFOp.idem.magma M).FOStructure _ M.Graph := by
  classical
  refine ⟨recFormula G k, Set.ext fun v => ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [Set.mem_setOf_eq, recFormula, diagFormula, Formula.Realize,
    BoundedFormula.realize_sup, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    BoundedFormula.realize_bdEqual, x, y, z, ap, Term.realize_functions_apply₂,
    Magma.FOStructure_funMap', Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Term.realize_var, Sum.elim_inl,
    @realize_colIter G (QFOp.idem.magma M),
    @DiagRow.realize_colFormula G (QFOp.idem.magma M)]
  by_cases hxy : v (some 0) = v (some 1)
  · rw [← hxy]
    simp only [ne_eq, not_true_eq_false, false_and, true_and, false_or]
    have hh := EraseCycle.recover (fun u => M.op u (v (some 0)))
      (hinj (v (some 0))) (v (some 0)) (v none) k hk (hcycle (v (some 0)))
    simpa only [← column_erase M (v (some 0))] using eq_comm.trans hh
  · simp only [hxy, not_false_eq_true, true_and, false_and, or_false]
    rw [QFOp.idem_ne M _ _ hxy]
    exact eq_comm

/-- Every such source is FO interdefinable with an idempotent magma. -/
theorem structuralFrom_idem {L : NatMagmaLaw} (k : ℕ) (hk : 0 < k)
    (h : ∀ {G : Type} (M : Magma G), satisfies G L →
      (∀ a, Function.Injective (fun u => M.op u a)) ∧
      (∀ a, (fun u => M.op u a)^[k] a = a)) :
    Law3.StructuralFrom L := by
  intro G M hM
  refine ⟨QFOp.idem.magma M, ?_, QFOp.idem.definable_graph M,
    definable_graph M k hk (h M hM).1 (h M hM).2⟩
  exact (@Law3.models_iff G (QFOp.idem.magma M)).mpr fun a => (QFOp.idem_diag M a).symm

end DiagonalCycle

/-- E118 columns are injective, and their diagonal point has period three. -/
theorem Equation3_structuralFrom_Equation118_diagonalCycle :
    Law3.StructuralFrom Law118 := by
  apply DiagonalCycle.structuralFrom_idem 3 (by decide)
  intro G M hM
  have h := (@Law118.models_iff G M).mp hM
  refine ⟨(@E63Family.split118 G M h).right_injective, ?_⟩
  intro a
  change M.op (M.op (M.op a a) a) a = a
  have hac : M.op a (M.op (M.op a a) a) = a := (h a a).symm
  have hh := h a (M.op (M.op a a) a)
  simpa only [hac] using hh.symm

/-- E1289 has the analogous four-cycle; no column-surjectivity assumption is used. -/
theorem Equation3_structuralFrom_Equation1289_diagonalCycle :
    Law3.StructuralFrom Law1289 := by
  apply DiagonalCycle.structuralFrom_idem 4 (by decide)
  intro G M hM
  have h := (@Law1289.models_iff G M).mp hM
  constructor
  · intro a u v huv
    change M.op u a = M.op v a at huv
    calc
      u = M.op a (M.op (M.op (M.op u a) a) a) := h u a
      _ = M.op a (M.op (M.op (M.op v a) a) a) := by rw [huv]
      _ = v := (h v a).symm
  · intro a
    change M.op (M.op (M.op (M.op a a) a) a) a = a
    have hac : M.op a (M.op (M.op (M.op a a) a) a) = a := (h a a).symm
    have hh := h a (M.op (M.op (M.op a a) a) a)
    simpa only [hac] using hh.symm

spectrum_assert DiagonalCycle.structuralFrom_idem complete
spectrum_assert Equation3_structuralFrom_Equation118_diagonalCycle complete
spectrum_assert Equation3_structuralFrom_Equation1289_diagonalCycle complete

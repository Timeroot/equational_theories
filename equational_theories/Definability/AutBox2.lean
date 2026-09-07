import equational_theories.Definability.AutBox

/-!
# The guarded companion with two guards

`AutBox.iteOf` is a one-guard case tree over words of size at most two, and that family is spent:
of the 4,694 laws, 362 sources own a companion no finite model refutes, and the companions they own
satisfy about thirteen open targets each -- 3,558 reduced `structural/fin` cells in all.  Widening
the *words* does not help.  Measured on the model bank and then on `vampire -sa fmb`, the narrow
family survives 5.1% of the time, `|A|, |B| ≤ 3` survives 0%, and `|P|, |Q| ≤ 3` survives 0.12%: a
bigger word makes the companion's own automorphism group bigger, and the obligation
`Aut(□) ⊆ Aut(◇)` is exactly what that breaks.

A second *guard* moves the other way.  The companion

    x □ y := if P = Q then A else if R = S then B else C

reads three cases of `◇` where the one-guard tree reads two, so `□` records strictly more of `◇`
and `Aut(□) ⊆ Aut(◇)` is easier, not harder -- while every word stays at size two.  The obligation
is the same shape with one more Horn clause, and the target half gains a case, which is why the
companion is still handed to the prover as an opaque `k` with its defining clauses rather than as
an `ite` term ([[grind-disjunction-idiom]]).
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

attribute [local instance] instFOStructure

namespace AutBox

variable {G : Type}

open QFOp in
/-- `x □ y := if P(x, y) = Q(x, y) then A(x, y) else if R(x, y) = S(x, y) then B else C`. -/
def iteOf2 (P Q R S A B C : FreeMagma (Fin 2)) : QFOp :=
  .ite P Q (.leaf A) (.ite R S (.leaf B) (.leaf C))

open scoped Classical in
theorem iteOf2_apply (P Q R S A B C : FreeMagma (Fin 2)) (M : Magma G) (a b : G) :
    ((iteOf2 P Q R S A B C).magma M).op a b =
      if @evalInMagma _ _ M ![a, b] P = @evalInMagma _ _ M ![a, b] Q then
        @evalInMagma _ _ M ![a, b] A
      else if @evalInMagma _ _ M ![a, b] R = @evalInMagma _ _ M ![a, b] S then
        @evalInMagma _ _ M ![a, b] B
      else @evalInMagma _ _ M ![a, b] C := by
  show @QFOp.eval _ M (iteOf2 P Q R S A B C) ![a, b] = _
  simp only [iteOf2, QFOp.eval]

/-- The automorphism obligation of the two-guard companion, as a property of the source alone.
As in `GuardAut` the companion is handed over as a function `k` with its defining clauses, so a
superposition proof never has to split on a guard. -/
abbrev GuardAut2 (P Q R S A B C : FreeMagma (Fin 2)) (L' : Law.MagmaLaw ℕ) : Prop :=
  ∀ {G : Type} [Finite G] (M : Magma G), satisfies G L' →
    ∀ σ τ : G → G, (∀ a : G, τ (σ a) = a) → (∀ a : G, σ (τ a) = a) →
    ∀ k : G → G → G,
      (∀ a b : G, @evalInMagma _ _ M ![a, b] P = @evalInMagma _ _ M ![a, b] Q →
        k a b = @evalInMagma _ _ M ![a, b] A) →
      (∀ a b : G, @evalInMagma _ _ M ![a, b] P ≠ @evalInMagma _ _ M ![a, b] Q →
        @evalInMagma _ _ M ![a, b] R = @evalInMagma _ _ M ![a, b] S →
        k a b = @evalInMagma _ _ M ![a, b] B) →
      (∀ a b : G, @evalInMagma _ _ M ![a, b] P ≠ @evalInMagma _ _ M ![a, b] Q →
        @evalInMagma _ _ M ![a, b] R ≠ @evalInMagma _ _ M ![a, b] S →
        k a b = @evalInMagma _ _ M ![a, b] C) →
      (∀ a b : G, σ (k a b) = k (σ a) (σ b)) →
    ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b)

/-- Identity, so that a script can `refine AutBox.guardAut2_of P Q R S A B C (fun {G} _ M hM σ τ
h1 h2 k h1 h2 h3 hcom a b ↦ ?_)` and land on the unfolded goal. -/
theorem guardAut2_of (P Q R S A B C : FreeMagma (Fin 2)) {L' : Law.MagmaLaw ℕ}
    (h : GuardAut2 P Q R S A B C L') : GuardAut2 P Q R S A B C L' := h

/-- `GuardAut2` is antitone in the law: a stronger source has fewer models and inherits it. -/
theorem guardAut2_mono {L L' : Law.MagmaLaw ℕ} (P Q R S A B C : FreeMagma (Fin 2))
    (h : ∀ {G : Type} (M : Magma G), @satisfies _ G M L → @satisfies _ G M L')
    (hg : GuardAut2 P Q R S A B C L') : GuardAut2 P Q R S A B C L :=
  fun M hM ↦ hg M (h M hM)

/-- Collapsing the second guard recovers the one-guard obligation, so no `GuardAut` proof is
wasted: `iteOf P Q A B` is `iteOf2 P Q R S A B B` for any `R`, `S`. -/
theorem guardAut2_of_guardAut {L' : Law.MagmaLaw ℕ} (P Q R S A B : FreeMagma (Fin 2))
    (h : GuardAut P Q A B L') : GuardAut2 P Q R S A B B L' :=
  fun M hM σ τ h1 h2 k hA hB hC hcom ↦
    h M hM σ τ h1 h2 k hA
      (fun a b hne ↦ (eq_or_ne (@evalInMagma _ _ M ![a, b] R) (@evalInMagma _ _ M ![a, b] S)).elim
        (hB a b hne) (hC a b hne)) hcom

/-- **The guarded device with two guards.**  One automorphism obligation for the source, one
equational obligation per target, and the companion may be any two-guard case tree. -/
theorem structuralFromFin_iteOf2 {L L' : Law.MagmaLaw ℕ} (P Q R S A B C : FreeMagma (Fin 2))
    (hg : GuardAut2 P Q R S A B C L')
    (hsat : ∀ {G : Type} (M : Magma G), satisfies G L' →
      @satisfies _ G ((iteOf2 P Q R S A B C).magma M) L) :
    L.StructuralFromFin L' := by
  intro G _ M hM
  classical
  refine ⟨(iteOf2 P Q R S A B C).magma M, hsat M hM,
    (iteOf2 P Q R S A B C).definable_graph M, ?_⟩
  refine Magma.definable_of_aut_invariant ((iteOf2 P Q R S A B C).magma M) M.Graph ?_
  intro σ hbij hhom v hv
  let e : G ≃ G := Equiv.ofBijective σ hbij
  set k : G → G → G := fun a b ↦
    if @evalInMagma _ _ M ![a, b] P = @evalInMagma _ _ M ![a, b] Q then
      @evalInMagma _ _ M ![a, b] A
    else if @evalInMagma _ _ M ![a, b] R = @evalInMagma _ _ M ![a, b] S then
      @evalInMagma _ _ M ![a, b] B
    else @evalInMagma _ _ M ![a, b] C with hk
  have hall : ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b) := by
    refine hg M hM σ e.symm (fun a ↦ e.symm_apply_apply a) (fun a ↦ e.apply_symm_apply a) k
      (fun a b h ↦ by rw [hk]; exact if_pos h)
      (fun a b h h' ↦ by rw [hk]; exact (if_neg h).trans (if_pos h'))
      (fun a b h h' ↦ by rw [hk]; exact (if_neg h).trans (if_neg h')) ?_
    intro a b
    have h1 := hhom a b
    rwa [iteOf2_apply P Q R S A B C M a b,
      iteOf2_apply P Q R S A B C M (σ a) (σ b)] at h1
  show M.op (σ (v (some 0))) (σ (v (some 1))) = σ (v none)
  rw [← hall]
  exact congrArg σ hv

end AutBox

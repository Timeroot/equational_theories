import equational_theories.Definability.AutBox2

/-!
# The guarded companion with three guards

`AutBox2` argues that a second guard makes the automorphism obligation *easier*: the companion

    x □ y := if P = Q then A else if R = S then B else C

reads three cases of `◇` where the one-guard tree reads two, so `□` records strictly more of `◇`
and `Aut(□) ⊆ Aut(◇)` is more likely, while every word stays at size two.  A third guard is the
same move again, and the measurement that motivates it is sharp.  The obligation turns out not to
need the source law at all for part of the family -- `Aut(□) ⊆ Aut(◇)` holds in *every* magma --
and that law-free slice is the whole game, because it costs one derivation for the entire board
instead of one per source.  Of the 25,758 two-guard companions, 218 survive an exhaustive `Aut`
screen over every magma of order at most three and 211 of those are proved law-free; the three-guard
family is 4,374,000 companions and screens the same way.

Everything below is `AutBox2` with one more `if`.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

attribute [local instance] instFOStructure

namespace AutBox

variable {G : Type}

open QFOp in
/-- `x □ y := if P = Q then A else if R = S then B else if T = U then C else D`. -/
def iteOf3 (P Q R S T U A B C D : FreeMagma (Fin 2)) : QFOp :=
  .ite P Q (.leaf A) (.ite R S (.leaf B) (.ite T U (.leaf C) (.leaf D)))

open scoped Classical in
theorem iteOf3_apply (P Q R S T U A B C D : FreeMagma (Fin 2)) (M : Magma G) (a b : G) :
    ((iteOf3 P Q R S T U A B C D).magma M).op a b =
      if @evalInMagma _ _ M ![a, b] P = @evalInMagma _ _ M ![a, b] Q then
        @evalInMagma _ _ M ![a, b] A
      else if @evalInMagma _ _ M ![a, b] R = @evalInMagma _ _ M ![a, b] S then
        @evalInMagma _ _ M ![a, b] B
      else if @evalInMagma _ _ M ![a, b] T = @evalInMagma _ _ M ![a, b] U then
        @evalInMagma _ _ M ![a, b] C
      else @evalInMagma _ _ M ![a, b] D := by
  show @QFOp.eval _ M (iteOf3 P Q R S T U A B C D) ![a, b] = _
  simp only [iteOf3, QFOp.eval]

/-- The automorphism obligation of the three-guard companion, as a property of the source alone.
As in `GuardAut2` the companion is handed over as a function `k` with its defining clauses, so a
superposition proof never has to split on a guard. -/
abbrev GuardAut3 (P Q R S T U A B C D : FreeMagma (Fin 2)) (L' : Law.MagmaLaw ℕ) : Prop :=
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
        @evalInMagma _ _ M ![a, b] T = @evalInMagma _ _ M ![a, b] U →
        k a b = @evalInMagma _ _ M ![a, b] C) →
      (∀ a b : G, @evalInMagma _ _ M ![a, b] P ≠ @evalInMagma _ _ M ![a, b] Q →
        @evalInMagma _ _ M ![a, b] R ≠ @evalInMagma _ _ M ![a, b] S →
        @evalInMagma _ _ M ![a, b] T ≠ @evalInMagma _ _ M ![a, b] U →
        k a b = @evalInMagma _ _ M ![a, b] D) →
      (∀ a b : G, σ (k a b) = k (σ a) (σ b)) →
    ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b)

/-- Identity, so that a script can `refine AutBox.guardAut3_of P Q R S T U A B C D (fun {G} _ M hM
σ τ h1 h2 k h1 h2 h3 h4 hcom a b ↦ ?_)` and land on the unfolded goal. -/
theorem guardAut3_of (P Q R S T U A B C D : FreeMagma (Fin 2)) {L' : Law.MagmaLaw ℕ}
    (h : GuardAut3 P Q R S T U A B C D L') : GuardAut3 P Q R S T U A B C D L' := h

/-- `GuardAut3` is antitone in the law: a stronger source has fewer models and inherits it. -/
theorem guardAut3_mono {L L' : Law.MagmaLaw ℕ} (P Q R S T U A B C D : FreeMagma (Fin 2))
    (h : ∀ {G : Type} (M : Magma G), @satisfies _ G M L → @satisfies _ G M L')
    (hg : GuardAut3 P Q R S T U A B C D L') : GuardAut3 P Q R S T U A B C D L :=
  fun M hM ↦ hg M (h M hM)

/-- Collapsing the third guard recovers the two-guard obligation, so no `GuardAut2` proof is
wasted: `iteOf2 P Q R S A B C` is `iteOf3 P Q R S T U A B C C` for any `T`, `U`. -/
theorem guardAut3_of_guardAut2 {L' : Law.MagmaLaw ℕ} (P Q R S T U A B C : FreeMagma (Fin 2))
    (h : GuardAut2 P Q R S A B C L') : GuardAut3 P Q R S T U A B C C L' :=
  fun M hM σ τ h1 h2 k hA hB hC hD hcom ↦
    h M hM σ τ h1 h2 k hA hB
      (fun a b h1' h2' ↦
        (eq_or_ne (@evalInMagma _ _ M ![a, b] T) (@evalInMagma _ _ M ![a, b] U)).elim
          (hC a b h1' h2') (hD a b h1' h2'))
      hcom

/-- **The guarded device with three guards.**  One automorphism obligation for the source, one
equational obligation per target, and the companion may be any three-guard case tree. -/
theorem structuralFromFin_iteOf3 {L L' : Law.MagmaLaw ℕ} (P Q R S T U A B C D : FreeMagma (Fin 2))
    (hg : GuardAut3 P Q R S T U A B C D L')
    (hsat : ∀ {G : Type} (M : Magma G), satisfies G L' →
      @satisfies _ G ((iteOf3 P Q R S T U A B C D).magma M) L) :
    L.StructuralFromFin L' := by
  intro G _ M hM
  classical
  refine ⟨(iteOf3 P Q R S T U A B C D).magma M, hsat M hM,
    (iteOf3 P Q R S T U A B C D).definable_graph M, ?_⟩
  refine Magma.definable_of_aut_invariant ((iteOf3 P Q R S T U A B C D).magma M) M.Graph ?_
  intro σ hbij hhom v hv
  let e : G ≃ G := Equiv.ofBijective σ hbij
  set k : G → G → G := fun a b ↦
    if @evalInMagma _ _ M ![a, b] P = @evalInMagma _ _ M ![a, b] Q then
      @evalInMagma _ _ M ![a, b] A
    else if @evalInMagma _ _ M ![a, b] R = @evalInMagma _ _ M ![a, b] S then
      @evalInMagma _ _ M ![a, b] B
    else if @evalInMagma _ _ M ![a, b] T = @evalInMagma _ _ M ![a, b] U then
      @evalInMagma _ _ M ![a, b] C
    else @evalInMagma _ _ M ![a, b] D with hk
  have hall : ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b) := by
    refine hg M hM σ e.symm (fun a ↦ e.symm_apply_apply a) (fun a ↦ e.apply_symm_apply a) k
      (fun a b h ↦ by rw [hk]; exact if_pos h)
      (fun a b h h' ↦ by rw [hk]; exact (if_neg h).trans (if_pos h'))
      (fun a b h h' h'' ↦ by rw [hk]; exact (if_neg h).trans ((if_neg h').trans (if_pos h'')))
      (fun a b h h' h'' ↦ by rw [hk]; exact (if_neg h).trans ((if_neg h').trans (if_neg h''))) ?_
    intro a b
    have h1 := hhom a b
    rwa [iteOf3_apply P Q R S T U A B C D M a b,
      iteOf3_apply P Q R S T U A B C D M (σ a) (σ b)] at h1
  show M.op (σ (v (some 0))) (σ (v (some 1))) = σ (v none)
  rw [← hall]
  exact congrArg σ hv

end AutBox

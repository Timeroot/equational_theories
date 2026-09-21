import equational_theories.Definability.Confluence477Recovery
import equational_theories.Definability.Confluence680Recovery
import equational_theories.Definability.DualSevenRecovery

/-!
The right crossed-inverse law E4273 makes left cubing a unary endomorphism.
In the confluent E115, E477 and E680 models, a unary term endomorphism can only
be the identity. A reversible E4273 companion would therefore satisfy E14.
Surjective evaluation into the algebraic countermodels rules this out.
-/

open FirstOrder Law Law.MagmaLaw FreeMagma Confluence
namespace ConfluenceCrossedInverse

theorem cube_hom4273 {X : Type} (M : Magma X) (h : @Equation4273 X M) :
    ∀ x y, M.op (M.op x y) (M.op (M.op x y) (M.op x y)) =
      M.op (M.op x (M.op x x)) (M.op y (M.op y y)) := by
  intro x y
  have h1 := h x y
  have h2 := h y (M.op x y)
  have h3 := h (M.op x y) (M.op x (M.op x x))
  grind

theorem not_on_of_rigidity {X : Type} (M : Magma X) (P : (X → X → X) → Prop)
    (hP : M.IsCloneInvariant P)
    (hr : ∀ f, P f → (∀ x y, f (M.op x y) (M.op x y) = M.op (f x x) (f y y)) →
      ∀ x, f x x = x)
    (hbad : ¬ Law14.TermStructuralOnMagma M) : ¬ Law4273.TermStructuralOnMagma M := by
  rintro ⟨N, hN, hfwd, hback⟩
  let B : Magma X := ⟨fun x _ => N.op x (N.op x x)⟩
  have hbdef : @Set.TermDefinable X ∅ MagmaLanguage N.FOStructure (Fin 2) B.FinArityOp :=
    TermRecoveryHom.termMagma_definable N
      ((.Leaf (0 : Fin 2) ⋆ (.Leaf 0 ⋆ .Leaf 0)).toTerm)
  have hbg := hP.of_termDefinable (TermDefinable.trans_aux hfwd hbdef)
  have hbh := (FreeUnary115.hom_invariant N (fun x => N.op x (N.op x x))
    (cube_hom4273 N ((@Law4273.models_iff X N).mp hN))).of_termDefinable hback
  have hfix := hr B.op hbg hbh
  have h14 : @satisfies _ X N Law14 := by
    apply (@Law14.models_iff X N).mpr
    intro x y
    have hh := ((@Law4273.models_iff X N).mp hN) x y
    exact (hfix x).symm.trans hh
  exact hbad ⟨N, h14, hfwd, hback⟩

theorem law680_of14 {X : Type} (M : Magma X) (h : @Equation14 X M) :
    @Equation680 X M := by
  have hc : ∀ x, M.op (M.op x x) x = x := by
    intro x
    have h1 := h x x
    have h2 := h (M.op x x) x
    have h3 := h x (M.op x x)
    grind
  intro x y
  rw [hc]
  exact h x y

theorem negative477 : ¬ Law4273.TermStructuralFrom Law477 := by
  intro h
  have hbad : ¬ Law14.TermStructuralOnMagma
      (Confluence.instMagmaConfMagma (@Confluence477Recovery.rules GaussianInt _)) := by
    rintro ⟨N, hN, hfwd, hback⟩
    have h680 := (@Law680.models_iff Confluence477Recovery.G N).mpr
      (law680_of14 N ((@Law14.models_iff Confluence477Recovery.G N).mp hN))
    exact Confluence477Recovery.no_base_recovery
      (TermRecoveryHom.transfer (Confluence.instMagmaConfMagma (@Confluence477Recovery.rules GaussianInt _))
        Confluence477Recovery.base Confluence477Recovery.quotient
        Confluence477Recovery.quotient_hom Confluence477Recovery.quotient_surjective
        Law680 ⟨N, h680, hfwd, hback⟩)
  exact not_on_of_rigidity (Confluence.instMagmaConfMagma (@Confluence477Recovery.rules GaussianInt _))
    (ConfluenceTermEndomorphism.Good Confluence477Recovery.rules)
    (ConfluenceTermEndomorphism.good_invariant _ _ Confluence477Recovery.bu_copy)
    Confluence477Recovery.endomorphism_trivial hbad
    (h _ ((@Law477.models_iff Confluence477Recovery.G _).mpr Confluence477Recovery.source_law))

theorem negative680 : ¬ Law4273.TermStructuralFrom Law680 := by
  letI : DecidableEq DualNumberRecovery.R :=
    fun x y => decidable_of_iff (x.fst = y.fst ∧ x.snd = y.snd) TrivSqZeroExt.ext_iff.symm
  intro h
  have hbad : ¬ Law14.TermStructuralOnMagma
      (Confluence.instMagmaConfMagma (@rw680.rules DualNumberRecovery.R
        (fun x y => decidable_of_iff (x.fst = y.fst ∧ x.snd = y.snd) TrivSqZeroExt.ext_iff.symm))) := by
    intro hh
    exact DualNumberRecovery.no_recovery
      (TermRecoveryHom.transfer _ DualNumberRecovery.base Confluence680Recovery.quotient
        Confluence680Recovery.quotient_hom Confluence680Recovery.quotient_surjective Law14 hh)
  exact not_on_of_rigidity _ _
    (ConfluenceTermEndomorphism.good_invariant _ _ Confluence680Recovery.bu_copy)
    Confluence680Recovery.endomorphism_trivial hbad
    (h _ ((@Law680.models_iff Confluence680Recovery.G _).mpr Confluence680Recovery.source_law))

namespace Source115
open FreeUnary115 (copy)
local instance : DecidableEq DualSevenRecovery.R :=
  fun x y => decidable_of_iff (x.fst = y.fst ∧ x.snd = y.snd) TrivSqZeroExt.ext_iff.symm

abbrev G := ConfMagma (@rw115.rules DualSevenRecovery.R _)

theorem source_law : @Equation115 G inferInstance := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  simp only [Magma.op, bu, hx, hy, buFixed_rw_op]
  symm
  apply Subtype.ext
  apply rw115.comp3 ((NF_iff_buFixed rw115.rules).mpr hx)

theorem bu_copy (p : FreeMagma DualSevenRecovery.R)
    (hp : ConfluenceTermEndomorphism.Small rw115.rules p) (t : FreeMagma Unit) :
    bu rw115.rules (copy p t) = copy p (bu rw115.rules t) :=
  FreeUnary115.bu_copy p hp.1 hp.2.1 hp.2.2 t

theorem rules_mixed (s t : FreeMagma Unit) :
    rw115.rules (copy (.Leaf (0 : DualSevenRecovery.R)) s ⋆ copy (.Leaf 1) t) =
      copy (.Leaf (0 : DualSevenRecovery.R)) s ⋆ copy (.Leaf 1) t := by
  apply (rw115.rules.elim _ _).mpr
  refine Or.inr ⟨rfl, ?_, ?_⟩
  · rintro ⟨x, y, he⟩
    obtain ⟨hl, hr⟩ := FreeMagma.Fork.inj he
    have h1 := congrArg FreeUnary115.last hl
    have h2 := congrArg FreeUnary115.last hr
    simp only [FreeUnary115.last_copy, FreeUnary115.last] at h1 h2
    exact (by decide : (0 : DualSevenRecovery.R) ≠ 1) (h1.trans h2.symm)
  · rintro ⟨x, y, he⟩
    obtain ⟨hl, hr⟩ := FreeMagma.Fork.inj he
    have h1 := congrArg FreeUnary115.first hl
    have h2 := congrArg FreeUnary115.first hr
    simp only [FreeUnary115.first_copy, FreeUnary115.first] at h1 h2
    exact (by decide : (0 : DualSevenRecovery.R) ≠ 1) (h1.trans h2.symm)

theorem endomorphism_trivial (f : G → G → G)
    (hg : ConfluenceTermEndomorphism.Good rw115.rules f)
    (hf : ∀ x y : G, f (x ◇ y) (x ◇ y) = f x x ◇ f y y) :
    ∀ x, f x x = x :=
  ConfluenceTermEndomorphism.fixed_by_endomorphism rw115.rules (fun _ => rfl)
    0 1 (by decide) rfl rules_mixed f hg hf

open DualSevenRecovery (base)
def ev : FreeMagma DualSevenRecovery.R → DualSevenRecovery.R := @evalInMagma _ _ base id

@[simp] theorem ev_fork (x y : FreeMagma DualSevenRecovery.R) :
    ev (x ⋆ y) = base.op (ev x) (ev y) := rfl

theorem ev_rule (t : FreeMagma DualSevenRecovery.R) : ev (rw115.rules t) = ev t := by
  generalize hr : rw115.rules t = r
  rcases (rw115.rules.elim t r).mp hr with (h | h) | h
  · obtain ⟨x, y, ht, he⟩ := h
    rw [ht, he]
    exact DualSevenRecovery.source_law (ev x) (ev y)
  · obtain ⟨x, y, ht, he⟩ := h
    rw [ht, he]
    simp only [ev_fork]
    have h1 := DualSevenRecovery.source_law (ev y) (base.op (ev x) (ev x))
    have h2 := DualSevenRecovery.source_law (ev x)
      (base.op (base.op (ev y) (ev y)) (base.op (ev x) (ev x)))
    grind
  · obtain ⟨rfl, _, _⟩ := h
    rfl

theorem ev_bu (t : FreeMagma DualSevenRecovery.R) : ev (bu rw115.rules t) = ev t := by
  induction t with
  | Leaf => rfl
  | Fork x y hx hy => rw [bu, ev_rule, ev_fork, hx, hy, ev_fork]

def quotient (x : G) : DualSevenRecovery.R := ev x.val

theorem quotient_hom (x y : G) : quotient (x ◇ y) = base.op (quotient x) (quotient y) := by
  change ev (bu rw115.rules (x.val ⋆ y.val)) = _
  rw [ev_bu]
  rfl

theorem quotient_surjective : Function.Surjective quotient :=
  fun x => ⟨⟨.Leaf x, rfl⟩, rfl⟩

theorem no14 : ¬ Law14.TermStructuralOnMagma (Confluence.instMagmaConfMagma (@rw115.rules DualSevenRecovery.R _)) :=
  fun h => DualSevenRecovery.no_recovery
    (TermRecoveryHom.transfer _ base quotient quotient_hom quotient_surjective Law14 h)

theorem negative115 : ¬ Law4273.TermStructuralFrom Law115 := by
  intro h
  exact not_on_of_rigidity (Confluence.instMagmaConfMagma rw115.rules)
    (ConfluenceTermEndomorphism.Good rw115.rules)
    (ConfluenceTermEndomorphism.good_invariant _ _ bu_copy)
    endomorphism_trivial no14 (h _ ((@Law115.models_iff G _).mpr source_law))
end Source115

end ConfluenceCrossedInverse

open Law Law.MagmaLaw

theorem Equation4273_not_termStructuralFrom_Equation115_confluence :
    ¬ Law4273.TermStructuralFrom Law115 := ConfluenceCrossedInverse.Source115.negative115

theorem Equation4273_not_termStructuralFrom_Equation477_confluence :
    ¬ Law4273.TermStructuralFrom Law477 := ConfluenceCrossedInverse.negative477

theorem Equation4273_not_termStructuralFrom_Equation680_confluence :
    ¬ Law4273.TermStructuralFrom Law680 := ConfluenceCrossedInverse.negative680

/-- info: 'Equation4273_not_termStructuralFrom_Equation115_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4273_not_termStructuralFrom_Equation115_confluence

/-- info: 'Equation4273_not_termStructuralFrom_Equation477_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4273_not_termStructuralFrom_Equation477_confluence

/-- info: 'Equation4273_not_termStructuralFrom_Equation680_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4273_not_termStructuralFrom_Equation680_confluence

import equational_theories.Confluence1
import equational_theories.Definability.ConfluenceTermEndomorphism
import equational_theories.Definability.TermRecoveryHom
import equational_theories.Definability.GaussianRecovery

/-!
The free E477 model has no nonidentity unary term endomorphism. In an E1492
companion, left cubing is such an endomorphism, and recovery makes it an
endomorphism of the source as well. It must be the identity, so the companion
satisfies E680. Evaluation onto the Gaussian E1496 model then contradicts the
existing Gaussian obstruction to E680 term recovery.
-/

open FreeMagma Confluence
namespace Confluence477Recovery
open FreeUnary115 (copy copy_injective copy_square copy_not_fork_left copy_not_fork_right)

variable {α : Type} [DecidableEq α]
rule_system rules {x y : FreeMagma α}
  | y ⋆ (x ⋆ (y ⋆ (y ⋆ y))) => x

theorem rules_eq : (@rules α _) = rw477.rule := by
  funext t
  unfold rw477.rule
  split
  · simp only [rules, rules.rule1]
    split_ifs <;> grind
  · simp only [rules, rules.rule1]

omit [DecidableEq α] in
theorem copy_pattern (p : FreeMagma α) (hp : p.length ≤ 2)
    (hs : ∀ a, p ≠ a ⋆ a) (t : FreeMagma Unit) (x y : FreeMagma α)
    (h : copy p t = y ⋆ (x ⋆ (y ⋆ (y ⋆ y)))) :
    ∃ a b, t = b ⋆ (a ⋆ (b ⋆ (b ⋆ b))) ∧ x = copy p a ∧ y = copy p b := by
  cases t with
  | Leaf =>
    have he := congrArg FreeMagma.length h
    have hx := x.length_pos
    have hy := y.length_pos
    simp only [copy, length] at he
    omega
  | Fork a b =>
    obtain ⟨ha, hb⟩ := FreeMagma.Fork.inj h
    cases b with
    | Leaf =>
      apply False.elim
      apply copy_not_fork_right p (a ⋆ (a ⋆ a)) x
      simpa only [copy, ha] using hb
    | Fork c d =>
      obtain ⟨hc, hd⟩ := FreeMagma.Fork.inj hb
      cases d with
      | Leaf =>
        exact (copy_not_fork_left p a (y ⋆ y) (hd.trans (by rw [ha]))).elim
      | Fork e f =>
        obtain ⟨he, hf⟩ := FreeMagma.Fork.inj hd
        obtain ⟨v, rfl, hv⟩ := copy_square p hs f y hf
        have hae := copy_injective p (ha.trans he.symm)
        have hav := copy_injective p (ha.trans hv)
        exact ⟨c, a, by rw [← hae, ← hav], hc.symm, ha.symm⟩

theorem rules_copy (p : FreeMagma α) (hp : p.length ≤ 2)
    (hs : ∀ a, p ≠ a ⋆ a) (t : FreeMagma Unit) :
    rules (copy p t) = copy p (rules t) := by
  generalize hr : rules t = r
  rcases (rules.elim t r).mp hr with h | h
  · obtain ⟨x, y, rfl, rfl⟩ := h
    exact rules.eq1 _ _
  · obtain ⟨ht, hn⟩ := h
    rw [← ht]
    apply (rules.elim _ _).mpr
    refine Or.inr ⟨rfl, ?_⟩
    rintro ⟨x, y, he⟩
    obtain ⟨a, b, ha, _, _⟩ := copy_pattern p hp hs t x y he
    exact hn ⟨a, b, ha⟩

theorem bu_copy (p : FreeMagma α) (hp : ConfluenceTermEndomorphism.Small rules p)
    (t : FreeMagma Unit) : bu rules (copy p t) = copy p (bu rules t) := by
  induction t with
  | Leaf => simpa [copy] using hp.2.2
  | Fork a b ha hb =>
    change rules (bu rules (copy p a) ⋆ bu rules (copy p b)) =
      copy p (rules (bu rules a ⋆ bu rules b))
    rw [ha, hb]
    exact rules_copy p hp.1 hp.2.1 (bu rules a ⋆ bu rules b)

theorem rules_mixed (a b : α) (hab : a ≠ b) (s t : FreeMagma Unit) :
    rules (copy (.Leaf a) s ⋆ copy (.Leaf b) t) = copy (.Leaf a) s ⋆ copy (.Leaf b) t := by
  apply (rules.elim _ _).mpr
  refine Or.inr ⟨rfl, ?_⟩
  rintro ⟨x, y, he⟩
  obtain ⟨hl, hr⟩ := FreeMagma.Fork.inj he
  have h1 := congrArg FreeUnary115.last hl
  have h2 := congrArg FreeUnary115.last hr
  simp only [FreeUnary115.last_copy, FreeUnary115.last] at h1 h2
  exact hab (h1.trans h2.symm)

abbrev G := ConfMagma (@rules GaussianInt _)

theorem source_law : @Equation477 G inferInstance := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  simp only [rules_eq] at hx hy
  simp [Magma.op, bu, rules_eq, hx, hy]

theorem endomorphism_trivial (f : G → G → G)
    (hg : ConfluenceTermEndomorphism.Good rules f)
    (hf : ∀ x y : G, f (x ◇ y) (x ◇ y) = f x x ◇ f y y) :
    ∀ x, f x x = x :=
  ConfluenceTermEndomorphism.fixed_by_endomorphism rules (fun _ => rfl)
    0 1 (by decide) rfl (rules_mixed 0 1 (by decide)) f hg hf

open FirstOrder Law Law.MagmaLaw

theorem left_cube_hom1492 {X : Type} (M : Magma X) (h : @Equation1492 X M) :
    ∀ x y, M.op (M.op x y) (M.op (M.op x y) (M.op x y)) =
      M.op (M.op x (M.op x x)) (M.op y (M.op y y)) := by
  intro x y
  grind

@[reducible] def base : Magma GaussianInt := Magma.lin Magma.gi (-Magma.gi)

theorem base_law : @Equation477 GaussianInt base := by
  intro x y
  simp only [Magma.lin_op]
  linear_combination (x - Magma.gi * y) * Magma.gi_sq

def ev : FreeMagma GaussianInt → GaussianInt := @evalInMagma _ _ base id

@[simp] theorem ev_fork (x y : FreeMagma GaussianInt) :
    ev (x ⋆ y) = base.op (ev x) (ev y) := rfl

theorem ev_rule (t : FreeMagma GaussianInt) : ev (rules t) = ev t := by
  generalize hr : rules t = r
  rcases (rules.elim t r).mp hr with h | h
  · obtain ⟨x, y, ht, he⟩ := h
    rw [ht, he]
    exact base_law (ev x) (ev y)
  · obtain ⟨rfl, _⟩ := h
    rfl

theorem ev_bu (t : FreeMagma GaussianInt) : ev (bu rules t) = ev t := by
  induction t with
  | Leaf => rfl
  | Fork x y hx hy =>
    rw [bu, ev_rule, ev_fork, hx, hy, ev_fork]

def quotient (x : G) : GaussianInt := ev x.val

theorem quotient_hom (x y : G) : quotient (x ◇ y) = base.op (quotient x) (quotient y) := by
  change ev (bu rules (x.val ⋆ y.val)) = _
  rw [ev_bu]
  rfl

theorem quotient_surjective : Function.Surjective quotient :=
  fun x => ⟨⟨.Leaf x, rfl⟩, rfl⟩

theorem no_base_recovery : ¬ Law680.TermStructuralOnMagma base := by
  rintro ⟨N, hN, hfwd, hback⟩
  obtain ⟨a, b, _, hop, _⟩ :=
    (Magma.lin_isCloneInvariant Magma.gi (-Magma.gi) (-1) 1 (by ring)).of_termDefinable hfwd
  have hEq : N = Magma.lin a b := by
    cases N
    exact congrArg Magma.mk (funext fun x => funext fun y => hop x y)
  subst N
  exact GaussianRecovery.no_recovery a b
    (GaussianRecovery.traps_680 a b ((@Law680.models_iff GaussianInt (Magma.lin a b)).mp hN)) hback

theorem law680_of_1492_cube {X : Type} (M : Magma X) (h : @Equation1492 X M)
    (hc : ∀ x, M.op x (M.op x x) = x) : @Equation680 X M := by
  have hr : ∀ x y, M.op (M.op y x) y = x := by
    intro x y
    have := h x y
    simpa only [hc] using this.symm
  have hl : ∀ x y, M.op y (M.op x y) = x := by
    intro x y
    have h1 := hr y x
    have h2 := hr x (M.op x y)
    grind
  intro x y
  rw [hr y y]
  exact (hl x y).symm

theorem not_termStructural : ¬ Law1492.TermStructuralFrom Law477 := by
  intro h
  obtain ⟨N, hN, hfwd, hback⟩ := h (inferInstance : Magma G)
    ((@Law477.models_iff G inferInstance).mpr source_law)
  let B : Magma G := ⟨fun x _ => N.op x (N.op x x)⟩
  have hbdef : @Set.TermDefinable G ∅ MagmaLanguage N.FOStructure (Fin 2) B.FinArityOp :=
    TermRecoveryHom.termMagma_definable N
      ((.Leaf (0 : Fin 2) ⋆ (.Leaf 0 ⋆ .Leaf 0)).toTerm)
  have hbg := (ConfluenceTermEndomorphism.good_invariant rules rules bu_copy).of_termDefinable
    (TermDefinable.trans_aux hfwd hbdef)
  have hbh := (FreeUnary115.hom_invariant N (fun x => N.op x (N.op x x))
    (left_cube_hom1492 N ((@Law1492.models_iff G N).mp hN))).of_termDefinable hback
  have hfix := endomorphism_trivial B.op hbg hbh
  have h680 : @satisfies _ G N Law680 := (@Law680.models_iff G N).mpr
    (law680_of_1492_cube N ((@Law1492.models_iff G N).mp hN) hfix)
  exact no_base_recovery (TermRecoveryHom.transfer (Confluence.instMagmaConfMagma rules) base
    quotient quotient_hom quotient_surjective Law680 ⟨N, h680, hfwd, hback⟩)

end Confluence477Recovery

open Law Law.MagmaLaw

theorem Equation1492_not_termStructuralFrom_Equation477_confluence :
    ¬ Law1492.TermStructuralFrom Law477 := Confluence477Recovery.not_termStructural

/-- info: 'Equation1492_not_termStructuralFrom_Equation477_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1492_not_termStructuralFrom_Equation477_confluence

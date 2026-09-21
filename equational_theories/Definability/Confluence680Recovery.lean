import equational_theories.Definability.ConfluenceTermEndomorphism
import equational_theories.Definability.TermRecoveryHom
import equational_theories.Definability.DualNumberRecovery

/-!
No unary term endomorphism of the confluent E680 model is nontrivial. An E1695
companion would therefore have identity right cubing and satisfy E14. The
surjective evaluation onto a rational dual-number E680 model transfers the
purported recovery and contradicts `DualNumberRecovery.no_recovery`.
-/

open FreeMagma Confluence
namespace Confluence680Recovery
open FreeUnary115 (copy copy_injective copy_square copy_not_fork_left copy_not_fork_right)
local notation "rules" => rw680.rules

variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
theorem copy_rule1 (p : FreeMagma α) (hp : p.length ≤ 2)
    (hs : ∀ a, p ≠ a ⋆ a) (t : FreeMagma Unit) (x y : FreeMagma α)
    (h : copy p t = y ⋆ (x ⋆ ((y ⋆ y) ⋆ y))) :
    ∃ a b, t = b ⋆ (a ⋆ ((b ⋆ b) ⋆ b)) ∧ x = copy p a ∧ y = copy p b := by
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
      apply copy_not_fork_right p ((a ⋆ a) ⋆ a) x
      simpa only [copy, ha] using hb
    | Fork c d =>
      obtain ⟨hc, hd⟩ := FreeMagma.Fork.inj hb
      cases d with
      | Leaf =>
        exact (copy_not_fork_right p a (y ⋆ y) (hd.trans (by rw [ha]))).elim
      | Fork e f =>
        obtain ⟨he, hf⟩ := FreeMagma.Fork.inj hd
        obtain ⟨v, rfl, hv⟩ := copy_square p hs e y he
        have hav := copy_injective p (ha.trans hv)
        have haf := copy_injective p (ha.trans hf.symm)
        exact ⟨c, a, by rw [← hav, ← haf], hc.symm, ha.symm⟩

omit [DecidableEq α] in
theorem copy_rule2 (p : FreeMagma α) (hp : p.length ≤ 2)
    (hs : ∀ a, p ≠ a ⋆ a) (t : FreeMagma Unit) (x : FreeMagma α)
    (h : copy p t = ((x ⋆ x) ⋆ x) ⋆ (((x ⋆ x) ⋆ x) ⋆ ((x ⋆ x) ⋆ x))) :
    ∃ a, t = ((a ⋆ a) ⋆ a) ⋆ (((a ⋆ a) ⋆ a) ⋆ ((a ⋆ a) ⋆ a)) ∧ x = copy p a := by
  cases t with
  | Leaf =>
    have he := congrArg FreeMagma.length h
    have hx := x.length_pos
    simp only [copy, length] at he
    omega
  | Fork a b =>
    obtain ⟨ha, hb⟩ := FreeMagma.Fork.inj h
    obtain ⟨v, rfl, hv⟩ := copy_square p hs b ((x ⋆ x) ⋆ x) hb
    have hav := copy_injective p (ha.trans hv)
    cases a with
    | Leaf =>
      have he := congrArg FreeMagma.length ha
      have hx := x.length_pos
      simp only [copy, length] at he
      omega
    | Fork c d =>
      obtain ⟨hc, hd⟩ := FreeMagma.Fork.inj ha
      obtain ⟨w, rfl, hw⟩ := copy_square p hs c x hc
      have hwd := copy_injective p (hw.symm.trans hd.symm)
      exact ⟨d, by rw [← hav, hwd], hd.symm⟩

theorem rules_copy (p : FreeMagma α) (hp : p.length ≤ 2)
    (hs : ∀ a, p ≠ a ⋆ a) (t : FreeMagma Unit) :
    rules (copy p t) = copy p (rules t) := by
  generalize hr : rules t = r
  rcases (rw680.rules.elim t r).mp hr with (h | h) | h
  · obtain ⟨x, y, rfl, he⟩ := h
    rw [he]
    exact rw680.rules.eq1 _ _
  · obtain ⟨x, rfl, he⟩ := h
    rw [he]
    exact rw680.rules.eq2 _
  · obtain ⟨ht, h1, h2⟩ := h
    rw [← ht]
    apply (rw680.rules.elim _ _).mpr
    refine Or.inr ⟨rfl, ?_, ?_⟩
    · rintro ⟨x, y, he⟩
      obtain ⟨a, b, ha, _, _⟩ := copy_rule1 p hp hs t y x he
      exact h1 ⟨b, a, ha⟩
    · rintro ⟨x, he⟩
      obtain ⟨a, ha, _⟩ := copy_rule2 p hp hs t x he
      exact h2 ⟨a, ha⟩

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
  apply (rw680.rules.elim _ _).mpr
  refine Or.inr ⟨rfl, ?_, ?_⟩
  · rintro ⟨x, y, he⟩
    obtain ⟨hl, hr⟩ := FreeMagma.Fork.inj he
    have h1 := congrArg FreeUnary115.last hl
    have h2 := congrArg FreeUnary115.last hr
    simp only [FreeUnary115.last_copy, FreeUnary115.last] at h1 h2
    exact hab (h1.trans h2.symm)
  · rintro ⟨x, he⟩
    obtain ⟨hl, hr⟩ := FreeMagma.Fork.inj he
    have h1 := congrArg FreeUnary115.last hl
    have h2 := congrArg FreeUnary115.last hr
    simp only [FreeUnary115.last_copy, FreeUnary115.last] at h1 h2
    exact hab (h1.trans h2.symm)

local instance : DecidableEq DualNumberRecovery.R :=
  fun x y => decidable_of_iff (x.fst = y.fst ∧ x.snd = y.snd) (TrivSqZeroExt.ext_iff).symm

abbrev G := ConfMagma (@rw680.rules DualNumberRecovery.R _)

theorem source_law : @Equation680 G inferInstance := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  simp (disch := bufixed) only [Magma.op, bu, hx, hy, buFixed_rw_op]
  symm
  apply Subtype.ext
  apply rw680.comp1_4

theorem endomorphism_trivial (f : G → G → G)
    (hg : ConfluenceTermEndomorphism.Good rules f)
    (hf : ∀ x y : G, f (x ◇ y) (x ◇ y) = f x x ◇ f y y) :
    ∀ x, f x x = x :=
  ConfluenceTermEndomorphism.fixed_by_endomorphism rules (fun _ => rfl)
    0 1 (by decide) rfl (rules_mixed 0 1 (by decide)) f hg hf

open FirstOrder Law Law.MagmaLaw

theorem right_cube_hom1695 {X : Type} (M : Magma X) (h : @Equation1695 X M) :
    ∀ x y, M.op (M.op (M.op x y) (M.op x y)) (M.op x y) =
      M.op (M.op (M.op x x) x) (M.op (M.op y y) y) := by
  intro x y
  grind

open DualNumberRecovery (base)

def ev : FreeMagma DualNumberRecovery.R → DualNumberRecovery.R := @evalInMagma _ _ base id

@[simp] theorem ev_fork (x y : FreeMagma DualNumberRecovery.R) :
    ev (x ⋆ y) = base.op (ev x) (ev y) := rfl

theorem ev_rule (t : FreeMagma DualNumberRecovery.R) : ev (rules t) = ev t := by
  generalize hr : rules t = r
  rcases (rw680.rules.elim t r).mp hr with (h | h) | h
  · obtain ⟨x, y, ht, he⟩ := h
    rw [ht, he]
    exact DualNumberRecovery.source_law (ev y) (ev x)
  · obtain ⟨x, ht, he⟩ := h
    rw [ht, he]
    simp only [ev_fork]
    apply TrivSqZeroExt.ext <;> simp [Magma.lin_op] <;> ring
  · obtain ⟨rfl, _, _⟩ := h
    rfl

theorem ev_bu (t : FreeMagma DualNumberRecovery.R) : ev (bu rules t) = ev t := by
  induction t with
  | Leaf => rfl
  | Fork x y hx hy => rw [bu, ev_rule, ev_fork, hx, hy, ev_fork]

def quotient (x : G) : DualNumberRecovery.R := ev x.val

theorem quotient_hom (x y : G) : quotient (x ◇ y) = base.op (quotient x) (quotient y) := by
  change ev (bu rules (x.val ⋆ y.val)) = _
  rw [ev_bu]
  rfl

theorem quotient_surjective : Function.Surjective quotient :=
  fun x => ⟨⟨.Leaf x, rfl⟩, rfl⟩

theorem law14_of_1695_cube {X : Type} (M : Magma X) (h : @Equation1695 X M)
    (hc : ∀ x, M.op (M.op x x) x = x) : @Equation14 X M := by
  have hr : ∀ x y, M.op (M.op y x) y = x := by
    intro x y
    have := h x y
    simpa only [hc] using this.symm
  intro x y
  have h1 := hr y x
  have h2 := hr x (M.op x y)
  grind

theorem not_termStructural : ¬ Law1695.TermStructuralFrom Law680 := by
  intro h
  obtain ⟨N, hN, hfwd, hback⟩ := h (inferInstance : Magma G)
    ((@Law680.models_iff G inferInstance).mpr source_law)
  let B : Magma G := ⟨fun x _ => N.op (N.op x x) x⟩
  have hbdef : @Set.TermDefinable G ∅ MagmaLanguage N.FOStructure (Fin 2) B.FinArityOp :=
    TermRecoveryHom.termMagma_definable N
      (((.Leaf (0 : Fin 2) ⋆ .Leaf 0) ⋆ .Leaf 0).toTerm)
  have hbg := (ConfluenceTermEndomorphism.good_invariant rules rules bu_copy).of_termDefinable
    (TermDefinable.trans_aux hfwd hbdef)
  have hbh := (FreeUnary115.hom_invariant N (fun x => N.op (N.op x x) x)
    (right_cube_hom1695 N ((@Law1695.models_iff G N).mp hN))).of_termDefinable hback
  have hfix := endomorphism_trivial B.op hbg hbh
  have h14 : @satisfies _ G N Law14 := (@Law14.models_iff G N).mpr
    (law14_of_1695_cube N ((@Law1695.models_iff G N).mp hN) hfix)
  exact DualNumberRecovery.no_recovery (TermRecoveryHom.transfer (Confluence.instMagmaConfMagma rules) base
    quotient quotient_hom quotient_surjective Law14 ⟨N, h14, hfwd, hback⟩)

end Confluence680Recovery

open Law Law.MagmaLaw

theorem Equation1695_not_termStructuralFrom_Equation680_confluence :
    ¬ Law1695.TermStructuralFrom Law680 := Confluence680Recovery.not_termStructural

/-- info: 'Equation1695_not_termStructuralFrom_Equation680_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1695_not_termStructuralFrom_Equation680_confluence

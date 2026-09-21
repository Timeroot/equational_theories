import equational_theories.Definability.PointedConfluence481
import equational_theories.Definability.ConfluenceCrossedInverse

/-! The pointed E481 normal-form model has only identity-or-zero unary term
endomorphisms at a generator. Left cubing in E1492 and E4273 must therefore be
identity-or-zero in any reversible companion. On the Gaussian quotient, this
forces real coefficients and prevents recovery of i*(x-y). E1496 is excluded
already by its Gaussian coefficient equations. -/

open FreeMagma Confluence FirstOrder Law Law.MagmaLaw
namespace Confluence481Recovery
open PointedConfluence481

abbrev X := G (α := GaussianInt)
@[reducible] def base : Magma GaussianInt := Magma.lin Magma.gi (-Magma.gi)

def ev : FreeMagma (Option GaussianInt) → GaussianInt :=
  @evalInMagma _ _ base (fun x => x.getD 0)

@[simp] theorem ev_fork (s t : FreeMagma (Option GaussianInt)) :
    ev (s ⋆ t) = base.op (ev s) (ev t) := rfl

@[simp] theorem ev_zero : ev (zero : FreeMagma (Option GaussianInt)) = 0 := rfl

theorem ev_rule (t : FreeMagma (Option GaussianInt)) : ev (rules t) = ev t := by
  generalize hr : rules t = r
  rcases (rules.elim t r).mp hr with (h | h | h) | h
  · obtain ⟨x, y, ht, he⟩ := h
    rw [ht, he]
    simp only [ev_fork, show ev (.Leaf none) = 0 from rfl, Magma.lin_op]
    linear_combination (ev x - Magma.gi * ev y) * Magma.gi_sq
  · obtain ⟨x, ht, he⟩ := h
    rw [ht, he]
    simp only [ev_fork, show ev (.Leaf none) = 0 from rfl, Magma.lin_op]
    linear_combination ev x * Magma.gi_sq
  · obtain ⟨x, ht, he⟩ := h
    rw [ht, he]
    simp only [ev_fork, Magma.lin_op]
    change 0 = _
    ring
  · obtain ⟨rfl, _⟩ := h
    rfl

theorem ev_bu (t : FreeMagma (Option GaussianInt)) : ev (bu rules t) = ev t := by
  induction t with
  | Leaf => rfl
  | Fork x y hx hy => rw [bu, ev_rule, ev_fork, hx, hy, ev_fork]

def quotient (x : X) : GaussianInt := ev x.val

theorem quotient_hom (x y : X) : quotient (x ◇ y) = base.op (quotient x) (quotient y) := by
  change ev (bu rules (x.val ⋆ y.val)) = _
  rw [ev_bu]
  rfl

theorem quotient_surjective : Function.Surjective quotient := fun x => ⟨point x, rfl⟩

theorem cube_hom1496 {Y : Type} (M : Magma Y) (h : @Equation1496 Y M) :
    ∀ x y, M.op (M.op x y) (M.op (M.op x y) (M.op x y)) =
      M.op (M.op x (M.op x x)) (M.op y (M.op y y)) :=
  Confluence477Recovery.left_cube_hom1492 M (fun x y => h x y y)

theorem gaussian_obstruction (a b : GaussianInt) (h : @Equation1496 GaussianInt (Magma.lin a b))
    (hc : a + b * (a + b) = 1 ∨ a + b * (a + b) = 0) : False := by
  have h1 : a * b = 1 := by
    have := h 1 0 0
    simp only [Magma.lin_op] at this
    linear_combination -this
  have h2 : b ^ 2 * (a + b) = 0 := by
    have := h 0 0 1
    simp only [Magma.lin_op] at this
    linear_combination -this
  have ha : IsUnit a := isUnit_iff_exists_inv.mpr ⟨b, h1⟩
  have hb : IsUnit b := isUnit_iff_exists_inv.mpr ⟨a, by simpa [mul_comm] using h1⟩
  rcases GaussianRecovery.unit_cases a ha with rfl | rfl | rfl | rfl <;>
    rcases GaussianRecovery.unit_cases b hb with rfl | rfl | rfl | rfl <;>
    revert h1 h2 hc <;> decide

theorem cube_quotient {β : Type} (L : MagmaLaw β)
    (h : L.TermStructuralOnMagma (inferInstance : Magma X))
    (hh : ∀ (N : Magma X), @satisfies _ X N L →
      ∀ x y, N.op (N.op x y) (N.op (N.op x y) (N.op x y)) =
        N.op (N.op x (N.op x x)) (N.op y (N.op y y))) :
    ∃ Nq : Magma GaussianInt, @satisfies _ GaussianInt Nq L ∧
      @Set.TermDefinable GaussianInt ∅ MagmaLanguage base.FOStructure (Fin 2) Nq.FinArityOp ∧
      @Set.TermDefinable GaussianInt ∅ MagmaLanguage Nq.FOStructure (Fin 2) base.FinArityOp ∧
      (Nq.op 1 (Nq.op 1 1) = 1 ∨ Nq.op 1 (Nq.op 1 1) = 0) := by
  obtain ⟨N, hN, hfwd, hback⟩ := h
  let B : Magma X := ⟨fun x _ => N.op x (N.op x x)⟩
  have hbdef : @Set.TermDefinable X ∅ MagmaLanguage N.FOStructure (Fin 2) B.FinArityOp :=
    TermRecoveryHom.termMagma_definable N
      ((.Leaf (0 : Fin 2) ⋆ (.Leaf 0 ⋆ .Leaf 0)).toTerm)
  have hbg := (good_invariant (1 : GaussianInt) 2 (by decide)).of_termDefinable
    (TermDefinable.trans_aux hfwd hbdef)
  have hbh := (FreeUnary115.hom_invariant N (fun x => N.op x (N.op x x))
    (hh N hN)).of_termDefinable hback
  have hfix := endomorphism_at_point 1 2 (by decide) B.op hbg hbh
  obtain ⟨Nq, hNq, hfwq, hbackq, hmap⟩ := TermRecoveryHom.transfer_companion
    (Confluence.instMagmaConfMagma rules) base quotient quotient_hom quotient_surjective
    L N hN hfwd hback
  have hc : Nq.op 1 (Nq.op 1 1) = 1 ∨ Nq.op 1 (Nq.op 1 1) = 0 := by
    rcases hfix with hh | hh
    · left
      have he := congrArg quotient hh
      change quotient (N.op _ (N.op _ _)) = 1 at he
      simpa only [hmap, show quotient (point 1) = 1 from rfl] using he
    · right
      have he := congrArg quotient hh
      change quotient (N.op _ (N.op _ _)) = 0 at he
      simpa only [hmap, show quotient (point 1) = 1 from rfl] using he
  exact ⟨Nq, hNq, hfwq, hbackq, hc⟩

theorem not_termStructural : ¬ Law1496.TermStructuralFrom Law481 := by
  intro h
  obtain ⟨Nq, hNq, hfwq, _, hc⟩ := cube_quotient Law1496
    (h _ ((@Law481.models_iff X inferInstance).mpr source_law))
    (fun N hN => cube_hom1496 N ((@Law1496.models_iff X N).mp hN))
  obtain ⟨a, b, _, hop, _⟩ :=
    (Magma.lin_isCloneInvariant Magma.gi (-Magma.gi) (-1) 1 (by ring)).of_termDefinable hfwq
  have hEq : Nq = Magma.lin a b := by
    cases Nq
    exact congrArg Magma.mk (funext fun x => funext fun y => hop x y)
  subst Nq
  apply gaussian_obstruction a b ((@Law1496.models_iff GaussianInt (Magma.lin a b)).mp hNq)
  simpa only [Magma.lin_op, mul_one] using hc


theorem gaussian_trap1492 (a b : GaussianInt) (h : @Equation1492 GaussianInt (Magma.lin a b))
    (hc : a + b * (a + b) = 1 ∨ a + b * (a + b) = 0) : GaussianRecovery.Trapped a b := by
  have h1 : a * b = 1 := by
    have := h 1 0
    simp only [Magma.lin_op] at this
    linear_combination -this
  have h2 : a ^ 2 + b * (a + b * (a + b)) = 0 := by
    have := h 0 1
    simp only [Magma.lin_op] at this
    linear_combination -this
  have ha : IsUnit a := isUnit_iff_exists_inv.mpr ⟨b, h1⟩
  have hb : IsUnit b := isUnit_iff_exists_inv.mpr ⟨a, by simpa [mul_comm] using h1⟩
  rcases GaussianRecovery.unit_cases a ha with rfl | rfl | rfl | rfl <;>
    rcases GaussianRecovery.unit_cases b hb with rfl | rfl | rfl | rfl <;>
    revert h1 h2 hc <;> decide

theorem gaussian_trap4273 (a b : GaussianInt) (h : @Equation4273 GaussianInt (Magma.lin a b))
    (hc : a + b * (a + b) = 1 ∨ a + b * (a + b) = 0) : GaussianRecovery.Trapped a b := by
  have h1 : a + b ^ 2 = 0 := by
    have := h 0 1
    simp only [Magma.lin_op] at this
    linear_combination -this
  have h2 : a * b = 1 ∨ a * b = 0 := by
    rcases hc with hc | hc
    · left; linear_combination hc - h1
    · right; linear_combination hc - h1
  rcases h2 with h2 | h2
  · have ha : IsUnit a := isUnit_iff_exists_inv.mpr ⟨b, h2⟩
    have hb : IsUnit b := isUnit_iff_exists_inv.mpr ⟨a, by simpa [mul_comm] using h2⟩
    rcases GaussianRecovery.unit_cases a ha with rfl | rfl | rfl | rfl <;>
      rcases GaussianRecovery.unit_cases b hb with rfl | rfl | rfl | rfl <;>
      revert h1 h2 <;> decide
  · rcases mul_eq_zero.mp h2 with ha | hb
    · subst a
      have hb : b = 0 := eq_zero_of_pow_eq_zero (n := 2) (by simpa only [zero_add] using h1)
      subst b
      decide
    · subst b
      have ha : a = 0 := by simpa using h1
      subst a
      decide

theorem not1492 : ¬ Law1492.TermStructuralFrom Law481 := by
  intro h
  obtain ⟨Nq, hNq, hfwq, hbackq, hc⟩ := cube_quotient Law1492
    (h _ ((@Law481.models_iff X inferInstance).mpr source_law))
    (fun N hN => Confluence477Recovery.left_cube_hom1492 N ((@Law1492.models_iff X N).mp hN))
  obtain ⟨a, b, _, hop, _⟩ :=
    (Magma.lin_isCloneInvariant Magma.gi (-Magma.gi) (-1) 1 (by ring)).of_termDefinable hfwq
  have hEq : Nq = Magma.lin a b := by
    cases Nq
    exact congrArg Magma.mk (funext fun x => funext fun y => hop x y)
  subst Nq
  exact GaussianRecovery.no_recovery a b
    (gaussian_trap1492 a b ((@Law1492.models_iff GaussianInt (Magma.lin a b)).mp hNq)
      (by simpa only [Magma.lin_op, mul_one] using hc)) hbackq

theorem not4273 : ¬ Law4273.TermStructuralFrom Law481 := by
  intro h
  obtain ⟨Nq, hNq, hfwq, hbackq, hc⟩ := cube_quotient Law4273
    (h _ ((@Law481.models_iff X inferInstance).mpr source_law))
    (fun N hN => ConfluenceCrossedInverse.cube_hom4273 N ((@Law4273.models_iff X N).mp hN))
  obtain ⟨a, b, _, hop, _⟩ :=
    (Magma.lin_isCloneInvariant Magma.gi (-Magma.gi) (-1) 1 (by ring)).of_termDefinable hfwq
  have hEq : Nq = Magma.lin a b := by
    cases Nq
    exact congrArg Magma.mk (funext fun x => funext fun y => hop x y)
  subst Nq
  exact GaussianRecovery.no_recovery a b
    (gaussian_trap4273 a b ((@Law4273.models_iff GaussianInt (Magma.lin a b)).mp hNq)
      (by simpa only [Magma.lin_op, mul_one] using hc)) hbackq

end Confluence481Recovery

open Law Law.MagmaLaw

theorem Equation1496_not_termStructuralFrom_Equation481_confluence :
    ¬ Law1496.TermStructuralFrom Law481 := Confluence481Recovery.not_termStructural

/-- info: 'Equation1496_not_termStructuralFrom_Equation481_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1496_not_termStructuralFrom_Equation481_confluence


theorem Equation1492_not_termStructuralFrom_Equation481_confluence :
    ¬ Law1492.TermStructuralFrom Law481 := Confluence481Recovery.not1492

theorem Equation4273_not_termStructuralFrom_Equation481_confluence :
    ¬ Law4273.TermStructuralFrom Law481 := Confluence481Recovery.not4273

/-- info: 'Equation1492_not_termStructuralFrom_Equation481_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1492_not_termStructuralFrom_Equation481_confluence

/-- info: 'Equation4273_not_termStructuralFrom_Equation481_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4273_not_termStructuralFrom_Equation481_confluence

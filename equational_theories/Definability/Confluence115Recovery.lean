import equational_theories.Confluence2
import equational_theories.Definability.Invariant

/-!
The confluent E115 model admits no nonidentity unary term endomorphism.
A term evaluated at two distinct generators and their product has the same
normal-form shape in all three positions. An endomorphism must preserve that
product, which is incompatible with any nontrivial shape.

Squaring is an endomorphism in E880. Mutual term recovery would therefore make
the E880 square fix a source generator, forcing the recovered source operation
to be idempotent there. The free E115 operation is not idempotent.
-/

open FreeMagma Confluence
namespace FreeUnary115

def copy {α : Type} (p : FreeMagma α) : FreeMagma Unit → FreeMagma α
  | .Leaf _ => p
  | .Fork a b => .Fork (copy p a) (copy p b)

@[simp] theorem copy_fork {α} (p : FreeMagma α) (a b : FreeMagma Unit) :
    copy p (a ⋆ b) = copy p a ⋆ copy p b := rfl

@[simp] theorem length_copy {α} (p : FreeMagma α) (a : FreeMagma Unit) :
    (copy p a).length = p.length * a.length := by
  induction a with
  | Leaf => simp [copy]
  | Fork a b ha hb => simp [copy, ha, hb, Nat.mul_add]

theorem length_copy_ge {α} (p : FreeMagma α) (a : FreeMagma Unit) :
    p.length ≤ (copy p a).length := by
  rw [length_copy]
  exact Nat.le_mul_of_pos_right _ a.length_pos

theorem copy_injective {α} (p : FreeMagma α) : Function.Injective (copy p) := by
  intro a
  induction a with
  | Leaf a =>
    intro b h
    cases b with
    | Leaf b => rfl
    | Fork b c =>
      have he := congrArg FreeMagma.length h
      have hp := p.length_pos
      have hb := length_copy_ge p b
      have hc := length_copy_ge p c
      simp only [copy, length] at he
      omega
  | Fork a b ha hb =>
    intro c h
    cases c with
    | Leaf c =>
      have he := congrArg FreeMagma.length h
      have hp := p.length_pos
      have ha := length_copy_ge p a
      have hb := length_copy_ge p b
      simp only [copy, length] at he
      omega
    | Fork c d =>
      obtain ⟨hc, hd⟩ := FreeMagma.Fork.inj h
      rw [ha hc, hb hd]

theorem copy_not_fork_left {α} (p : FreeMagma α) (a : FreeMagma Unit) (b : FreeMagma α) :
    p ≠ copy p a ⋆ b := by
  intro h
  have he := congrArg FreeMagma.length h
  have ha := length_copy_ge p a
  have hb := b.length_pos
  simp only [length] at he
  omega

theorem copy_not_fork_right {α} (p : FreeMagma α) (a : FreeMagma Unit) (b : FreeMagma α) :
    p ≠ b ⋆ copy p a := by
  intro h
  have he := congrArg FreeMagma.length h
  have ha := length_copy_ge p a
  have hb := b.length_pos
  simp only [length] at he
  omega

theorem copy_square {α} (p : FreeMagma α) (hp : ∀ a, p ≠ a ⋆ a)
    (t : FreeMagma Unit) (a : FreeMagma α) (h : copy p t = a ⋆ a) :
    ∃ u, t = u ⋆ u ∧ a = copy p u := by
  cases t with
  | Leaf => exact (hp a h).elim
  | Fork u v =>
    obtain ⟨hu, hv⟩ := FreeMagma.Fork.inj h
    have huv := copy_injective p (hu.trans hv.symm)
    exact ⟨u, by rw [huv], hu.symm⟩

theorem copy_rule1 {α} (p : FreeMagma α) (hp : p.length ≤ 2)
    (hs : ∀ a, p ≠ a ⋆ a) (t : FreeMagma Unit) (x y : FreeMagma α)
    (h : copy p t = y ⋆ ((x ⋆ x) ⋆ y)) :
    ∃ a b, t = b ⋆ ((a ⋆ a) ⋆ b) ∧ x = copy p a ∧ y = copy p b := by
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
    | Leaf => exact (copy_not_fork_right p a (x ⋆ x) (hb.trans (by rw [ha]))).elim
    | Fork c d =>
      obtain ⟨hc, hd⟩ := FreeMagma.Fork.inj hb
      obtain ⟨v, rfl, hx⟩ := copy_square p hs c x hc
      have had := copy_injective p (ha.trans hd.symm)
      exact ⟨v, a, by rw [had], hx, ha.symm⟩

theorem copy_rule2 {α} (p : FreeMagma α) (hp : p.length ≤ 2)
    (hs : ∀ a, p ≠ a ⋆ a) (t : FreeMagma Unit) (x y : FreeMagma α)
    (h : copy p t = ((y ⋆ y) ⋆ (x ⋆ x)) ⋆ y) :
    ∃ a b, t = ((b ⋆ b) ⋆ (a ⋆ a)) ⋆ b ∧ x = copy p a ∧ y = copy p b := by
  cases t with
  | Leaf =>
    have he := congrArg FreeMagma.length h
    have hx := x.length_pos
    have hy := y.length_pos
    simp only [copy, length] at he
    omega
  | Fork a b =>
    obtain ⟨ha, hb⟩ := FreeMagma.Fork.inj h
    cases a with
    | Leaf =>
      have he := congrArg FreeMagma.length ha
      have hh := length_copy_ge p b
      have hx := x.length_pos
      rw [hb] at hh
      simp only [copy, length] at he
      omega
    | Fork c d =>
      obtain ⟨hc, hd⟩ := FreeMagma.Fork.inj ha
      obtain ⟨v, rfl, hy⟩ := copy_square p hs c y hc
      obtain ⟨w, rfl, hx⟩ := copy_square p hs d x hd
      have hvb := copy_injective p (hy.symm.trans hb.symm)
      exact ⟨w, b, by rw [hvb], hx, hb.symm⟩

theorem rules_copy {α} [DecidableEq α] (p : FreeMagma α) (hp : p.length ≤ 2)
    (hs : ∀ a, p ≠ a ⋆ a) (t : FreeMagma Unit) :
    rw115.rules (copy p t) = copy p (rw115.rules t) := by
  generalize hr : rw115.rules t = r
  rcases (rw115.rules.elim t r).mp hr with (h | h) | h
  · obtain ⟨x, y, rfl, he⟩ := h
    rw [he]
    exact rw115.rules.eq1 _ _
  · obtain ⟨x, y, rfl, he⟩ := h
    rw [he]
    exact rw115.rules.eq2 _ _
  · obtain ⟨ht, h1, h2⟩ := h
    rw [← ht]
    apply (rw115.rules.elim _ _).mpr
    refine Or.inr ⟨rfl, ?_, ?_⟩
    · rintro ⟨x, y, he⟩
      obtain ⟨a, b, ha, _, _⟩ := copy_rule1 p hp hs t x y he
      exact h1 ⟨a, b, ha⟩
    · rintro ⟨x, y, he⟩
      obtain ⟨a, b, ha, _, _⟩ := copy_rule2 p hp hs t x y he
      exact h2 ⟨a, b, ha⟩

theorem bu_copy {α} [DecidableEq α] (p : FreeMagma α) (hp : p.length ≤ 2)
    (hs : ∀ a, p ≠ a ⋆ a) (hn : bu rw115.rules p = p) (t : FreeMagma Unit) :
    bu rw115.rules (copy p t) = copy p (bu rw115.rules t) := by
  induction t with
  | Leaf => simpa [copy] using hn
  | Fork a b ha hb =>
    change rw115.rules (bu rw115.rules (copy p a) ⋆ bu rw115.rules (copy p b)) =
      copy p (rw115.rules (bu rw115.rules a ⋆ bu rw115.rules b))
    rw [ha, hb]
    exact rules_copy p hp hs (bu rw115.rules a ⋆ bu rw115.rules b)

def first {α} : FreeMagma α → α
  | .Leaf a => a
  | .Fork a _ => first a

def last {α} : FreeMagma α → α
  | .Leaf a => a
  | .Fork _ b => last b

@[simp] theorem first_copy {α} (p : FreeMagma α) (t : FreeMagma Unit) :
    first (copy p t) = first p := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb => exact ha

@[simp] theorem last_copy {α} (p : FreeMagma α) (t : FreeMagma Unit) :
    last (copy p t) = last p := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb => exact hb

def leaf (i : Bool) : FreeMagma Bool := .Leaf i
def pair : FreeMagma Bool := leaf false ⋆ leaf true

theorem leaf_not_square (i : Bool) (a : FreeMagma Bool) : leaf i ≠ a ⋆ a := by
  intro h; cases h

theorem pair_not_square (a : FreeMagma Bool) : pair ≠ a ⋆ a := by
  intro h
  obtain ⟨h1, h2⟩ := FreeMagma.Fork.inj h
  have he := h1.trans h2.symm
  cases he

@[simp] theorem bu_copy_leaf (i : Bool) (t : FreeMagma Unit) :
    bu rw115.rules (copy (leaf i) t) = copy (leaf i) (bu rw115.rules t) :=
  bu_copy (leaf i) (by simp [leaf]) (leaf_not_square i) rfl t

@[simp] theorem bu_copy_pair (t : FreeMagma Unit) :
    bu rw115.rules (copy pair t) = copy pair (bu rw115.rules t) :=
  bu_copy pair (by decide) pair_not_square rfl t

theorem rules_mixed (s t : FreeMagma Unit) :
    rw115.rules (copy (leaf false) s ⋆ copy (leaf true) t) =
      copy (leaf false) s ⋆ copy (leaf true) t := by
  apply (rw115.rules.elim _ _).mpr
  refine Or.inr ⟨rfl, ?_, ?_⟩
  · rintro ⟨x, y, he⟩
    obtain ⟨hl, hr⟩ := FreeMagma.Fork.inj he
    have h1 := congrArg last hl
    have h2 := congrArg last hr
    simp only [last_copy, last, leaf] at h1 h2
    exact Bool.false_ne_true (h1.trans h2.symm)
  · rintro ⟨x, y, he⟩
    obtain ⟨hl, hr⟩ := FreeMagma.Fork.inj he
    have h1 := congrArg first hl
    have h2 := congrArg first hr
    simp only [first_copy, first, leaf] at h1 h2
    exact Bool.false_ne_true (h1.trans h2.symm)

abbrev G := ConfMagma (@rw115.rules Bool _)
def a : G := ⟨leaf false, rfl⟩
def b : G := ⟨leaf true, rfl⟩
def ab : G := ⟨pair, rfl⟩

def Good (f : G → G → G) : Prop :=
  ∃ t : FreeMagma Unit,
    (f a a).val = copy (leaf false) t ∧
    (f b b).val = copy (leaf true) t ∧
    (f ab ab).val = copy pair t

theorem good_invariant : (inferInstance : Magma G).IsCloneInvariant Good where
  fst := ⟨.Leaf (), rfl, rfl, rfl⟩
  snd := ⟨.Leaf (), rfl, rfl, rfl⟩
  comp := by
    rintro f g ⟨s, hs0, hs1, hsp⟩ ⟨t, ht0, ht1, htp⟩
    refine ⟨bu rw115.rules (s ⋆ t), ?_, ?_, ?_⟩
    · change bu rw115.rules ((f a a).val ⋆ (g a a).val) = _
      rw [hs0, ht0, ← copy_fork, bu_copy_leaf]
    · change bu rw115.rules ((f b b).val ⋆ (g b b).val) = _
      rw [hs1, ht1, ← copy_fork, bu_copy_leaf]
    · change bu rw115.rules ((f ab ab).val ⋆ (g ab ab).val) = _
      rw [hsp, htp, ← copy_fork, bu_copy_pair]

theorem good_endomorphism_fixes (f : G → G → G) (hf : Good f)
    (he : ∀ x y : G, f (x ◇ y) (x ◇ y) = f x x ◇ f y y) : f a a = a := by
  obtain ⟨t, ht0, ht1, htp⟩ := hf
  have h := congrArg Subtype.val (he a b)
  change (f ab ab).val = bu rw115.rules ((f a a).val ⋆ (f b b).val) at h
  rw [bu_op_eq_rw_op rw115.rules (f a a).property (f b b).property] at h
  rw [ht0, ht1, htp, rules_mixed] at h
  cases t with
  | Leaf u => exact Subtype.ext ht0
  | Fork s t =>
    obtain ⟨hl, _⟩ := FreeMagma.Fork.inj h
    have hh := congrArg last hl
    simp only [last_copy, pair, leaf, last] at hh
    cases hh

open FirstOrder Law Law.MagmaLaw

section Endomorphism
variable {X : Type} (M : Magma X) (f : X → X)

theorem hom_invariant (hf : ∀ x y, f (M.op x y) = M.op (f x) (f y)) :
    M.IsCloneInvariant (fun g => ∀ x y, f (g x y) = g (f x) (f y)) where
  fst := fun _ _ => rfl
  snd := fun _ _ => rfl
  comp := by
    intro g k hg hk x y
    rw [hf, hg, hk]

theorem fixed_invariant (x : X) (hx : M.op x x = x) :
    M.IsCloneInvariant (fun g => g x x = x) where
  fst := rfl
  snd := rfl
  comp := by
    intro g k hg hk
    change M.op (g x x) (k x x) = x
    rw [hg, hk, hx]
end Endomorphism

theorem square_hom880 {X : Type} (M : Magma X) (h : @Equation880 X M) :
    ∀ x y, M.op (M.op x y) (M.op x y) = M.op (M.op x x) (M.op y y) := by
  intro x y
  have h1 := h x y
  have h2 := h y (M.op (M.op x y) (M.op x y))
  have h3 := h (M.op (M.op x y) (M.op x y)) (M.op x x)
  grind

theorem source_law : @Equation115 G inferInstance := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  simp only [Magma.op, bu, hx, hy, buFixed_rw_op]
  symm
  apply Subtype.ext
  apply rw115.comp3 ((NF_iff_buFixed rw115.rules).mpr hx)

theorem not_termStructural : ¬ Law880.TermStructuralFrom Law115 := by
  intro h
  obtain ⟨N, hN, hf, hb⟩ := h (inferInstance : Magma G)
    ((@Law115.models_iff G inferInstance).mpr source_law)
  have hh := (hom_invariant N (fun x => N.op x x)
    (square_hom880 N ((@Law880.models_iff G N).mp hN))).of_termDefinable hb
  have ha := good_endomorphism_fixes N.op (good_invariant.of_termDefinable hf) hh
  have he := (fixed_invariant N a ha).of_termDefinable hb
  have bad := congrArg Subtype.val he
  cases bad

end FreeUnary115

open Law Law.MagmaLaw

theorem Equation880_not_termStructuralFrom_Equation115_confluence :
    ¬ Law880.TermStructuralFrom Law115 := FreeUnary115.not_termStructural

/-- info: 'Equation880_not_termStructuralFrom_Equation115_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation880_not_termStructuralFrom_Equation115_confluence

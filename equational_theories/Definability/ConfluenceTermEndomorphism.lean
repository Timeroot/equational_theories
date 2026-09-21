import equational_theories.Definability.Confluence115Recovery

/-! A criterion making unary term endomorphisms trivial in a normal-form magma.
Substitution by one leaf or a pair of distinct leaves must commute with
normalization. Comparing the two substitutions forces the unary normal form
to be a variable. Preservation of multiplication then fixes every normal form. -/

open FreeMagma Confluence
namespace ConfluenceTermEndomorphism
open FreeUnary115 (copy first last)

variable {α : Type} (r : FreeMagma α → FreeMagma α)
  [IsProjOrNF r] (u : FreeMagma Unit → FreeMagma Unit)

abbrev G := ConfMagma r

def Small (p : FreeMagma α) : Prop :=
  p.length ≤ 2 ∧ (∀ a, p ≠ a ⋆ a) ∧ bu r p = p

def Good (f : G r → G r → G r) : Prop :=
  ∃ t : FreeMagma Unit, ∀ p (hp : Small r p),
    (f ⟨p, hp.2.2⟩ ⟨p, hp.2.2⟩).val = copy p t

variable (hc : ∀ p, Small r p → ∀ t, bu r (copy p t) = copy p (bu u t))

include hc in
theorem good_invariant : (inferInstance : Magma (G r)).IsCloneInvariant (Good r) where
  fst := ⟨.Leaf (), fun _ _ => rfl⟩
  snd := ⟨.Leaf (), fun _ _ => rfl⟩
  comp := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨bu u (s ⋆ t), ?_⟩
    intro p hp
    change bu r ((f ⟨p, hp.2.2⟩ ⟨p, hp.2.2⟩).val ⋆
      (g ⟨p, hp.2.2⟩ ⟨p, hp.2.2⟩).val) = _
    rw [hs p hp, ht p hp]
    exact hc p hp (s ⋆ t)

omit [IsProjOrNF r] in
theorem leaf_small (h : ∀ a, bu r (.Leaf a) = .Leaf a) (a : α) :
    Small r (.Leaf a) := by
  refine ⟨by simp, ?_, h a⟩
  intro b he
  cases he

theorem fixed_by_endomorphism
    (hl : ∀ a, bu r (.Leaf a) = .Leaf a)
    (a b : α) (hab : a ≠ b)
    (hp : bu r (.Leaf a ⋆ .Leaf b) = .Leaf a ⋆ .Leaf b)
    (hm : ∀ s t : FreeMagma Unit,
      r (copy (.Leaf a) s ⋆ copy (.Leaf b) t) = copy (.Leaf a) s ⋆ copy (.Leaf b) t)
    (f : G r → G r → G r) (hg : Good r f)
    (hf : ∀ x y : G r, f (x ◇ y) (x ◇ y) = f x x ◇ f y y) :
    ∀ x, f x x = x := by
  obtain ⟨t, ht⟩ := hg
  have hps : Small r (.Leaf a ⋆ .Leaf b) := by
    refine ⟨by simp, ?_, hp⟩
    intro c he
    obtain ⟨h1, h2⟩ := FreeMagma.Fork.inj he
    exact hab (FreeMagma.Leaf.inj (h1.trans h2.symm))
  let x : G r := ⟨.Leaf a, hl a⟩
  let y : G r := ⟨.Leaf b, hl b⟩
  have hxy : x ◇ y = ⟨.Leaf a ⋆ .Leaf b, hp⟩ := Subtype.ext hp
  have he := congrArg Subtype.val (hf x y)
  rw [hxy] at he
  change (f ⟨.Leaf a ⋆ .Leaf b, hp⟩ ⟨.Leaf a ⋆ .Leaf b, hp⟩).val =
    bu r ((f x x).val ⋆ (f y y).val) at he
  rw [bu_op_eq_rw_op r (f x x).property (f y y).property] at he
  rw [ht _ hps, ht _ (leaf_small r hl a), ht _ (leaf_small r hl b), hm] at he
  have htleaf : t = .Leaf () := by
    cases t with
    | Leaf z => rfl
    | Fork s t =>
      obtain ⟨hleft, _⟩ := FreeMagma.Fork.inj he
      have hh := congrArg FreeUnary115.last hleft
      simp only [FreeUnary115.last_copy, FreeUnary115.last] at hh
      exact (hab hh.symm).elim
  subst t
  have hfix : ∀ a, f ⟨.Leaf a, hl a⟩ ⟨.Leaf a, hl a⟩ = ⟨.Leaf a, hl a⟩ := by
    intro a
    exact Subtype.ext (ht _ (leaf_small r hl a))
  have hnorm : ∀ t : FreeMagma α,
      f ⟨bu r t, bu_idem r t⟩ ⟨bu r t, bu_idem r t⟩ = ⟨bu r t, bu_idem r t⟩ := by
    intro t
    induction t with
    | Leaf a => simpa only [hl a] using hfix a
    | Fork s t hs ht =>
      have he : (⟨bu r (s ⋆ t), bu_idem r (s ⋆ t)⟩ : G r) =
          @Magma.op (G r) inferInstance ⟨bu r s, bu_idem r s⟩ ⟨bu r t, bu_idem r t⟩ := by
        apply Subtype.ext
        simp only [Magma.op, bu, bu_idem]
      rw [he, hf, hs, ht]
  intro ⟨x, hx⟩
  simpa only [hx] using hnorm x

end ConfluenceTermEndomorphism

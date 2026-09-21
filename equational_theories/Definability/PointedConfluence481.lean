import equational_theories.ConfluenceSystem
import equational_theories.Definability.Invariant

/-! A pointed normal-form E481 magma. Substitution of either a generator or a
pair of distinct generators commutes with normalization. Consequently any unary
term endomorphism sends a generator either to itself or to the common square. -/

open FreeMagma Confluence
namespace PointedConfluence481
variable {α : Type} [DecidableEq α]

def zero : FreeMagma (Option α) := .Leaf none

rule_system rules {x y : FreeMagma (Option α)} -IsProj
  | y ⋆ (x ⋆ (y ⋆ .Leaf none)) => x
  | .Leaf none ⋆ (x ⋆ .Leaf none) => x
  | x ⋆ x => .Leaf none

instance : IsProjOrNF (@rules α _) where
  proj_or_nf t := by
    generalize hr : rules t = r
    rcases (rules.elim t r).mp hr with (h | h | h) | h
    · obtain ⟨x, y, rfl, rfl⟩ := h
      exact Or.inl (by subterm)
    · obtain ⟨x, rfl, rfl⟩ := h
      exact Or.inl (by subterm)
    · obtain ⟨x, rfl, rfl⟩ := h
      exact Or.inr (by rfl)
    · obtain ⟨rfl, _⟩ := h
      exact Or.inl (SubtermOf.refl _)

theorem rule_square (x : FreeMagma (Option α)) : rules (x ⋆ x) = zero := rules.eq3 x

theorem rule_right_zero (x : FreeMagma (Option α)) :
    rules (x ⋆ zero) = if x = zero then zero else x ⋆ zero := by
  simp only [rules, rules.rule1, rules.rule2, rules.rule3, zero]
  split <;> simp_all

theorem comp1 (x y : FreeMagma (Option α)) (hx : NF rules x) :
    rules (y ⋆ rules (x ⋆ (y ⋆ zero))) = x := by
  generalize hr : rules (x ⋆ (y ⋆ zero)) = r
  rcases (rules.elim _ _).mp hr with (h | h | h) | h
  · obtain ⟨a, b, he, he'⟩ := h
    simp only [zero, FreeMagma.Fork.injEq] at he
    have hz := he.2.2
    cases hz
  · obtain ⟨a, he, he'⟩ := h
    simp only [zero, FreeMagma.Fork.injEq] at he
    have hx0 : x = zero := he.1
    have hya : y = a := he.2.1
    rw [he', ← hya, rule_square, hx0]
  · obtain ⟨a, he, he'⟩ := h
    obtain ⟨hx1, hy1⟩ := FreeMagma.Fork.inj he
    have hxy : y ⋆ zero = x := hy1.trans hx1.symm
    rw [he', show (.Leaf none : FreeMagma (Option α)) = zero from rfl, hxy]
    exact rw_eq_self_of_NF rules hx
  · obtain ⟨he, _⟩ := h
    rw [← he]
    exact rules.eq1 _ _

theorem comp_zero (x : FreeMagma (Option α)) :
    rules (zero ⋆ rules (x ⋆ zero)) = x := by
  rw [rule_right_zero]
  split
  · rename_i hx
    subst x
    exact rules.eq3 _
  · exact rules.eq2 x

theorem comp2 (x y : FreeMagma (Option α)) (hx : NF rules x) :
    rules (y ⋆ rules (x ⋆ rules (y ⋆ zero))) = x := by
  rw [rule_right_zero]
  split
  · rename_i hy
    subst y
    exact comp_zero x
  · exact comp1 x y hx

@[simp] theorem bu_zero : bu rules (zero : FreeMagma (Option α)) = zero := rfl

abbrev G := ConfMagma (@rules α _)

theorem source_law : @Equation481 (G (α := α)) inferInstance := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
  have hzero : bu rules (zero : FreeMagma (Option α)) = zero := rfl
  simp (disch := bufixed) only [Magma.op, bu, hx, hy, hz, buFixed_rw_op, rule_square, bu_zero]
  symm
  apply Subtype.ext
  apply comp2 x y ((NF_iff_buFixed rules).mpr hx)

def plug (p : FreeMagma (Option α)) : FreeMagma (Option Unit) → FreeMagma (Option α)
  | .Leaf none => zero
  | .Leaf (some _) => p
  | .Fork a b => plug p a ⋆ plug p b

omit [DecidableEq α] in
@[simp] theorem plug_fork (p : FreeMagma (Option α)) (a b : FreeMagma (Option Unit)) :
    plug p (a ⋆ b) = plug p a ⋆ plug p b := rfl

def atom (a : α) : FreeMagma (Option α) := .Leaf (some a)
def pair (a b : α) : FreeMagma (Option α) := atom a ⋆ atom b

omit [DecidableEq α] in
theorem plug_injective (p : FreeMagma (Option α)) (hp : p ≠ zero)
    (hn : ∀ s t, p ≠ plug p s ⋆ plug p t) : Function.Injective (plug p) := by
  intro s
  induction s with
  | Leaf a =>
    intro t he
    cases a with
    | none =>
      cases t with
      | Leaf b => cases b <;> simp_all [plug]
      | Fork u v => cases he
    | some a =>
      cases t with
      | Leaf b => cases b <;> simp_all [plug]
      | Fork u v => exact (hn u v he).elim
  | Fork s t hs ht =>
    intro u he
    cases u with
    | Leaf a =>
      cases a with
      | none => cases he
      | some a => exact (hn s t he.symm).elim
    | Fork u v =>
      obtain ⟨h1, h2⟩ := FreeMagma.Fork.inj he
      rw [hs h1, ht h2]

omit [DecidableEq α] in
theorem plug_atom_injective (a : α) : Function.Injective (plug (atom a)) :=
  plug_injective _ (by intro h; cases h) (by intro s t h; cases h)

omit [DecidableEq α] in
theorem plug_pair_ne_atom (a b c : α) (t : FreeMagma (Option Unit)) :
    plug (pair a b) t ≠ atom c := by
  cases t with
  | Leaf v => cases v <;> intro h <;> cases h
  | Fork s t => intro h; cases h

omit [DecidableEq α] in
theorem plug_pair_injective (a b : α) : Function.Injective (plug (pair a b)) := by
  apply plug_injective _ (by intro h; cases h)
  intro s t he
  have h1 := (FreeMagma.Fork.inj he).1
  exact plug_pair_ne_atom a b a s h1.symm

def occurs (a : Option α) : FreeMagma (Option α) → Prop
  | .Leaf b => a = b
  | .Fork s t => occurs a s ∨ occurs a t

def HasVar (t : FreeMagma (Option Unit)) := occurs (some ()) t

omit [DecidableEq α] in
theorem occurs_plug (p : FreeMagma (Option α)) (t : FreeMagma (Option Unit)) (a : α) :
    occurs (some a) (plug p t) ↔ occurs (some a) p ∧ HasVar t := by
  induction t with
  | Leaf v => cases v <;> simp [plug, zero, occurs, HasVar]
  | Fork s t hs ht => simp only [plug, occurs, hs, ht, HasVar]; tauto

omit [DecidableEq α] in
theorem plug_square (p : FreeMagma (Option α)) (hi : Function.Injective (plug p))
    (hp : ∀ a, p ≠ a ⋆ a) (t : FreeMagma (Option Unit)) (a : FreeMagma (Option α))
    (he : plug p t = a ⋆ a) : ∃ u, t = u ⋆ u ∧ a = plug p u := by
  cases t with
  | Leaf v => cases v with
    | none => cases he
    | some v => exact (hp a he).elim
  | Fork s t =>
    obtain ⟨h1, h2⟩ := FreeMagma.Fork.inj he
    have hst := hi (h1.trans h2.symm)
    exact ⟨s, by rw [hst], h1.symm⟩

omit [DecidableEq α] in
theorem plug_eq_zero (p : FreeMagma (Option α)) (hp : p ≠ zero)
    (t : FreeMagma (Option Unit)) (he : plug p t = zero) : t = zero := by
  cases t with
  | Leaf v => cases v with
    | none => rfl
    | some v => exact (hp he).elim
  | Fork s t => cases he

omit [DecidableEq α] in
theorem pattern1 (p : FreeMagma (Option α)) (hi : Function.Injective (plug p))
    (hp : p.length ≤ 2) (hz : p ≠ zero) (hn : ¬ occurs none p)
    (t : FreeMagma (Option Unit)) (x y : FreeMagma (Option α))
    (he : plug p t = y ⋆ (x ⋆ (y ⋆ zero))) :
    ∃ a b, t = b ⋆ (a ⋆ (b ⋆ zero)) ∧ x = plug p a ∧ y = plug p b := by
  cases t with
  | Leaf v =>
    cases v with
    | none => cases he
    | some v =>
      have he' := congrArg FreeMagma.length he
      have hx := x.length_pos
      have hy := y.length_pos
      simp only [plug, length, zero] at he'
      omega
  | Fork a b =>
    obtain ⟨ha, hb⟩ := FreeMagma.Fork.inj he
    cases b with
    | Leaf v =>
      cases v with
      | none => cases hb
      | some v =>
        apply False.elim
        apply hn
        rw [show p = x ⋆ (y ⋆ zero) from hb]
        exact Or.inr (Or.inr rfl)
    | Fork c d =>
      obtain ⟨hc, hd⟩ := FreeMagma.Fork.inj hb
      cases d with
      | Leaf v =>
        cases v with
        | none => cases hd
        | some v =>
          apply False.elim
          apply hn
          rw [show p = y ⋆ zero from hd]
          exact Or.inr rfl
      | Fork e f =>
        obtain ⟨he, hf⟩ := FreeMagma.Fork.inj hd
        have hae := hi (ha.trans he.symm)
        have hf0 := plug_eq_zero p hz f hf
        exact ⟨c, a, by rw [hae, hf0], hc.symm, ha.symm⟩

omit [DecidableEq α] in
theorem pattern2 (p : FreeMagma (Option α)) (hp : p.length ≤ 2)
    (hz : p ≠ zero) (hn : ¬ occurs none p) (t : FreeMagma (Option Unit))
    (x : FreeMagma (Option α)) (he : plug p t = zero ⋆ (x ⋆ zero)) :
    ∃ a, t = zero ⋆ (a ⋆ zero) ∧ x = plug p a := by
  cases t with
  | Leaf v =>
    cases v with
    | none => cases he
    | some v =>
      have he' := congrArg FreeMagma.length he
      have hx := x.length_pos
      simp only [plug, length, zero] at he'
      omega
  | Fork a b =>
    obtain ⟨ha, hb⟩ := FreeMagma.Fork.inj he
    have ha0 := plug_eq_zero p hz a ha
    cases b with
    | Leaf v =>
      cases v with
      | none => cases hb
      | some v =>
        apply False.elim
        apply hn
        rw [show p = x ⋆ zero from hb]
        exact Or.inr rfl
    | Fork c d =>
      obtain ⟨hc, hd⟩ := FreeMagma.Fork.inj hb
      have hd0 := plug_eq_zero p hz d hd
      exact ⟨c, by rw [ha0, hd0], hc.symm⟩

theorem rules_plug (p : FreeMagma (Option α)) (hi : Function.Injective (plug p))
    (hp : p.length ≤ 2) (hz : p ≠ zero) (hn : ¬ occurs none p)
    (hs : ∀ a, p ≠ a ⋆ a) (t : FreeMagma (Option Unit)) :
    rules (plug p t) = plug p (rules t) := by
  generalize hr : rules t = r
  rcases (rules.elim t r).mp hr with (h | h | h) | h
  · obtain ⟨x, y, rfl, he⟩ := h
    rw [he]
    exact rules.eq1 _ _
  · obtain ⟨x, rfl, he⟩ := h
    rw [he]
    exact rules.eq2 _
  · obtain ⟨x, rfl, he⟩ := h
    rw [he]
    exact rules.eq3 _
  · obtain ⟨ht, h1, h2, h3⟩ := h
    rw [← ht]
    apply (rules.elim _ _).mpr
    refine Or.inr ⟨rfl, ?_, ?_, ?_⟩
    · rintro ⟨x, y, he⟩
      obtain ⟨a, b, hab, _, _⟩ := pattern1 p hi hp hz hn t x y he
      exact h1 ⟨a, b, hab⟩
    · rintro ⟨x, he⟩
      obtain ⟨a, ha, _⟩ := pattern2 p hp hz hn t x he
      exact h2 ⟨a, ha⟩
    · rintro ⟨x, he⟩
      obtain ⟨a, ha, _⟩ := plug_square p hi hs t x he
      exact h3 ⟨a, ha⟩

theorem bu_plug (p : FreeMagma (Option α)) (hi : Function.Injective (plug p))
    (hp : p.length ≤ 2) (hz : p ≠ zero) (hn : ¬ occurs none p)
    (hs : ∀ a, p ≠ a ⋆ a) (hb : bu rules p = p) (t : FreeMagma (Option Unit)) :
    bu rules (plug p t) = plug p (bu rules t) := by
  induction t with
  | Leaf v =>
    cases v with
    | none => rfl
    | some v => exact hb
  | Fork a b ha hb =>
    change rules (bu rules (plug p a) ⋆ bu rules (plug p b)) =
      plug p (rules (bu rules a ⋆ bu rules b))
    rw [ha, hb]
    exact rules_plug p hi hp hz hn hs (bu rules a ⋆ bu rules b)

theorem bu_plug_atom (a : α) (t : FreeMagma (Option Unit)) :
    bu rules (plug (atom a) t) = plug (atom a) (bu rules t) := by
  apply bu_plug _ (plug_atom_injective a) (by simp [atom])
    (by intro h; cases h) (by simp [occurs, atom])
    (by intro b h; cases h) rfl

omit [DecidableEq α] in
theorem pair_not_square (a b : α) (hab : a ≠ b) (t : FreeMagma (Option α)) :
    pair a b ≠ t ⋆ t := by
  intro h
  obtain ⟨h1, h2⟩ := FreeMagma.Fork.inj h
  exact hab (Option.some.inj (FreeMagma.Leaf.inj (h1.trans h2.symm)))

theorem bu_pair (a b : α) (hab : a ≠ b) : bu rules (pair a b) = pair a b := by
  simp [bu, rules, rules.rule1, rules.rule2, rules.rule3, pair, atom, hab]

theorem bu_plug_pair (a b : α) (hab : a ≠ b) (t : FreeMagma (Option Unit)) :
    bu rules (plug (pair a b) t) = plug (pair a b) (bu rules t) := by
  apply bu_plug _ (plug_pair_injective a b) (by simp [pair, atom])
    (by intro h; cases h) (by simp [occurs, pair, atom])
    (pair_not_square a b hab) (bu_pair a b hab)

theorem bu_no_var (t : FreeMagma (Option Unit)) (h : ¬ HasVar t) : bu rules t = zero := by
  induction t with
  | Leaf v => cases v with
    | none => rfl
    | some v => exact (h rfl).elim
  | Fork s t hs ht =>
    have hs' : ¬ HasVar s := fun he => h (Or.inl he)
    have ht' : ¬ HasVar t := fun he => h (Or.inr he)
    change rules (bu rules s ⋆ bu rules t) = _
    rw [hs hs', ht ht']
    exact rules.eq3 _

def point (a : α) : G (α := α) := ⟨atom a, rfl⟩
def zeroPoint : G (α := α) := ⟨zero, rfl⟩

def Good (a b : α) (f : G (α := α) → G (α := α) → G (α := α)) : Prop :=
  ∃ t : FreeMagma (Option Unit), NF rules t ∧
    (f (point a) (point a)).val = plug (atom a) t ∧
    (f (point b) (point b)).val = plug (atom b) t ∧
    (f (point a ◇ point b) (point a ◇ point b)).val = plug (pair a b) t

theorem good_invariant (a b : α) (hab : a ≠ b) :
    (inferInstance : Magma (G (α := α))).IsCloneInvariant (Good a b) where
  fst := ⟨.Leaf (some ()), by rfl, rfl, rfl, bu_pair a b hab⟩
  snd := ⟨.Leaf (some ()), by rfl, rfl, rfl, bu_pair a b hab⟩
  comp := by
    rintro f g ⟨s, _, hsa, hsb, hsp⟩ ⟨t, _, hta, htb, htp⟩
    refine ⟨bu rules (s ⋆ t), bu_nf _ _, ?_, ?_, ?_⟩
    · change bu rules ((f _ _).val ⋆ (g _ _).val) = _
      rw [hsa, hta]
      exact bu_plug_atom a (s ⋆ t)
    · change bu rules ((f _ _).val ⋆ (g _ _).val) = _
      rw [hsb, htb]
      exact bu_plug_atom b (s ⋆ t)
    · change bu rules ((f _ _).val ⋆ (g _ _).val) = _
      rw [hsp, htp]
      exact bu_plug_pair a b hab (s ⋆ t)

theorem rules_mixed (a b : α) (hab : a ≠ b) (t : FreeMagma (Option Unit))
    (hv : HasVar t) :
    rules (plug (atom a) t ⋆ plug (atom b) t) = plug (atom a) t ⋆ plug (atom b) t := by
  have ha : occurs (some a) (plug (atom a) t) := (occurs_plug _ _ _).mpr ⟨rfl, hv⟩
  have hb : ¬ occurs (some a) (plug (atom b) t) := by
    rw [occurs_plug]
    simp [atom, occurs, hab]
  apply (rules.elim _ _).mpr
  refine Or.inr ⟨rfl, ?_, ?_, ?_⟩
  · rintro ⟨x, y, he⟩
    obtain ⟨hl, hr⟩ := FreeMagma.Fork.inj he
    apply hb
    rw [hr]
    exact Or.inr (Or.inl (hl ▸ ha))
  · rintro ⟨x, he⟩
    have hl := (FreeMagma.Fork.inj he).1
    rw [hl] at ha
    cases ha
  · rintro ⟨x, he⟩
    obtain ⟨hl, hr⟩ := FreeMagma.Fork.inj he
    exact hb (hr.symm ▸ (hl ▸ ha))

theorem endomorphism_at_point (a b : α) (hab : a ≠ b) (f : G (α := α) → G (α := α) → G (α := α))
    (hg : Good a b f)
    (hf : ∀ x y : G, f (x ◇ y) (x ◇ y) = f x x ◇ f y y) :
    f (point a) (point a) = point a ∨ f (point a) (point a) = zeroPoint := by
  obtain ⟨t, hn, ha, hb, hp⟩ := hg
  by_cases hv : HasVar t
  · have he := congrArg Subtype.val (hf (point a) (point b))
    change (f _ _).val = bu rules ((f _ _).val ⋆ (f _ _).val) at he
    rw [bu_op_eq_rw_op rules (f _ _).property (f _ _).property, hp, ha, hb,
      rules_mixed a b hab t hv] at he
    have ht : t = .Leaf (some ()) := by
      cases t with
      | Leaf v =>
        cases v with
        | none => cases hv
        | some v => rfl
      | Fork s t =>
        have hl := (FreeMagma.Fork.inj he).1
        have hoa : occurs (some a) (plug (atom a) (s ⋆ t)) :=
          (occurs_plug _ _ _).mpr ⟨rfl, hv⟩
        have hos : HasVar s := ((occurs_plug _ _ _).mp (hl.symm ▸ hoa)).2
        have hob : occurs (some b) (plug (pair a b) s) :=
          (occurs_plug _ _ _).mpr ⟨Or.inr rfl, hos⟩
        have hbad := (occurs_plug _ _ _).mp (hl ▸ hob)
        exact (hab (Option.some.inj hbad.1).symm).elim
    left
    apply Subtype.ext
    simpa only [ht, plug, point] using ha
  · right
    have ht : t = zero := (buFixed_of_NF rules hn).symm.trans (bu_no_var t hv)
    apply Subtype.ext
    simpa only [ht, plug, zero, zeroPoint] using ha

end PointedConfluence481

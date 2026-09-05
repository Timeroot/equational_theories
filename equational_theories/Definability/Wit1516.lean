import equational_theories.Definability.DiagWit
import equational_theories.Definability.Cancel1516

/-!
# `x = x ◇ x` is structural from `1516` on every carrier

`Cancel1516` fills the `Equation3` cell of `1516` on a **finite** carrier: there
`x = (y ◇ y) ◇ (x ◇ (x ◇ y))` bootstraps to a two-sided quasigroup and `AutBox` does the rest.
Over all magmas the bootstrap is unavailable -- the law only says that the rows of the *squares*
are onto -- and both `DiagRow.RowQG` and right cancellation have resisted every prover run.

Neither is needed.  Write `S(y) = y ◇ y` and `ψ_y(t) = t ◇ (t ◇ y)`, so the law reads
`S(y) ◇ ψ_y(t) = t`.  Then for **fixed** `u, w, v`,

    z ◇ u = w  and  z ◇ w = v   ⟹   z = S(u) ◇ v,

because `ψ_u(z) = z ◇ (z ◇ u) = z ◇ w = v` and the law at `y := u` reads that back.  So a chain
`a, ψ_x(a), ψ_x(ψ_x(a))` pins `S(x)`: both `S(x) ◇ ψ_x(a) = a` and `S(x) ◇ ψ_x(ψ_x(a)) = ψ_x(a)`
are instances of the law, and nothing else satisfies the pair.  `DiagWit` turns that into a
formula in the `idem` companion; this file supplies the three obligations.

Two of them are unconditional (`chain_pin` and `sq_eq_self_of_rightId`).  The third asks for a
chain to exist, and the only obstruction is a fat row of fixed points: `ψ_x(a) = a □ (a □ x)` is
an honest term only for `a` outside `Fix(R_x) = {u : u ◇ x = u}`, and the two links of the chain
cost two such points plus the three collisions with `S(x)` that `ψ_x`'s injectivity bounds.  So on
an infinite carrier a chain exists as soon as `Fix(R_x)` is finite -- and when `Fix(R_x)` is
everything, `x` is a right identity, hence idempotent, and the fallback disjunct of the formula
names the diagonal outright.  `RowFix` is exactly that dichotomy.
-/

open Law Law.MagmaLaw

namespace Law.MagmaLaw

namespace Wit1516

variable {G : Type} (M : Magma G)

/-! ## The two unconditional obligations -/

/-- **A chain pins the diagonal.**  If `w = ψ_x(a)` and `u = ψ_x(w)`, then `z ◇ w = a` and
`z ◇ u = w` force `z = x ◇ x`: both sides are `(u ◇ u) ◇ a`. -/
theorem chain_pin (h : ∀ x y : G, M.op (M.op y y) (M.op x (M.op x y)) = x) (x z a : G)
    (h1 : M.op z (M.op a (M.op a x)) = a)
    (h2 : M.op z (M.op (M.op a (M.op a x)) (M.op (M.op a (M.op a x)) x))
        = M.op a (M.op a x)) :
    z = M.op x x := by
  set w := M.op a (M.op a x) with hw
  set u := M.op w (M.op w x) with hu
  have hz : z = M.op (M.op u u) a := by
    have e := h z u
    rw [h2, h1] at e
    exact e.symm
  have e1 : M.op (M.op x x) w = a := by rw [hw]; exact h a x
  have e2 : M.op (M.op x x) u = w := by rw [hu]; exact h w x
  have hs : M.op x x = M.op (M.op u u) a := by
    have e := h (M.op x x) u
    rw [e2, e1] at e
    exact e.symm
  rw [hz, hs]

/-- **A right identity is idempotent.**  If `u ◇ x = u` for every `u ≠ x` then `x ◇ x = x`, so the
fallback disjunct of the formula names the right value. -/
theorem sq_eq_self_of_rightId (h : ∀ x y : G, M.op (M.op y y) (M.op x (M.op x y)) = x)
    (x : G) (hr : ∀ u : G, u ≠ x → M.op u x = u) : M.op x x = x := by
  by_contra hgx
  -- `g ◇ (u ◇ u) = u` for every `u ≠ x`: the law at `y := x`, with the row read off
  have h18 : ∀ u : G, u ≠ x → M.op (M.op x x) (M.op u u) = u := by
    intro u hu
    have e := h u x
    rwa [hr u hu] at e
  have hgx' : M.op x x ≠ x := hgx
  have hgxr : M.op (M.op x x) x = M.op x x := hr _ hgx'
  -- the square of the diagonal collapses onto it
  have h26 : M.op (M.op (M.op x x) (M.op x x)) (M.op x x) = M.op x x := by
    have e := h (M.op x x) (M.op x x)
    rwa [h18 _ hgx'] at e
  have h29 : M.op (M.op x x) (M.op x x) = M.op x x := by
    have e := h (M.op (M.op x x) (M.op x x)) (M.op x x)
    rw [h26, h26, h26] at e
    exact e.symm
  -- so `L_{x ◇ x}` inverts `ψ_{x ◇ x}` on the nose
  have h32 : ∀ u : G, M.op (M.op x x) (M.op u (M.op u (M.op x x))) = u := by
    intro u
    have e := h u (M.op x x)
    rwa [h29] at e
  -- ... and `ψ_{x ◇ x}(x)` is forced to be `x` or `x ◇ x`, both absurd
  have h39 : ∀ u : G, M.op (M.op (M.op u (M.op u (M.op x x))) (M.op u (M.op u (M.op x x))))
      (M.op (M.op x x) u) = M.op x x := by
    intro u
    have e := h (M.op x x) (M.op u (M.op u (M.op x x)))
    rwa [h32 u] at e
  have h53 : M.op (M.op (M.op x (M.op x (M.op x x))) (M.op x (M.op x (M.op x x))))
      (M.op x x) = M.op x x := by
    have e := h39 x
    rwa [hgxr] at e
  have h65 : M.op (M.op x (M.op x (M.op x x))) (M.op x (M.op x (M.op x x))) = M.op x x := by
    have e := h (M.op (M.op x (M.op x (M.op x x))) (M.op x (M.op x (M.op x x)))) (M.op x x)
    rw [h53, h53, h29, h29] at e
    exact e.symm
  rcases eq_or_ne (M.op x (M.op x (M.op x x))) x with hc | hc
  · have p := h32 x
    rw [hc] at p
    exact hgx' (hgxr.symm.trans p)
  · have q := h18 _ hc
    rw [h65, h29] at q
    have p := h32 x
    rw [← q] at p
    exact hgx' (h29.symm.trans p)

/-- `ψ_x` is injective: the law reads `a` back off `ψ_x(a)`. -/
theorem psi_inj (h : ∀ x y : G, M.op (M.op y y) (M.op x (M.op x y)) = x) (x : G) :
    Function.Injective (fun a : G ↦ M.op a (M.op a x)) := by
  intro a b hab
  have ha := h a x
  rw [show M.op a (M.op a x) = M.op b (M.op b x) from hab] at ha
  exact ha.symm.trans (h b x)

/-! ## The chain in the `idem` companion -/

open QFOp DiagWit in
/-- The companion computes `ψ_x(a)` whenever both of its `□` are honest. -/
theorem wOf_idem (x a : G) (h1 : a ≠ x) (h2 : a ≠ M.op a x) :
    wOf (idem.magma M) x a = M.op a (M.op a x) := by
  simp only [wOf, idem_ne M a x h1, idem_ne M a (M.op a x) h2]

open QFOp DiagWit in
/-- **Soundness.**  Every chain in the companion names `x ◇ x`. -/
theorem chain_sound (h : ∀ x y : G, M.op (M.op y y) (M.op x (M.op x y)) = x) (x z a : G)
    (hc : Chain (idem.magma M) x z a) : z = M.op x x := by
  obtain ⟨g1, g2, g3, g4, g5, g6, e1, e2⟩ := hc
  rw [idem_ne M a x g1] at g2
  have hw : wOf (idem.magma M) x a = M.op a (M.op a x) := wOf_idem M x a g1 g2
  rw [hw] at g3 g4 g5 e1 e2
  rw [idem_ne M _ x g3] at g4
  have hu : uOf (idem.magma M) x a
      = M.op (M.op a (M.op a x)) (M.op (M.op a (M.op a x)) x) := by
    rw [uOf, hw]
    exact wOf_idem M x _ g3 g4
  rw [hu] at g6 e2
  rw [idem_ne M z _ g5] at e1
  rw [idem_ne M z _ g6] at e2
  exact chain_pin M h x z a e1 e2

/-- `a` is a **chain head** at `x`: the `idem` box reads `ψ_x(a)` and `ψ_x(ψ_x(a))` honestly, and
neither of them collides with `x ◇ x`. -/
def Head (M : Magma G) (x a : G) : Prop :=
  a ≠ x ∧ M.op a x ≠ a ∧ M.op a (M.op a x) ≠ x ∧
    M.op (M.op a (M.op a x)) x ≠ M.op a (M.op a x) ∧
    M.op a (M.op a x) ≠ M.op x x ∧
    M.op (M.op a (M.op a x)) (M.op (M.op a (M.op a x)) x) ≠ M.op x x

open QFOp DiagWit in
/-- A chain head is a chain: the two links are instances of the law. -/
theorem chain_of_head (h : ∀ x y : G, M.op (M.op y y) (M.op x (M.op x y)) = x) (x a : G)
    (hh : Head M x a) : Chain (idem.magma M) x (M.op x x) a := by
  obtain ⟨hax, haF, hψx, hψF, hg1, hg2⟩ := hh
  have hw : wOf (idem.magma M) x a = M.op a (M.op a x) :=
    wOf_idem M x a hax fun e ↦ haF e.symm
  have hu : uOf (idem.magma M) x a
      = M.op (M.op a (M.op a x)) (M.op (M.op a (M.op a x)) x) := by
    rw [uOf, hw]
    exact wOf_idem M x _ hψx fun e ↦ hψF e.symm
  refine ⟨hax, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [idem_ne M a x hax]
    exact fun e ↦ haF e.symm
  · rwa [hw]
  · rw [hw, idem_ne M _ x hψx]
    exact fun e ↦ hψF e.symm
  · rw [hw]
    exact fun e ↦ hg1 e.symm
  · rw [hu]
    exact fun e ↦ hg2 e.symm
  · rw [hw, idem_ne M _ _ fun e ↦ hg1 e.symm]
    exact h a x
  · rw [hw, hu, idem_ne M _ _ fun e ↦ hg2 e.symm]
    exact h (M.op a (M.op a x)) x

/-- **A thin row gives a head.**  The `a` that fail are `x`, the fixed points of `R_x`, their
`ψ_x`-preimages, and the at most three points where the chain runs into `x ◇ x` itself; `ψ_x` is
injective, so on an infinite carrier a finite `Fix(R_x)` leaves a head over. -/
theorem head_of_finite_fix [Infinite G] (h : ∀ x y : G, M.op (M.op y y) (M.op x (M.op x y)) = x)
    (x : G) (hfin : {u : G | M.op u x = u}.Finite) : ∃ a : G, Head M x a := by
  classical
  set ψ : G → G := fun a ↦ M.op a (M.op a x) with hψ
  have hinj : Function.Injective ψ := psi_inj M h x
  have hpre : ∀ s : Set G, s.Finite → (ψ ⁻¹' s).Finite :=
    fun s hs ↦ Set.Finite.preimage (fun _ _ _ _ e ↦ hinj e) hs
  set F : Set G := {u : G | M.op u x = u} with hF
  set bad : Set G := {x} ∪ F ∪ ψ ⁻¹' {x} ∪ ψ ⁻¹' F ∪ ψ ⁻¹' {M.op x x} ∪
    ψ ⁻¹' (ψ ⁻¹' {M.op x x}) with hbaddef
  have hbad : bad.Finite :=
    (((((Set.finite_singleton x).union hfin).union
      (hpre _ (Set.finite_singleton x))).union (hpre _ hfin)).union
      (hpre _ (Set.finite_singleton _))).union (hpre _ (hpre _ (Set.finite_singleton _)))
  obtain ⟨a, ha⟩ := hbad.infinite_compl.nonempty
  simp only [hbaddef, Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_preimage,
    hF, Set.mem_setOf_eq, not_or] at ha
  obtain ⟨⟨⟨⟨⟨hax, haF⟩, hψx⟩, hψF⟩, hg1⟩, hg2⟩ := ha
  exact ⟨a, hax, haF, hψx, hψF, hg1, hg2⟩

end Wit1516

/-! ## The device -/

/-- The one fact about `1516` the all-magma device still spends: at every point that is not a right
identity, some `a` is a `Wit1516.Head` -- `a` and `ψ_x(a) = a ◇ (a ◇ x)` both move under `R_x`, and
neither `ψ_x(a)` nor `ψ_x(ψ_x(a))` is `x ◇ x`.  On a finite carrier the device is not needed at
all; `Cancel1516` closes those.

The clean dichotomy "`Fix(R_x)` is finite or everything" would give this
(`Wit1516.head_of_finite_fix`), and it is **false**: over `F_9 = F_3[b]/(b² + b - 1)` the model
`x ◇ y = x + b y` has `0` as a two-sided identity, so `Fix(R_0)` is everything, while
`(F_5, 3x + 3y)` has a single fixed point in every row; their product is a 45-element model of
`1516` whose rows carry `0` or `9` fixed points, and swapping `F_9` for `F_9(T)` makes the fat row
infinite and still proper.  Every point of that model has 36 heads, which is why the hypothesis is
stated at the head and not at the row. -/
abbrev ChainHead1516 : Prop :=
  ∀ {G : Type} (M : Magma G), satisfies G Law1516 →
    ∀ x : G, (∃ a : G, Wit1516.Head M x a) ∨ ∀ u : G, M.op u x = u

open QFOp DiagWit Wit1516 in
/-- `x = x ◇ x` is structural from `1516` over **every** carrier, given a head at every point.  The
finite carriers go through `Cancel1516`; the infinite ones through the chain. -/
theorem Equation3_StructuralFrom_Equation1516_of (hch : ChainHead1516) :
    Law3.StructuralFrom Law1516 := by
  intro G M hM
  by_cases hfin : Finite G
  · exact Equation3_StructuralFromFin_Equation1516 M hM
  · have : Infinite G := not_finite_iff_infinite.mp hfin
    have h0 := (@Law1516.models_iff G M).mp hM
    have h : ∀ x y : G, M.op (M.op y y) (M.op x (M.op x y)) = x := fun x y ↦ (h0 x y).symm
    refine structuralOnMagma_wit M idem (fun a b hab ↦ idem_ne M a b hab)
      (chain_sound M h) (fun x hx ↦ ?_) (fun x ↦ ?_)
      ((@Law3.models_iff _ (idem.magma M)).mpr fun x ↦ (idem_diag M x).symm)
    · exact sq_eq_self_of_rightId M h x fun u hu ↦ by rw [← idem_ne M u x hu]; exact hx u
    · rcases hch M hM x with ⟨a, ha⟩ | hall
      · exact Or.inl ⟨a, chain_of_head M h x a ha⟩
      · refine Or.inr fun u ↦ ?_
        rcases eq_or_ne u x with rfl | hu
        · exact idem_eq M u u rfl
        · rw [idem_ne M u x hu]
          exact hall u

end Law.MagmaLaw

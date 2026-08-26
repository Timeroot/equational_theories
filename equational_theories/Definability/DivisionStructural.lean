import equational_theories.Definability.QuasigroupWitness

/-!
# Division as a term-structural witness

`Definability/QuasigroupWitness.lean` shows that on a finite magma whose translations are injective
the two divisions are honest magma terms: a translation of a finite set is a permutation, so
`L_a⁻¹ = L_a^N` for an exponent `N` read off the carrier, and `a \ b = a ◇ (a ◇ ⋯ ◇ b)` with `N`
copies of `a`. That is enough for `TermDefinableFromFin`.

For `TermStructuralFromFin` the operation has to come back, and it does, for free and at the same
exponent: if `L_a^(N+1) = id` then `L_a^N` is the inverse of `L_a`, so iterating *it* `N` times is
`L_a` again -- `N * N ≡ 1` modulo `N + 1`. So the division is not merely definable from the
operation, it carries the same information, and `x ◇ y` is recovered by the very same iterate read
in the new operation.

This is a genuinely finite phenomenon. Over all magmas, `s ⊢ ∀ x y, ∃ z, x ◇ z = y` is an
equational consequence and equational logic has no case splits, so a provable existential always
has a single term witness and nothing is gained by allowing the term to vary. What varies here is
the *exponent*, and the hypothesis that pays for it -- injectivity of the translations -- is a Horn
clause rather than an equation, so it has no uniform-term counterpart at all.
-/

open FirstOrder FirstOrder.Language
open Law
open Law.MagmaLaw

namespace Law.MagmaLaw

variable {G : Type}

/-- **The inverse of an inverse.** If `N + 1` is a period of `f` then `f^[N]` inverts `f`, so `N`
iterations of `f^[N]` give `f` back: `N * N ≡ 1` modulo `N + 1`. -/
theorem iterate_iterate_of_period {f : G → G} {N : ℕ} (h : f^[N + 1] = id) :
    (f^[N])^[N] = f := by
  have hmul : (f^[N])^[N + 1] = id := by
    rw [← Function.iterate_mul, Nat.mul_comm, Function.iterate_mul, h, Function.iterate_id]
  funext x
  have h1 : f^[N] (f x) = x := by
    have := congrFun h x
    rwa [Function.iterate_succ_apply] at this
  calc (f^[N])^[N] x = (f^[N])^[N] (f^[N] (f x)) := by rw [h1]
    _ = (f^[N])^[N + 1] (f x) := (Function.iterate_succ_apply _ _ _).symm
    _ = f x := by rw [hmul]; rfl

/-- The `N`-fold left translation as a term, evaluated. -/
theorem bsem_liter_vars (M : Magma G) (N : ℕ) (x y : G) :
    bsem M (liter (Term.var 0) (Term.var 1) N) x y = (fun u ↦ M.op x u)^[N] y := by
  rw [bsem_liter]; rfl

/-- The `N`-fold right translation as a term, evaluated. -/
theorem bsem_riter_vars (M : Magma G) (N : ℕ) (x y : G) :
    bsem M (riter (Term.var 0) (Term.var 1) N) x y = (fun u ↦ M.op u y)^[N] x := by
  rw [bsem_riter]; rfl

private theorem vec_eta (w : Fin 2 → G) : ![w 0, w 1] = w := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- **The glue, left division.** On a finite magma whose translations are all injective, the left
division is term-structural: it is `N` left translations, and the operation is `N` of *its* left
translations. So to place `L` it suffices that `L` hold of the left division in any structure
carrying two-sided divisions. -/
theorem termStructuralOnMagma_of_leftDiv [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G)
    (hr : ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hl : ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ rd ld : G → G → G,
      (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
      (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
      @satisfies _ G ⟨ld⟩ L) :
    TermStructuralOnMagma L M := by
  obtain ⟨N, hN⟩ := exists_uniform_period G
  let rd : G → G → G := fun a b ↦ (fun u ↦ M.op u b)^[N] a
  let ld : G → G → G := fun a b ↦ (fun u ↦ M.op a u)^[N] b
  have hrs (a b : G) : M.op (rd a b) b = a := by
    have h := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
    rwa [Function.iterate_succ_apply'] at h
  have hri (a b : G) : rd (M.op a b) b = a := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
  have hls (a b : G) : M.op a (ld a b) = b := by
    have h := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
    rwa [Function.iterate_succ_apply'] at h
  have hli (a b : G) : ld a (M.op a b) = b := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
  refine ⟨⟨ld⟩, hsat rd ld hrs hri hls hli,
    ⟨liter (Term.var 0) (Term.var 1) N, ?_⟩, ⟨liter (Term.var 0) (Term.var 1) N, ?_⟩⟩
  · funext w
    show (fun u ↦ M.op (w 0) u)^[N] (w 1) = _
    rw [← bsem_liter_vars M N (w 0) (w 1)]
    show @Term.realize _ G M.FOStructure₀ _ ![w 0, w 1] _ = _
    rw [vec_eta]
  · funext w
    -- `fun u ↦ ⟨ld⟩.op (w 0) u` is the left translation of the *new* operation; it is `N`
    -- iterations of `M`'s, so `N` more of it is `M`'s again.  The `have` is stated through
    -- `Magma.op` so that the rewrite below matches syntactically.
    have h2 : (fun u ↦ (⟨ld⟩ : Magma G).op (w 0) u)^[N] (w 1) = M.op (w 0) (w 1) :=
      congrFun (iterate_iterate_of_period (hN (fun u ↦ M.op (w 0) u) (hl (w 0)))) (w 1)
    show M.op (w 0) (w 1) = _
    rw [← h2, ← bsem_liter_vars (⟨ld⟩ : Magma G) N (w 0) (w 1)]
    show @Term.realize _ G (⟨ld⟩ : Magma G).FOStructure₀ _ ![w 0, w 1] _ = _
    rw [vec_eta]

/-- **The glue, right division.** The mirror of `termStructuralOnMagma_of_leftDiv`. -/
theorem termStructuralOnMagma_of_rightDiv [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G)
    (hr : ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hl : ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ rd ld : G → G → G,
      (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
      (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
      @satisfies _ G ⟨rd⟩ L) :
    TermStructuralOnMagma L M := by
  obtain ⟨N, hN⟩ := exists_uniform_period G
  let rd : G → G → G := fun a b ↦ (fun u ↦ M.op u b)^[N] a
  let ld : G → G → G := fun a b ↦ (fun u ↦ M.op a u)^[N] b
  have hrs (a b : G) : M.op (rd a b) b = a := by
    have h := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
    rwa [Function.iterate_succ_apply'] at h
  have hri (a b : G) : rd (M.op a b) b = a := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
  have hls (a b : G) : M.op a (ld a b) = b := by
    have h := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
    rwa [Function.iterate_succ_apply'] at h
  have hli (a b : G) : ld a (M.op a b) = b := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
  refine ⟨⟨rd⟩, hsat rd ld hrs hri hls hli,
    ⟨riter (Term.var 0) (Term.var 1) N, ?_⟩, ⟨riter (Term.var 0) (Term.var 1) N, ?_⟩⟩
  · funext w
    show (fun u ↦ M.op u (w 1))^[N] (w 0) = _
    rw [← bsem_riter_vars M N (w 0) (w 1)]
    show @Term.realize _ G M.FOStructure₀ _ ![w 0, w 1] _ = _
    rw [vec_eta]
  · funext w
    have h2 : (fun u ↦ (⟨rd⟩ : Magma G).op u (w 1))^[N] (w 0) = M.op (w 0) (w 1) :=
      congrFun (iterate_iterate_of_period (hN (fun u ↦ M.op u (w 1)) (hr (w 1)))) (w 0)
    show M.op (w 0) (w 1) = _
    rw [← h2, ← bsem_riter_vars (⟨rd⟩ : Magma G) N (w 0) (w 1)]
    show @Term.realize _ G (⟨rd⟩ : Magma G).FOStructure₀ _ ![w 0, w 1] _ = _
    rw [vec_eta]

/-- **One-sided.** The left division needs only the *left* translations to be injective; a source
that forces a finite left quasigroup and nothing more is still a source for this device. -/
theorem termStructuralOnMagma_of_leftDiv' [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G)
    (hl : ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ ld : G → G → G,
      (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
      @satisfies _ G ⟨ld⟩ L) :
    TermStructuralOnMagma L M := by
  obtain ⟨N, hN⟩ := exists_uniform_period G
  let ld : G → G → G := fun a b ↦ (fun u ↦ M.op a u)^[N] b
  have hls (a b : G) : M.op a (ld a b) = b := by
    have h := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
    rwa [Function.iterate_succ_apply'] at h
  have hli (a b : G) : ld a (M.op a b) = b := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
  refine ⟨⟨ld⟩, hsat ld hls hli,
    ⟨liter (Term.var 0) (Term.var 1) N, ?_⟩, ⟨liter (Term.var 0) (Term.var 1) N, ?_⟩⟩
  · funext w
    show (fun u ↦ M.op (w 0) u)^[N] (w 1) = _
    rw [← bsem_liter_vars M N (w 0) (w 1)]
    show @Term.realize _ G M.FOStructure₀ _ ![w 0, w 1] _ = _
    rw [vec_eta]
  · funext w
    have h2 : (fun u ↦ (⟨ld⟩ : Magma G).op (w 0) u)^[N] (w 1) = M.op (w 0) (w 1) :=
      congrFun (iterate_iterate_of_period (hN (fun u ↦ M.op (w 0) u) (hl (w 0)))) (w 1)
    show M.op (w 0) (w 1) = _
    rw [← h2, ← bsem_liter_vars (⟨ld⟩ : Magma G) N (w 0) (w 1)]
    show @Term.realize _ G (⟨ld⟩ : Magma G).FOStructure₀ _ ![w 0, w 1] _ = _
    rw [vec_eta]

/-- **One-sided.** The mirror of `termStructuralOnMagma_of_leftDiv'`. -/
theorem termStructuralOnMagma_of_rightDiv' [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G)
    (hr : ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hsat : ∀ rd : G → G → G,
      (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
      @satisfies _ G ⟨rd⟩ L) :
    TermStructuralOnMagma L M := by
  obtain ⟨N, hN⟩ := exists_uniform_period G
  let rd : G → G → G := fun a b ↦ (fun u ↦ M.op u b)^[N] a
  have hrs (a b : G) : M.op (rd a b) b = a := by
    have h := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
    rwa [Function.iterate_succ_apply'] at h
  have hri (a b : G) : rd (M.op a b) b = a := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
  refine ⟨⟨rd⟩, hsat rd hrs hri,
    ⟨riter (Term.var 0) (Term.var 1) N, ?_⟩, ⟨riter (Term.var 0) (Term.var 1) N, ?_⟩⟩
  · funext w
    show (fun u ↦ M.op u (w 1))^[N] (w 0) = _
    rw [← bsem_riter_vars M N (w 0) (w 1)]
    show @Term.realize _ G M.FOStructure₀ _ ![w 0, w 1] _ = _
    rw [vec_eta]
  · funext w
    have h2 : (fun u ↦ (⟨rd⟩ : Magma G).op u (w 1))^[N] (w 0) = M.op (w 0) (w 1) :=
      congrFun (iterate_iterate_of_period (hN (fun u ↦ M.op u (w 1)) (hr (w 1)))) (w 0)
    show M.op (w 0) (w 1) = _
    rw [← h2, ← bsem_riter_vars (⟨rd⟩ : Magma G) N (w 0) (w 1)]
    show @Term.realize _ G (⟨rd⟩ : Magma G).FOStructure₀ _ ![w 0, w 1] _ = _
    rw [vec_eta]

/-- The one-sided `TermStructuralFromFin` wrapper for the left division. -/
theorem termStructuralFromFin_of_leftDiv' {β : Type} {L L' : Law.MagmaLaw β}
    (hl : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ ld : G → G → G,
        (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
        @satisfies _ G ⟨ld⟩ L) :
    TermStructuralFromFin L L' :=
  fun {G} _ M hM ↦ termStructuralOnMagma_of_leftDiv' M (hl G M hM) (hsat G M hM)

/-- The one-sided `TermStructuralFromFin` wrapper for the right division. -/
theorem termStructuralFromFin_of_rightDiv' {β : Type} {L L' : Law.MagmaLaw β}
    (hr : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hsat : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ rd : G → G → G,
        (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
        @satisfies _ G ⟨rd⟩ L) :
    TermStructuralFromFin L L' :=
  fun {G} _ M hM ↦ termStructuralOnMagma_of_rightDiv' M (hr G M hM) (hsat G M hM)

/-- The `TermStructuralFromFin` wrapper for the left division. -/
theorem termStructuralFromFin_of_leftDiv {β : Type} {L L' : Law.MagmaLaw β}
    (hr : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hl : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ rd ld : G → G → G,
        (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
        (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
        @satisfies _ G ⟨ld⟩ L) :
    TermStructuralFromFin L L' :=
  fun {G} _ M hM ↦ termStructuralOnMagma_of_leftDiv M (hr G M hM) (hl G M hM) (hsat G M hM)

/-- The `TermStructuralFromFin` wrapper for the right division. -/
theorem termStructuralFromFin_of_rightDiv {β : Type} {L L' : Law.MagmaLaw β}
    (hr : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hl : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ rd ld : G → G → G,
        (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
        (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
        @satisfies _ G ⟨rd⟩ L) :
    TermStructuralFromFin L L' :=
  fun {G} _ M hM ↦ termStructuralOnMagma_of_rightDiv M (hr G M hM) (hl G M hM) (hsat G M hM)

end Law.MagmaLaw

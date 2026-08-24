import equational_theories.Definability.IdempotentPower

/-!
# Idempotent iterates applied outside a defining term, at an arbitrary depth

`IdempotentPower.lean` supplies one wrapper: `fun x y ↦ e (t x y)`, with `e = u^[N+1]` the
idempotent iterate of a unary term `u`. That is the only exponent reachable when the iterate is
pinned to `e`, and for most cells it is the wrong one -- see `SigmaOuter546.lean`, where the
coefficient the targets need is two powers *below* the idempotent.

`e` and `v = u^[N]` generate every iterate the device can name. Since `e` is idempotent and
commutes with `v`, every composite of the two collapses to `v^[k]` or `e ∘ v^[k]`, and those two
families are exactly `u^[N k]` and `u^[N k + N + 1]`. The two lemmas below are the corresponding
glue; `termDefinableOnMagma_of_iterate` is the `k = 0` case of the first.

The hypothesis that makes any of this usable is that `u` is a magma endomorphism, so that `e` and
`v` distribute over `◇` and a prover can push them through a defining term. `iterate_endo` is that
step: it is an iterate of an endomorphism, so it is one.
-/

open FirstOrder.Language
open Law
open Law.MagmaLaw

namespace Law.MagmaLaw

variable {G : Type}

/-- **The glue at depth `k`.** `e ∘ v^[k]` is `u^[N k + N + 1]`, so it is named by a term just as
`e` is; what it buys is a whole arithmetic progression of exponents instead of one. -/
theorem termDefinableOnMagma_of_iterate_ev [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G) (u : UTerm G) (t : BTerm G) (k : ℕ)
    (hsat : ∀ (N : ℕ) (e v : G → G), Function.IsIdempotentIterate (ufunM M u) N e v →
      @satisfies _ G ⟨fun x y ↦ e (v^[k] (@Term.realize _ G M.FOStructure₀ _ ![x, y] t))⟩ L) :
    TermDefinableOnMagma L M := by
  obtain ⟨N, e, v, he⟩ := Function.exists_isIdempotentIterate (ufunM M u)
  refine ⟨⟨fun x y ↦ e (v^[k] (@Term.realize _ G M.FOStructure₀ _ ![x, y] t))⟩, hsat N e v he,
    ⟨uiter u (N + 1 + N * k) t, ?_⟩⟩
  funext w
  have hw : ![w 0, w 1] = w := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  show e (v^[k] (@Term.realize _ G M.FOStructure₀ _ ![w 0, w 1] t)) = _
  rw [hw]
  have hz : ∀ z : G, e (v^[k] z) = (ufunM M u)^[N + 1 + N * k] z := by
    intro z
    rw [he.e_eq, he.v_eq, ← Function.iterate_mul, ← Function.iterate_add_apply]
  rw [hz]
  exact (@realize_uiter G M.FOStructure₀ u (N + 1 + N * k) t w).symm

/-- The other half of the grid: `v^[k]` is `u^[N k]`, the exponents `e` cannot reach at all. -/
theorem termDefinableOnMagma_of_iterate_v [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G) (u : UTerm G) (t : BTerm G) (k : ℕ)
    (hsat : ∀ (N : ℕ) (e v : G → G), Function.IsIdempotentIterate (ufunM M u) N e v →
      @satisfies _ G ⟨fun x y ↦ v^[k] (@Term.realize _ G M.FOStructure₀ _ ![x, y] t)⟩ L) :
    TermDefinableOnMagma L M := by
  obtain ⟨N, e, v, he⟩ := Function.exists_isIdempotentIterate (ufunM M u)
  refine ⟨⟨fun x y ↦ v^[k] (@Term.realize _ G M.FOStructure₀ _ ![x, y] t)⟩, hsat N e v he,
    ⟨uiter u (N * k) t, ?_⟩⟩
  funext w
  have hw : ![w 0, w 1] = w := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  show v^[k] (@Term.realize _ G M.FOStructure₀ _ ![w 0, w 1] t) = _
  rw [hw]
  have hz : ∀ z : G, v^[k] z = (ufunM M u)^[N * k] z := by
    intro z
    rw [he.v_eq, ← Function.iterate_mul]
  rw [hz]
  exact (@realize_uiter G M.FOStructure₀ u (N * k) t w).symm

/-- The `TermDefinableFromFin` wrapper around `termDefinableOnMagma_of_iterate_ev`. -/
theorem termDefinableFromFin_of_iterate_ev {β : Type} {L L' : Law.MagmaLaw β}
    (u : ∀ G : Type, UTerm G) (t : ∀ G : Type, BTerm G) (k : ℕ)
    (h : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ (N : ℕ) (e v : G → G), Function.IsIdempotentIterate (ufunM M (u G)) N e v →
        @satisfies _ G
          ⟨fun x y ↦ e (v^[k] (@Term.realize _ G M.FOStructure₀ _ ![x, y] (t G)))⟩ L) :
    TermDefinableFromFin L L' :=
  fun {G} _ M hM ↦ termDefinableOnMagma_of_iterate_ev M (u G) (t G) k (h G M hM)

/-- The `TermDefinableFromFin` wrapper around `termDefinableOnMagma_of_iterate_v`. -/
theorem termDefinableFromFin_of_iterate_v {β : Type} {L L' : Law.MagmaLaw β}
    (u : ∀ G : Type, UTerm G) (t : ∀ G : Type, BTerm G) (k : ℕ)
    (h : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ (N : ℕ) (e v : G → G), Function.IsIdempotentIterate (ufunM M (u G)) N e v →
        @satisfies _ G ⟨fun x y ↦ v^[k] (@Term.realize _ G M.FOStructure₀ _ ![x, y] (t G))⟩ L) :
    TermDefinableFromFin L L' :=
  fun {G} _ M hM ↦ termDefinableOnMagma_of_iterate_v M (u G) (t G) k (h G M hM)

/-- The two families of iterates the device can name: `v^[k] = u^[N k]`, and its composite with
the idempotent `e`, `e ∘ v^[k] = u^[N k + N + 1]`. -/
def wrapf {α : Type*} (e v : α → α) (d : Bool) (k : ℕ) : α → α :=
  fun x ↦ if d then e (v^[k] x) else v^[k] x

/-- The exponent `wrapf` denotes, given the index `N` of the idempotent iterate. -/
def wrapn (N k : ℕ) (d : Bool) : ℕ := if d then N + 1 + N * k else N * k

theorem wrapf_eq {α : Type*} {u e v : α → α} {N : ℕ} (he : Function.IsIdempotentIterate u N e v)
    (d : Bool) (k : ℕ) (x : α) : wrapf e v d k x = u^[wrapn N k d] x := by
  cases d with
  | false =>
    simp only [wrapf, Bool.false_eq_true, if_false, wrapn, he.v_eq, ← Function.iterate_mul]
  | true =>
    simp only [wrapf, if_true, wrapn, he.e_eq, he.v_eq, ← Function.iterate_mul,
      ← Function.iterate_add_apply]

section Realize

variable [inst : (MagmaLanguage.withConstants (∅ : Set G)).Structure G]

/-- Realizing a base term whose two variables have been replaced by iterates of `u`: the same as
realizing it at the iterated arguments. This is `Term.realize_subst` with the substitution spelled
out, stated where the structure instance is in scope. -/
theorem realize_bsubst (u : UTerm G) (na nb : ℕ) (t : BTerm G) (w : Fin 2 → G) :
    (t.subst ![uiter u na (Term.var 0), uiter u nb (Term.var 1)]).realize w
      = t.realize ![(ufun u)^[na] (w 0), (ufun u)^[nb] (w 1)] := by
  rw [Term.realize_subst]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => exact realize_uiter u na (Term.var 0) w
  | ⟨1, _⟩ => exact realize_uiter u nb (Term.var 1) w

end Realize

/-- **The glue with one iterate per variable.** An outer wrapper `u^[c] (t x y)` is the same as
`t (u^[c] x) (u^[c] y)`, because `u` is an endomorphism: one knob for both arguments. Giving the
two variables *different* exponents is a strictly larger family, and it is the one that reaches
targets no outer wrapper does. -/
theorem termDefinableOnMagma_of_iterate_pair [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G) (u : UTerm G) (t : BTerm G) (da db : Bool) (ka kb : ℕ)
    (hsat : ∀ (N : ℕ) (e v : G → G), Function.IsIdempotentIterate (ufunM M u) N e v →
      @satisfies _ G ⟨fun x y ↦ @Term.realize _ G M.FOStructure₀ _
        ![wrapf e v da ka x, wrapf e v db kb y] t⟩ L) :
    TermDefinableOnMagma L M := by
  obtain ⟨N, e, v, he⟩ := Function.exists_isIdempotentIterate (ufunM M u)
  refine ⟨⟨fun x y ↦ @Term.realize _ G M.FOStructure₀ _
      ![wrapf e v da ka x, wrapf e v db kb y] t⟩, hsat N e v he,
    ⟨t.subst ![uiter u (wrapn N ka da) (Term.var 0), uiter u (wrapn N kb db) (Term.var 1)], ?_⟩⟩
  funext w
  show @Term.realize _ G M.FOStructure₀ _ ![wrapf e v da ka (w 0), wrapf e v db kb (w 1)] t = _
  rw [@realize_bsubst G M.FOStructure₀ u (wrapn N ka da) (wrapn N kb db) t w]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => exact wrapf_eq he da ka (w 0)
  | ⟨1, _⟩ => exact wrapf_eq he db kb (w 1)

/-- The `TermDefinableFromFin` wrapper around `termDefinableOnMagma_of_iterate_pair`. -/
theorem termDefinableFromFin_of_iterate_pair {β : Type} {L L' : Law.MagmaLaw β}
    (u : ∀ G : Type, UTerm G) (t : ∀ G : Type, BTerm G) (da db : Bool) (ka kb : ℕ)
    (h : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ (N : ℕ) (e v : G → G), Function.IsIdempotentIterate (ufunM M (u G)) N e v →
        @satisfies _ G ⟨fun x y ↦ @Term.realize _ G M.FOStructure₀ _
          ![wrapf e v da ka x, wrapf e v db kb y] (t G)⟩ L) :
    TermDefinableFromFin L L' :=
  fun {G} _ M hM ↦ termDefinableOnMagma_of_iterate_pair M (u G) (t G) da db ka kb (h G M hM)

/-- An iterate of a magma endomorphism is one. Both `e` and `v` are iterates of the chosen unary
term, so whenever the source law makes that term an endomorphism, both distribute over `◇`. -/
theorem iterate_endo [Magma G] {u : G → G} (hu : ∀ a b : G, u (a ◇ b) = u a ◇ u b) :
    ∀ (n : ℕ) (a b : G), u^[n] (a ◇ b) = u^[n] a ◇ u^[n] b := by
  intro n
  induction n with
  | zero => intro a b; rfl
  | succ k ih =>
    intro a b
    simp only [Function.iterate_succ_apply', ih, hu]

end Law.MagmaLaw

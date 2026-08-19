import equational_theories.Definability.FiniteFlavour
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finite.Prod

/-!
# The idempotent power of a unary term, and the definitions it builds

This file supplies the generic machinery behind a family of `TermDefinableFromFin` facts whose
defining term is *not* uniform in the magma.

Fix a magma `M` on a finite carrier `G` and a unary term `u`. The iterates `u, u², u³, …` cannot
all be distinct, so the sequence is eventually periodic, and some iterate `e := u^[N]` is
idempotent. The number `N` depends on `M`, so `e` is not a term of the magma language in any
uniform sense. But for each *fixed* finite magma it is one: it is `u` substituted into itself `N`
times. That is exactly the gap between `TermDefinableFrom` (a single term must work for every
magma) and `TermDefinableFromFin` (the term may be chosen after the magma), so definitions of this
shape live only in the finite flavour.

The eventual image `Set.range e` is where all the content sits. On it `e` is the identity, `u` is a
bijection, and it is precisely the set of periodic points of `u`. Those three facts are what a
first-order axiomatisation of `e` cannot express -- the axioms `e ∘ e = e`, `e = v ∘ u = u ∘ v`,
`v ∘ e = v` admit models in which `Set.range e` is far too small -- and they are proved here as
ordinary lemmas about a finite type.

## Main results

* `Function.exists_pos_iterate_idempotent`: on a finite type some positive iterate is idempotent.
* `Function.IsIdempotentIterate`: the data `e = u^[N+1]`, `v = u^[N]`, `e ∘ e = e`.
* `Function.IsIdempotentIterate.bijOn_range`, `eqOn_range`, `range_eq_periodicPts`: the structure
  of the eventual image.
* `Law.MagmaLaw.uiter`, `Law.MagmaLaw.realize_uiter`: `u^[N]` as a syntactic term.
* `Law.MagmaLaw.termDefinableOnMagma_of_iterate` and `termDefinableFromFin_of_iterate`: the glue.
  To get `TermDefinableOnMagma L M` it is enough to exhibit a unary term `u` and a binary term `t`
  such that `fun x y ↦ u^[N] (t x y)` satisfies `L` whenever `u^[N]` is idempotent.

## How a cell proof is meant to go

Empirically, on the finite models of the source laws for which this device produces witnesses, `e`
is either the identity or a constant map, and the two cases are handled by the two ends of the
development:

* `Function.IsIdempotentIterate.eq_id_of_injective`: if `u` is injective then `e = id`, so the
  defining term collapses to the plain term `t` and the goal becomes an ordinary equational
  consequence of the source law together with the finiteness rotations.
* `Law.MagmaLaw.satisfies_of_const`: if `e` is constant then the defined operation is constant, and
  every law with a compound term on both sides -- which is the case for all of the targets in this
  family -- holds of it.

What is *not* supplied here is the step that says a non-injective `u` has a one-point eventual
image. That is false for a general self-map and has to come from the source law; on the sources
tried so far neither an equational prover nor a hand argument reaches it, so no cell is proved in
this file yet.
-/

open FirstOrder FirstOrder.Language
open Law
open Law.MagmaLaw

namespace Function

variable {α : Type*}

/-- On a finite type the iterates of `f` cannot all be distinct, so `f` is eventually periodic:
there is a positive `p` and a threshold `i` past which `f^[n + p] = f^[n]`. -/
theorem exists_pos_period_iterate [Finite α] (f : α → α) :
    ∃ i p : ℕ, 0 < p ∧ ∀ n, i ≤ n → f^[n + p] = f^[n] := by
  obtain ⟨a, b, hne, hab⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ ↦ (f^[n] : α → α))
  have hab' : f^[a] = f^[b] := hab
  have key : ∀ c d : ℕ, c < d → f^[c] = f^[d] → ∀ n, c ≤ n → f^[n + (d - c)] = f^[n] := by
    intro c d hcd hcdeq n hn
    funext x
    have h1 : n + (d - c) = (n - c) + d := by omega
    have h2 : n = (n - c) + c := by omega
    rw [h1, iterate_add_apply, ← hcdeq, ← iterate_add_apply, ← h2]
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨a, b - a, by omega, key a b h hab'⟩
  · exact ⟨b, a - b, by omega, key b a h hab'.symm⟩

/-- On a finite type some positive iterate of any self-map is idempotent. This is the fact the
whole file rests on; `N` depends on `f`, and no bound uniform in the type is available. -/
theorem exists_pos_iterate_idempotent [Finite α] (f : α → α) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, f^[N] (f^[N] x) = f^[N] x := by
  obtain ⟨i, p, hp, hper⟩ := exists_pos_period_iterate f
  refine ⟨p * (i + 1), Nat.mul_pos hp (Nat.succ_pos i), fun x ↦ ?_⟩
  have hNi : i ≤ p * (i + 1) :=
    le_trans (Nat.le_succ i) (Nat.le_mul_of_pos_left (i + 1) hp)
  -- peel the period off `i + 1` times
  have key : ∀ m : ℕ, f^[p * (i + 1) + p * m] = f^[p * (i + 1)] := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have e1 : p * (i + 1) + p * (k + 1) = p * (i + 1) + p * k + p := by
        rw [Nat.mul_succ p k, ← Nat.add_assoc]
      rw [e1, hper _ (le_trans hNi (Nat.le_add_right _ _)), ih]
  have h := congrFun (key (i + 1)) x
  rwa [iterate_add_apply] at h

/-- `e = u^[N+1]` is an idempotent iterate of `u`, with `v = u^[N]` the iterate one step below.
On a finite carrier such an `N` always exists (`Function.exists_isIdempotentIterate`), but it
depends on the carrier: that is precisely why the definitions it builds are not uniform. -/
structure IsIdempotentIterate (u : α → α) (N : ℕ) (e v : α → α) : Prop where
  /-- `e` is the `(N+1)`-st iterate -/
  e_eq : e = u^[N + 1]
  /-- `v` is the iterate one step below -/
  v_eq : v = u^[N]
  /-- and the `(N+1)`-st iterate is idempotent -/
  idem : ∀ x, e (e x) = e x

/-- Every self-map of a finite type has an idempotent iterate. -/
theorem exists_isIdempotentIterate [Finite α] (u : α → α) :
    ∃ (N : ℕ) (e v : α → α), IsIdempotentIterate u N e v := by
  obtain ⟨N, hN, hidem⟩ := exists_pos_iterate_idempotent u
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact ⟨m, u^[m + 1], u^[m], ⟨rfl, rfl, hidem⟩⟩

namespace IsIdempotentIterate

variable {u e v : α → α} {N : ℕ} (h : IsIdempotentIterate u N e v)
include h

/-- `e` commutes with `u`: both sides are `u^[N + 2]`. -/
theorem comm (x : α) : e (u x) = u (e x) := by
  rw [h.e_eq]
  exact (iterate_succ_apply u (N + 1) x).symm.trans (iterate_succ_apply' u (N + 1) x)

/-- `e` commutes with `v`: both sides are `u^[2N + 1]`. -/
theorem comm_v (x : α) : v (e x) = e (v x) := by
  rw [h.e_eq, h.v_eq, ← iterate_add_apply, ← iterate_add_apply, Nat.add_comm]

theorem u_comp_v (x : α) : u (v x) = e x := by
  rw [h.v_eq, h.e_eq, iterate_succ_apply']

theorem v_comp_u (x : α) : v (u x) = e x := by
  rw [h.v_eq, h.e_eq, iterate_succ_apply]

/-- `e` is the identity on its own image. -/
theorem eqOn_range : Set.EqOn e id (Set.range e) := by
  rintro _ ⟨x, rfl⟩
  exact h.idem x

theorem mem_range_iff {x : α} : x ∈ Set.range e ↔ e x = x :=
  ⟨fun hx ↦ h.eqOn_range hx, fun hx ↦ ⟨x, hx⟩⟩

/-- `u` maps the eventual image into itself. -/
theorem mapsTo_range : Set.MapsTo u (Set.range e) (Set.range e) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨u x, h.comm x⟩

/-- `v` maps the eventual image into itself. -/
theorem mapsTo_range_v : Set.MapsTo v (Set.range e) (Set.range e) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨v x, (h.comm_v x).symm⟩

/-- On the eventual image `u` is a bijection, with `v` as inverse. This is the first of the two
facts that no equational axiomatisation of `e` can force. -/
theorem bijOn_range : Set.BijOn u (Set.range e) (Set.range e) := by
  refine ⟨h.mapsTo_range, ?_, ?_⟩
  · intro a ha b hb hab
    have hva : v (u a) = v (u b) := congrArg v hab
    rw [h.v_comp_u, h.v_comp_u, h.mem_range_iff.mp ha, h.mem_range_iff.mp hb] at hva
    exact hva
  · rintro b hb
    refine ⟨v b, h.mapsTo_range_v hb, ?_⟩
    rw [h.u_comp_v, h.mem_range_iff.mp hb]

/-- If `u` is injective on a finite carrier then it is a bijection, every iterate is a bijection,
and an idempotent bijection is the identity: the device degenerates and the defining term is the
plain one. This is one half of the dichotomy that governs these cells. -/
theorem eq_id_of_injective (hu : Function.Injective u) : e = id := by
  have he : Function.Injective e := by
    rw [h.e_eq]; exact hu.iterate _
  funext x
  exact he (h.idem x)

/-- On a finite carrier surjectivity of `u` has the same consequence. -/
theorem eq_id_of_surjective [Finite α] (hu : Function.Surjective u) : e = id :=
  h.eq_id_of_injective (Finite.injective_iff_surjective.mpr hu)

omit h in
/-- The other degenerate case: if the eventual image is a single point then `e` is constant. -/
theorem eq_const_of_subsingleton {a : α} (hs : (Set.range e).Subsingleton)
    (ha : a ∈ Set.range e) : e = fun _ ↦ a := by
  funext x
  exact hs ⟨x, rfl⟩ ha

/-- Conversely, if `e` is the identity then `u` is a bijection. -/
theorem bijective_of_eq_id (hid : e = id) : Function.Bijective u := by
  constructor
  · intro a b hab
    have := congrArg v hab
    rw [h.v_comp_u, h.v_comp_u, hid] at this
    exact this
  · intro b
    exact ⟨v b, by rw [h.u_comp_v, hid]; rfl⟩

/-- The eventual image is exactly the set of periodic points of `u`. This is the second fact; it
pins `Set.range e` down from below, and the countermodels of the equational axiomatisation of `e`
are precisely maps whose image is too small to contain all the periodic points. -/
theorem range_eq_periodicPts : Set.range e = {x | ∃ k, 0 < k ∧ u^[k] x = x} := by
  ext x
  constructor
  · intro hx
    exact ⟨N + 1, Nat.succ_pos N, by rw [← h.e_eq]; exact h.mem_range_iff.mp hx⟩
  · rintro ⟨k, hk, hkx⟩
    -- `x` is fixed by every multiple of `k`, in particular by one that is at least `N + 1`
    have hmul : ∀ m : ℕ, u^[k * m] x = x := by
      intro m
      induction m with
      | zero => simp
      | succ j ih =>
        have e1 : k * (j + 1) = k + k * j := by
          rw [Nat.mul_succ k j]; exact Nat.add_comm _ _
        rw [e1, iterate_add_apply, ih, hkx]
    have hle : N + 1 ≤ k * (N + 1) := Nat.le_mul_of_pos_left (N + 1) hk
    refine ⟨u^[k * (N + 1) - (N + 1)] x, ?_⟩
    rw [h.e_eq, ← iterate_add_apply,
      show N + 1 + (k * (N + 1) - (N + 1)) = k * (N + 1) by omega, hmul]

end IsIdempotentIterate

end Function

namespace Law.MagmaLaw

variable {G : Type}

/-- A one-variable term of the magma language. -/
abbrev UTerm (G : Type) := (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 1)

/-- A two-variable term of the magma language: the shape a defining term must have. -/
abbrev BTerm (G : Type) := (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 2)

/-- Substitute the two-variable term `t` for the single variable of the unary term `u`. -/
def uapp (u : UTerm G) (t : BTerm G) : BTerm G := u.subst (fun _ ↦ t)

/-- `u` iterated `n` times and applied to `t`. This is the term that names `u^[n]`: for each fixed
`n` it is an honest `MagmaLanguage` term, which is all the finite flavour needs. -/
def uiter (u : UTerm G) (n : ℕ) (t : BTerm G) : BTerm G := (uapp u)^[n] t

section Realize

variable [MagmaLanguage[[(∅ : Set G)]].Structure G]

/-- The unary function that a one-variable term denotes. -/
def ufun (u : UTerm G) : G → G := fun x ↦ u.realize (fun _ ↦ x)

theorem realize_uapp (u : UTerm G) (t : BTerm G) (w : Fin 2 → G) :
    (uapp u t).realize w = ufun u (t.realize w) := by
  show (u.subst fun _ ↦ t).realize w = _
  rw [Term.realize_subst]
  rfl

theorem realize_uiter (u : UTerm G) (n : ℕ) (t : BTerm G) (w : Fin 2 → G) :
    (uiter u n t).realize w = (ufun u)^[n] (t.realize w) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : uiter u (k + 1) t = uapp u (uiter u k t) := Function.iterate_succ_apply' _ _ _
    rw [h1, realize_uapp, ih, Function.iterate_succ_apply']

end Realize

/-- The `MagmaLanguage[[∅]]`-structure attached to a magma. -/
abbrev _root_.Magma.FOStructure₀ (M : Magma G) : MagmaLanguage[[(∅ : Set G)]].Structure G :=
  @FirstOrder.Language.withConstantsStructure MagmaLanguage G M.FOStructure (∅ : Set G)
    (FirstOrder.Language.paramsStructure G ∅)

/-- The unary function a one-variable term denotes in the magma `M`. -/
abbrev ufunM (M : Magma G) (u : UTerm G) : G → G := @ufun G M.FOStructure₀ u

/-- **The glue.** On a finite magma, to term-define `L` it is enough to give a unary term `u` and
a binary term `t` such that `fun x y ↦ e (t x y)` satisfies `L` for every idempotent iterate `e` of
`u`. The exponent is produced by `Function.exists_isIdempotentIterate`, so it depends on the
magma -- legal in the finite flavour, and only there. -/
theorem termDefinableOnMagma_of_iterate [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G) (u : UTerm G) (t : BTerm G)
    (hsat : ∀ (N : ℕ) (e v : G → G), Function.IsIdempotentIterate (ufunM M u) N e v →
      @satisfies _ G ⟨fun x y ↦ e (@Term.realize _ G M.FOStructure₀ _ ![x, y] t)⟩ L) :
    TermDefinableOnMagma L M := by
  obtain ⟨N, e, v, he⟩ := Function.exists_isIdempotentIterate (ufunM M u)
  refine ⟨⟨fun x y ↦ e (@Term.realize _ G M.FOStructure₀ _ ![x, y] t)⟩, hsat N e v he,
    ⟨uiter u (N + 1) t, ?_⟩⟩
  funext w
  have hw : ![w 0, w 1] = w := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  show e (@Term.realize _ G M.FOStructure₀ _ ![w 0, w 1] t) = _
  rw [hw, he.e_eq]
  exact (@realize_uiter G M.FOStructure₀ u (N + 1) t w).symm

/-- Degenerate branch of the device: when `e` is constant the defined operation is constant too,
so `L` holds of it as soon as it holds of a constant magma -- which is the case for every law with
a compound term on both sides. On the bank models of the sources in this family `e` is either the
identity (`u` a bijection, `Function.IsIdempotentIterate.eq_id_of_injective`) or constant, so these
two lemmas are the two halves of every cell proof. -/
theorem satisfies_of_const {β : Type} {L : Law.MagmaLaw β} {e : G → G} {a : G}
    (he : ∀ x, e x = a) (hL : @satisfies _ G ⟨fun _ _ ↦ a⟩ L) (f : G → G → G) :
    @satisfies _ G ⟨fun x y ↦ e (f x y)⟩ L := by
  have h : (⟨fun x y ↦ e (f x y)⟩ : Magma G) = ⟨fun _ _ ↦ a⟩ := by
    congr 1
    funext x y
    exact he _
  rw [h]
  exact hL

/-- The `TermDefinableFromFin` wrapper around `termDefinableOnMagma_of_iterate`. The unary term
`u` and the binary term `t` are chosen uniformly, but the exponent -- and hence the defining term
`u^[N] (t x y)` -- is chosen after the magma. -/
theorem termDefinableFromFin_of_iterate {β : Type} {L L' : Law.MagmaLaw β}
    (u : ∀ G : Type, UTerm G) (t : ∀ G : Type, BTerm G)
    (h : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ (N : ℕ) (e v : G → G), Function.IsIdempotentIterate (ufunM M (u G)) N e v →
        @satisfies _ G ⟨fun x y ↦ e (@Term.realize _ G M.FOStructure₀ _ ![x, y] (t G))⟩ L) :
    TermDefinableFromFin L L' :=
  fun {G} _ M hM ↦ termDefinableOnMagma_of_iterate M (u G) (t G) (h G M hM)

end Law.MagmaLaw

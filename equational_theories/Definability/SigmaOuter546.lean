import equational_theories.Definability.IdempotentPower
import equational_theories.Equations.All
import equational_theories.Superposition

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# Source 546: an idempotent iterate applied outside the defining term

Equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))` carries more of the definability board than any other
open source. Its chain makes every left translation bijective, so a model is a quasigroup, and the
law also proves mediality; by Toyoda a finite model is `x ◇ y = -x + g y + c` on a finite
`Z[i]`-module, `g` acting as `i`. A binary term is then a triple `(P, Q, α)` standing for
`P x + Q y + α c`, and for each of the targets below the triple that would satisfy it has
`P = Q = λ/2` where `λ` is idempotent. No *uniform* triple works, which is why every fixed-term
search on this source came back empty.

But `2 = i (i-1)²` in `Z[i]`, so `λ/2` is an honest Gaussian integer sitting two powers below `λ`.
Writing `u x = x ◇ x`, which multiplies a triple by `(i-1)`, the witness is therefore `u^[3N+1]`
applied to a small *base* term, where `u^[N+1]` is idempotent -- and `u^[3N+1] = e ∘ v ∘ v` in the
data that `Function.IsIdempotentIterate` already provides. The exponent depends on the magma, so
these are finite-flavour facts.

Earlier searches placed the iterates at the *leaves* of the defining term; the algebra puts them on
the outside. That is the whole content of this file: the glue lemma
`termDefinableOnMagma_of_iterate_evv` is `termDefinableOnMagma_of_iterate` with `v` applied twice,
and each cell is then an ordinary equational replay against the axioms of `IdempotentPower.lean`.
-/

open FirstOrder.Language
open Law
open Law.MagmaLaw

namespace Law.MagmaLaw

variable {G : Type}

/-- The magma operation as a two-variable term, for building `TermDefinable` witnesses. -/
private abbrev tm (a b : (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 2)) :
    (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 2) :=
  Functions.apply₂ (Sum.inl ()) a b

/-- The magma operation as a one-variable term: `tm` at the other arity. -/
private abbrev tm1 (a b : (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 1)) :
    (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 1) :=
  Functions.apply₂ (Sum.inl ()) a b

/-- **The glue, with the iterate two steps below idempotent.** `e ∘ v ∘ v` is `u^[3N+1]`, so it is
named by a term just as `e = u^[N+1]` is; what it buys is a coefficient that `e` alone cannot
reach. Compare `termDefinableOnMagma_of_iterate`, of which this is the only variant needed. -/
theorem termDefinableOnMagma_of_iterate_evv [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G) (u : UTerm G) (t : BTerm G)
    (hsat : ∀ (N : ℕ) (e v : G → G), Function.IsIdempotentIterate (ufunM M u) N e v →
      @satisfies _ G ⟨fun x y ↦ e (v (v (@Term.realize _ G M.FOStructure₀ _ ![x, y] t)))⟩ L) :
    TermDefinableOnMagma L M := by
  obtain ⟨N, e, v, he⟩ := Function.exists_isIdempotentIterate (ufunM M u)
  refine ⟨⟨fun x y ↦ e (v (v (@Term.realize _ G M.FOStructure₀ _ ![x, y] t)))⟩, hsat N e v he,
    ⟨uiter u (3 * N + 1) t, ?_⟩⟩
  funext w
  have hw : ![w 0, w 1] = w := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  show e (v (v (@Term.realize _ G M.FOStructure₀ _ ![w 0, w 1] t))) = _
  rw [hw]
  have hz : ∀ z : G, e (v (v z)) = (ufunM M u)^[3 * N + 1] z := by
    intro z
    rw [he.e_eq, he.v_eq, ← Function.iterate_add_apply, ← Function.iterate_add_apply,
      show N + 1 + N + N = 3 * N + 1 from by omega]
  rw [hz]
  exact (@realize_uiter G M.FOStructure₀ u (3 * N + 1) t w).symm

/-- The `TermDefinableFromFin` wrapper around `termDefinableOnMagma_of_iterate_evv`. -/
theorem termDefinableFromFin_of_iterate_evv {β : Type} {L L' : Law.MagmaLaw β}
    (u : ∀ G : Type, UTerm G) (t : ∀ G : Type, BTerm G)
    (h : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ (N : ℕ) (e v : G → G), Function.IsIdempotentIterate (ufunM M (u G)) N e v →
        @satisfies _ G ⟨fun x y ↦ e (v (v (@Term.realize _ G M.FOStructure₀ _ ![x, y] (t G))))⟩ L) :
    TermDefinableFromFin L L' :=
  fun {G} _ M hM ↦ termDefinableOnMagma_of_iterate_evv M (u G) (t G) (h G M hM)

/-- An iterate of a magma endomorphism is one. Both `e` and `v` are iterates of `u x = x ◇ x`,
which equation 546 forces to be an endomorphism, so both distribute over `◇`. -/
private theorem iterate_endo [Magma G] {u : G → G} (hu : ∀ a b : G, u (a ◇ b) = u a ◇ u b) :
    ∀ (n : ℕ) (a b : G), u^[n] (a ◇ b) = u^[n] a ◇ u^[n] b := by
  intro n
  induction n with
  | zero => intro a b; rfl
  | succ k ih =>
    intro a b
    simp only [Function.iterate_succ_apply', ih, hu]


/-- `u x = x ◇ x` is an endomorphism. This is mediality specialised to the diagonal, and equation
546 proves mediality unaided -- no rotations are needed anywhere in this file. -/
private theorem sq_endo [Magma G] (h : Equation546 G) (x y : G) :
    (x ◇ y) ◇ (x ◇ y) = (x ◇ x) ◇ (y ◇ y) := by
  by_contra nh
  have eq6 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq7 : ((x ◇ y) ◇ (x ◇ y)) ≠ ((x ◇ x) ◇ (y ◇ y)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := by first | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6) | exact superpose eq6 eq6 | exact mod_symm (superpose eq6 eq6)
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X1 ◇ (X2 ◇ X0)) := by first | exact superpose eq10 eq6 | exact mod_symm (superpose eq10 eq6) | exact superpose eq6 eq10 | exact mod_symm (superpose eq6 eq10)
  have eq144 : ((x ◇ x) ◇ (y ◇ y)) ≠ (y ◇ (x ◇ (x ◇ y))) := by first | exact superpose eq13 eq7 | exact mod_symm (superpose eq13 eq7) | exact superpose eq7 eq13 | exact mod_symm (superpose eq7 eq13)
  have eq164 : (y ◇ (x ◇ (x ◇ y))) ≠ (y ◇ (y ◇ (x ◇ x))) := by first | exact superpose eq13 eq144 | exact mod_symm (superpose eq13 eq144) | exact superpose eq144 eq13 | exact mod_symm (superpose eq144 eq13)
  have eq173 : (y ◇ (x ◇ (x ◇ y))) ≠ (y ◇ (x ◇ (x ◇ y))) := by first | exact superpose eq13 eq164 | exact mod_symm (superpose eq13 eq164) | exact superpose eq164 eq13 | exact mod_symm (superpose eq164 eq13)
  first | exact eq173 rfl | exact eq173 _ rfl | exact eq173 _ _ rfl | exact eq173 _ _ _ rfl


/-- Equation 332 `x ◇ y = y ◇ (x ◇ x)` is term-definable from equation 546 over finite magmas, via the term
`x □ y := u^[3N+1] ((x ◇ x) ◇ (y ◇ x))` where `u a = a ◇ a`. -/
private theorem aux546_332 [Magma G] (h : Equation546 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, v (e a) ◇ v (e a) = e a) (hvue : ∀ a : G, v (e a ◇ e a) = e a)
    (hw : ∀ a b : G, w a b = (e (v (v ((a ◇ a) ◇ (b ◇ a))))))
    (x y : G) :
    (w x y) =
      (w y (w x x)) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ (v (e X0))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ (e X0))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (v ((X0 ◇ X0) ◇ (X1 ◇ X0))))) := mod_symm (hw ..)
  have eq21 : (w x y) ≠ (w y (w x x)) := mod_symm nh
  have eq26 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq27 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq28 (X0 : G) : (e X0) = (v (e (X0 ◇ X0))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq29 (X0 : G) : (e X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq17 eq28 | exact mod_symm (superpose eq17 eq28) | exact superpose eq28 eq17 | exact mod_symm (superpose eq28 eq17)
  have eq30 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq27 | exact mod_symm (superpose eq14 eq27) | exact superpose eq27 eq14 | exact mod_symm (superpose eq27 eq14)
  have eq31 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq32 (X0 X1 : G) : (v ((e X0) ◇ X1)) = ((e (v X0)) ◇ (v X1)) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq33 (X0 X1 : G) : (v (((e X0) ◇ (e X0)) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq34 (X0 X1 : G) : (v (X1 ◇ (e X0))) = ((v X1) ◇ (e (v X0))) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq35 (X0 X1 : G) : (v (X1 ◇ ((e X0) ◇ (e X0)))) = ((v X1) ◇ (e X0)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq36 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X1 ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35) | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14)
  have eq37 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v ((e (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq33 | exact mod_symm (superpose eq14 eq33) | exact superpose eq33 eq14 | exact mod_symm (superpose eq33 eq14)
  have eq39 (X0 : G) : (e (v X0)) = (e (v (v (X0 ◇ X0)))) := by first | exact superpose eq15 eq29 | exact mod_symm (superpose eq15 eq29) | exact superpose eq29 eq15 | exact mod_symm (superpose eq29 eq15)
  have eq64 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq30 eq17 | exact mod_symm (superpose eq30 eq17) | exact superpose eq17 eq30 | exact mod_symm (superpose eq17 eq30)
  have eq67 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq17 eq64 | exact mod_symm (superpose eq17 eq64) | exact superpose eq64 eq17 | exact mod_symm (superpose eq64 eq17)
  have eq75 (X0 X1 : G) : ((v (e X0)) ◇ ((v (e X0)) ◇ (X1 ◇ (e X0)))) = X1 := by first | exact superpose eq18 eq13 | exact mod_symm (superpose eq18 eq13) | exact superpose eq13 eq18 | exact mod_symm (superpose eq13 eq18)
  have eq77 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X2 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq78 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq79 (X0 X1 : G) : ((e (v X0)) ◇ ((e (v X0)) ◇ (X1 ◇ (e X0)))) = X1 := by first | exact superpose eq17 eq75 | exact mod_symm (superpose eq17 eq75) | exact superpose eq75 eq17 | exact mod_symm (superpose eq75 eq17)
  have eq83 (X0 : G) : (v (e X0)) = ((e X0) ◇ (v (e X0))) := by first | exact superpose eq18 eq78 | exact mod_symm (superpose eq18 eq78) | exact superpose eq78 eq18 | exact mod_symm (superpose eq78 eq18)
  have eq85 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X1 ◇ (X2 ◇ X0)) := by first | exact superpose eq78 eq13 | exact mod_symm (superpose eq78 eq13) | exact superpose eq13 eq78 | exact mod_symm (superpose eq13 eq78)
  have eq89 (X0 : G) : (e (v X0)) = ((e X0) ◇ (e (v X0))) := by first | exact superpose eq17 eq83 | exact mod_symm (superpose eq17 eq83) | exact superpose eq83 eq17 | exact mod_symm (superpose eq83 eq17)
  have eq92 (X0 : G) : (e (v X0)) = (e (X0 ◇ (v X0))) := by first | exact superpose eq14 eq89 | exact mod_symm (superpose eq14 eq89) | exact superpose eq89 eq14 | exact mod_symm (superpose eq89 eq14)
  have eq93 (X0 X1 : G) : (w (e X0) X1) = (e (v (v ((e (X0 ◇ X0)) ◇ (X1 ◇ (e X0)))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq94 (X0 X1 : G) : (w (v X0) X1) = (e (v (v ((v (X0 ◇ X0)) ◇ (X1 ◇ (v X0)))))) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  have eq95 (X0 X1 : G) : (w (v (e X0)) X1) = (e (v (v ((e X0) ◇ (X1 ◇ (v (e X0))))))) := by first | exact superpose eq18 eq20 | exact mod_symm (superpose eq18 eq20) | exact superpose eq20 eq18 | exact mod_symm (superpose eq20 eq18)
  have eq98 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (v (((e X1) ◇ (e X1)) ◇ (e (X0 ◇ X1)))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq99 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (((v X1) ◇ (v X1)) ◇ (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  have eq103 (X0 X1 : G) : (w X0 X1) = (e (w X0 X1)) := by first | exact superpose eq20 eq16 | exact mod_symm (superpose eq20 eq16) | exact superpose eq16 eq20 | exact mod_symm (superpose eq16 eq20)
  have eq104 (X0 X1 : G) : (e (v (v (v ((X0 ◇ X0) ◇ (X1 ◇ X0)))))) = (v (w X0 X1)) := by first | exact superpose eq20 eq17 | exact mod_symm (superpose eq20 eq17) | exact superpose eq17 eq20 | exact mod_symm (superpose eq17 eq20)
  have eq106 (X0 X1 : G) : (w X0 X1) = (v ((w X0 X1) ◇ (w X0 X1))) := by first | exact superpose eq20 eq19 | exact mod_symm (superpose eq20 eq19) | exact superpose eq19 eq20 | exact mod_symm (superpose eq19 eq20)
  have eq110 (X0 X1 : G) : (v (w X0 X1)) = (e (v (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by first | exact superpose eq85 eq104 | exact mod_symm (superpose eq85 eq104) | exact superpose eq104 eq85 | exact mod_symm (superpose eq104 eq85)
  have eq114 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v ((v (X1 ◇ X1)) ◇ (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq99 | exact mod_symm (superpose eq15 eq99) | exact superpose eq99 eq15 | exact mod_symm (superpose eq99 eq15)
  have eq115 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (v ((e (X1 ◇ X1)) ◇ (e (X0 ◇ X1)))))) := by first | exact superpose eq14 eq98 | exact mod_symm (superpose eq14 eq98) | exact superpose eq98 eq14 | exact mod_symm (superpose eq98 eq14)
  have eq117 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e X0) ◇ (X1 ◇ (e (v X0))))))) := by first | exact superpose eq17 eq95 | exact mod_symm (superpose eq17 eq95) | exact superpose eq95 eq17 | exact mod_symm (superpose eq95 eq17)
  have eq118 (X0 X1 : G) : (w (v X0) X1) = (e (v (v ((v X0) ◇ (X1 ◇ (v (X0 ◇ X0))))))) := by first | exact superpose eq85 eq94 | exact mod_symm (superpose eq85 eq94) | exact superpose eq94 eq85 | exact mod_symm (superpose eq94 eq85)
  have eq119 (X0 X1 : G) : (w (e X0) X1) = (e (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq37 eq93 | exact mod_symm (superpose eq37 eq93) | exact superpose eq93 eq37 | exact mod_symm (superpose eq93 eq37)
  have eq122 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (v ((X1 ◇ X1) ◇ (X0 ◇ X1)))))) := by first | exact superpose eq15 eq114 | exact mod_symm (superpose eq15 eq114) | exact superpose eq114 eq15 | exact mod_symm (superpose eq114 eq15)
  have eq123 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (v (e (X0 ◇ X1)))))) := by first | exact superpose eq37 eq115 | exact mod_symm (superpose eq37 eq115) | exact superpose eq115 eq37 | exact mod_symm (superpose eq115 eq37)
  have eq125 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (v (X1 ◇ (X0 ◇ (X1 ◇ X1))))))) := by first | exact superpose eq85 eq122 | exact mod_symm (superpose eq85 eq122) | exact superpose eq122 eq85 | exact mod_symm (superpose eq122 eq85)
  have eq126 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (e (v (X0 ◇ X1)))))) := by first | exact superpose eq17 eq123 | exact mod_symm (superpose eq17 eq123) | exact superpose eq123 eq17 | exact mod_symm (superpose eq123 eq17)
  have eq127 (X0 X1 : G) : (w (v X1) (v X0)) = (v (w X1 X0)) := by first | exact superpose eq110 eq125 | exact mod_symm (superpose eq110 eq125) | exact superpose eq125 eq110 | exact mod_symm (superpose eq125 eq110)
  have eq128 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (v (X0 ◇ X1))))) := by first | exact superpose eq67 eq126 | exact mod_symm (superpose eq67 eq126) | exact superpose eq126 eq67 | exact mod_symm (superpose eq126 eq67)
  have eq147 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq31 eq17 | exact mod_symm (superpose eq31 eq17) | exact superpose eq17 eq31 | exact mod_symm (superpose eq17 eq31)
  have eq152 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq17 eq147 | exact mod_symm (superpose eq17 eq147) | exact superpose eq147 eq17 | exact mod_symm (superpose eq147 eq17)
  have eq193 (X0 X1 : G) : (v (w (e X0) X1)) = (w (e (v X0)) (v X1)) := by first | exact superpose eq17 eq127 | exact mod_symm (superpose eq17 eq127) | exact superpose eq127 eq17 | exact mod_symm (superpose eq127 eq17)
  have eq203 (X0 : G) : (w X0 X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq39 eq20 | exact mod_symm (superpose eq39 eq20) | exact superpose eq20 eq39 | exact mod_symm (superpose eq20 eq39)
  have eq217 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq29 eq203 | exact mod_symm (superpose eq29 eq203) | exact superpose eq203 eq29 | exact mod_symm (superpose eq203 eq29)
  have eq233 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X2 := by first | exact superpose eq78 eq77 | exact mod_symm (superpose eq78 eq77) | exact superpose eq77 eq78 | exact mod_symm (superpose eq77 eq78)
  have eq238 (X0 X1 : G) : (e (v (v X0))) = (w (X1 ◇ X0) X1) := by first | exact superpose eq77 eq20 | exact mod_symm (superpose eq77 eq20) | exact superpose eq20 eq77 | exact mod_symm (superpose eq20 eq77)
  have eq258 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq217 eq21 | exact mod_symm (superpose eq217 eq21) | exact superpose eq21 eq217 | exact mod_symm (superpose eq21 eq217)
  have eq364 (X0 X1 X2 : G) : (e (v (v (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) = (w X0 X2) := by first | exact superpose eq13 eq238 | exact mod_symm (superpose eq13 eq238) | exact superpose eq238 eq13 | exact mod_symm (superpose eq238 eq13)
  have eq609 (X0 X1 X2 : G) : (X2 ◇ (v (X0 ◇ X1))) = ((v X1) ◇ ((v X0) ◇ X2)) := by first | exact superpose eq15 eq85 | exact mod_symm (superpose eq15 eq85) | exact superpose eq85 eq15 | exact mod_symm (superpose eq85 eq15)
  have eq1772 (X0 X1 : G) : (w (e X1) (X0 ◇ (e X1))) = (e (v ((e X1) ◇ (v X0)))) := by first | exact superpose eq78 eq119 | exact mod_symm (superpose eq78 eq119) | exact superpose eq119 eq78 | exact mod_symm (superpose eq119 eq78)
  have eq1774 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (v (e (X0 ◇ X1)))))) := by first | exact superpose eq14 eq119 | exact mod_symm (superpose eq14 eq119) | exact superpose eq119 eq14 | exact mod_symm (superpose eq119 eq14)
  have eq1775 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v ((e (v X1)) ◇ (v (v (X0 ◇ (e X1))))))) := by first | exact superpose eq34 eq119 | exact mod_symm (superpose eq34 eq119) | exact superpose eq119 eq34 | exact mod_symm (superpose eq119 eq34)
  have eq1810 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v ((v X1) ◇ (v (v (X0 ◇ (e X1))))))) := by first | exact superpose eq152 eq1775 | exact mod_symm (superpose eq152 eq1775) | exact superpose eq1775 eq152 | exact mod_symm (superpose eq1775 eq152)
  have eq1811 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (X1 ◇ (v (e (X0 ◇ X1)))))) := by first | exact superpose eq152 eq1774 | exact mod_symm (superpose eq152 eq1774) | exact superpose eq1774 eq152 | exact mod_symm (superpose eq1774 eq152)
  have eq1813 (X0 X1 : G) : (w (e X1) (X0 ◇ (e X1))) = (e (v (X1 ◇ (v X0)))) := by first | exact superpose eq152 eq1772 | exact mod_symm (superpose eq152 eq1772) | exact superpose eq1772 eq152 | exact mod_symm (superpose eq1772 eq152)
  have eq1819 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq15 eq1810 | exact mod_symm (superpose eq15 eq1810) | exact superpose eq1810 eq15 | exact mod_symm (superpose eq1810 eq15)
  have eq1820 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (X1 ◇ (e (v (X0 ◇ X1)))))) := by first | exact superpose eq17 eq1811 | exact mod_symm (superpose eq17 eq1811) | exact superpose eq1811 eq17 | exact mod_symm (superpose eq1811 eq17)
  have eq1824 (X0 X1 : G) : (v (w (e X1) X0)) = (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq193 eq1819 | exact mod_symm (superpose eq193 eq1819) | exact superpose eq1819 eq193 | exact mod_symm (superpose eq1819 eq193)
  have eq1825 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (X1 ◇ (v (X0 ◇ X1))))) := by first | exact superpose eq67 eq1820 | exact mod_symm (superpose eq67 eq1820) | exact superpose eq1820 eq67 | exact mod_symm (superpose eq1820 eq67)
  have eq1864 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (e (v ((e (v X0)) ◇ (v (X1 ◇ (X0 ◇ (v X0))))))) := by first | exact superpose eq92 eq128 | exact mod_symm (superpose eq92 eq128) | exact superpose eq128 eq92 | exact mod_symm (superpose eq128 eq92)
  have eq1891 (X0 X1 : G) : (w (e (v X1)) (e (v X0))) = (e (v ((e (v X1)) ◇ (v (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq128 | exact mod_symm (superpose eq15 eq128) | exact superpose eq128 eq15 | exact mod_symm (superpose eq128 eq15)
  have eq1893 (X0 X1 : G) : (w (e (e (v X1))) (e (v X0))) = (e (v ((e (e (v X1))) ◇ (v (v (X0 ◇ (e X1))))))) := by first | exact superpose eq34 eq128 | exact mod_symm (superpose eq34 eq128) | exact superpose eq128 eq34 | exact mod_symm (superpose eq128 eq34)
  have eq1903 (X0 X1 X2 : G) : (v ((e ((e X0) ◇ (v (X1 ◇ X0)))) ◇ X2)) = ((w (e X0) (e X1)) ◇ (v X2)) := by first | exact superpose eq128 eq32 | exact mod_symm (superpose eq128 eq32) | exact superpose eq32 eq128 | exact mod_symm (superpose eq32 eq128)
  have eq1923 (X0 X1 X2 : G) : ((w (e X0) (e X1)) ◇ (v X2)) = (v ((e (X0 ◇ (v (X1 ◇ X0)))) ◇ X2)) := by first | exact superpose eq31 eq1903 | exact mod_symm (superpose eq31 eq1903) | exact superpose eq1903 eq31 | exact mod_symm (superpose eq1903 eq31)
  have eq1932 (X0 X1 : G) : (e (v ((e (v X1)) ◇ (v (v (X0 ◇ (e X1))))))) = (w (e (e (v X1))) (e (v X0))) := by first | exact superpose eq152 eq1893 | exact mod_symm (superpose eq152 eq1893) | exact superpose eq1893 eq152 | exact mod_symm (superpose eq1893 eq152)
  have eq1934 (X0 X1 : G) : (w (e (v X1)) (e (v X0))) = (e (v ((v X1) ◇ (v (v (X0 ◇ X1)))))) := by first | exact superpose eq152 eq1891 | exact mod_symm (superpose eq152 eq1891) | exact superpose eq1891 eq152 | exact mod_symm (superpose eq1891 eq152)
  have eq1959 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (e (v ((v X0) ◇ (v (X1 ◇ (X0 ◇ (v X0))))))) := by first | exact superpose eq152 eq1864 | exact mod_symm (superpose eq152 eq1864) | exact superpose eq1864 eq152 | exact mod_symm (superpose eq1864 eq152)
  have eq1966 (X0 X1 : G) : (e (v ((e (v X1)) ◇ (v (v (X0 ◇ (e X1))))))) = (w (e (v X1)) (e (v X0))) := by first | exact superpose eq16 eq1932 | exact mod_symm (superpose eq16 eq1932) | exact superpose eq1932 eq16 | exact mod_symm (superpose eq1932 eq16)
  have eq1968 (X0 X1 : G) : (w (e (v X1)) (e (v X0))) = (e (v (v (X1 ◇ (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq1934 | exact mod_symm (superpose eq15 eq1934) | exact superpose eq1934 eq15 | exact mod_symm (superpose eq1934 eq15)
  have eq1977 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ (v X0))))))) := by first | exact superpose eq15 eq1959 | exact mod_symm (superpose eq15 eq1959) | exact superpose eq1959 eq15 | exact mod_symm (superpose eq1959 eq15)
  have eq1982 (X0 X1 : G) : (e (v ((v X1) ◇ (v (v (X0 ◇ (e X1))))))) = (w (e (v X1)) (e (v X0))) := by first | exact superpose eq152 eq1966 | exact mod_symm (superpose eq152 eq1966) | exact superpose eq1966 eq152 | exact mod_symm (superpose eq1966 eq152)
  have eq1989 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (w X1 (v X0)) := by first | exact superpose eq364 eq1977 | exact mod_symm (superpose eq364 eq1977) | exact superpose eq1977 eq364 | exact mod_symm (superpose eq1977 eq364)
  have eq1993 (X0 X1 : G) : (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) = (w (e (v X1)) (e (v X0))) := by first | exact superpose eq15 eq1982 | exact mod_symm (superpose eq15 eq1982) | exact superpose eq1982 eq15 | exact mod_symm (superpose eq1982 eq15)
  have eq2000 (X0 X1 : G) : (w (v X0) (v X1)) = (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq1989 eq1993 | exact mod_symm (superpose eq1989 eq1993) | exact superpose eq1993 eq1989 | exact mod_symm (superpose eq1993 eq1989)
  have eq2005 (X0 X1 : G) : (w (v X0) (v X1)) = (v (w (e X1) X0)) := by first | exact superpose eq1824 eq2000 | exact mod_symm (superpose eq1824 eq2000) | exact superpose eq2000 eq1824 | exact mod_symm (superpose eq2000 eq1824)
  have eq2007 (X0 X1 : G) : (v (w X0 X1)) = (v (w (e X1) X0)) := by first | exact superpose eq127 eq2005 | exact mod_symm (superpose eq127 eq2005) | exact superpose eq2005 eq127 | exact mod_symm (superpose eq2005 eq127)
  have eq2010 (X0 X1 X2 : G) : (v (w (e (X0 ◇ X1)) X2)) = (v (w X2 ((e X0) ◇ X1))) := by first | exact superpose eq31 eq2007 | exact mod_symm (superpose eq31 eq2007) | exact superpose eq2007 eq31 | exact mod_symm (superpose eq2007 eq31)
  have eq2011 (X0 X1 : G) : (v (w (e X0) X1)) = (v (w X1 (e X0))) := by first | exact superpose eq16 eq2007 | exact mod_symm (superpose eq16 eq2007) | exact superpose eq2007 eq16 | exact mod_symm (superpose eq2007 eq16)
  have eq2026 (X0 X1 X2 : G) : ((v (w X0 X1)) ◇ (v X2)) = (v ((w (e X1) X0) ◇ X2)) := by first | exact superpose eq2007 eq15 | exact mod_symm (superpose eq2007 eq15) | exact superpose eq15 eq2007 | exact mod_symm (superpose eq15 eq2007)
  have eq2027 (X0 X1 X2 : G) : ((v X2) ◇ (v (w X0 X1))) = (v (X2 ◇ (w (e X1) X0))) := by first | exact superpose eq2007 eq15 | exact mod_symm (superpose eq2007 eq15) | exact superpose eq15 eq2007 | exact mod_symm (superpose eq15 eq2007)
  have eq2053 (X0 X1 X2 : G) : (v (X2 ◇ (w X0 X1))) = (v (X2 ◇ (w (e X1) X0))) := by first | exact superpose eq15 eq2027 | exact mod_symm (superpose eq15 eq2027) | exact superpose eq2027 eq15 | exact mod_symm (superpose eq2027 eq15)
  have eq2054 (X0 X1 X2 : G) : (v ((w X0 X1) ◇ X2)) = (v ((w (e X1) X0) ◇ X2)) := by first | exact superpose eq15 eq2026 | exact mod_symm (superpose eq15 eq2026) | exact superpose eq2026 eq15 | exact mod_symm (superpose eq2026 eq15)
  have eq2064 (X0 X1 : G) : (v (w X1 X0)) = (v (w X1 (e X0))) := by first | exact superpose eq2007 eq2011 | exact mod_symm (superpose eq2007 eq2011) | exact superpose eq2011 eq2007 | exact mod_symm (superpose eq2011 eq2007)
  have eq2065 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ X1))) = (v (w X2 (X0 ◇ X1))) := by first | exact superpose eq2007 eq2010 | exact mod_symm (superpose eq2007 eq2010) | exact superpose eq2010 eq2007 | exact mod_symm (superpose eq2010 eq2007)
  have eq2104 (X0 X1 X2 : G) : ((v (w X0 X1)) ◇ ((v (w X0 X1)) ◇ (X2 ◇ (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))))) = X2 := by first | exact superpose eq110 eq79 | exact mod_symm (superpose eq110 eq79) | exact superpose eq79 eq110 | exact mod_symm (superpose eq79 eq110)
  have eq2133 (X0 X1 X2 : G) : ((X2 ◇ (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) ◇ (v ((w X0 X1) ◇ (w X0 X1)))) = X2 := by first | exact superpose eq609 eq2104 | exact mod_symm (superpose eq609 eq2104) | exact superpose eq2104 eq609 | exact mod_symm (superpose eq2104 eq609)
  have eq2152 (X0 X1 X2 : G) : ((X2 ◇ (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) ◇ (w X0 X1)) = X2 := by first | exact superpose eq106 eq2133 | exact mod_symm (superpose eq106 eq2133) | exact superpose eq2133 eq106 | exact mod_symm (superpose eq2133 eq106)
  have eq2162 (X0 X1 X2 : G) : ((X2 ◇ (w X1 X0)) ◇ (w X0 X1)) = X2 := by first | exact superpose eq364 eq2152 | exact mod_symm (superpose eq364 eq2152) | exact superpose eq2152 eq364 | exact mod_symm (superpose eq2152 eq364)
  have eq2194 (X0 X1 : G) : (v (w (e X0) X1)) = (v (w (e X1) X0)) := by first | exact superpose eq2064 eq2007 | exact mod_symm (superpose eq2064 eq2007) | exact superpose eq2007 eq2064 | exact mod_symm (superpose eq2007 eq2064)
  have eq2195 (X0 X1 X2 : G) : ((v (w X0 X1)) ◇ (v X2)) = (v ((w X0 (e X1)) ◇ X2)) := by first | exact superpose eq2064 eq15 | exact mod_symm (superpose eq2064 eq15) | exact superpose eq15 eq2064 | exact mod_symm (superpose eq15 eq2064)
  have eq2223 (X0 X1 X2 : G) : (v ((w X0 X1) ◇ X2)) = (v ((w X0 (e X1)) ◇ X2)) := by first | exact superpose eq15 eq2195 | exact mod_symm (superpose eq15 eq2195) | exact superpose eq2195 eq15 | exact mod_symm (superpose eq2195 eq15)
  have eq2224 (X0 X1 : G) : (v (w X0 X1)) = (v (w (e X0) X1)) := by first | exact superpose eq2007 eq2194 | exact mod_symm (superpose eq2007 eq2194) | exact superpose eq2194 eq2007 | exact mod_symm (superpose eq2194 eq2007)
  have eq2288 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v (v ((e ((e X0) ◇ (v (X1 ◇ (e X0))))) ◇ (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq119 eq117 | exact mod_symm (superpose eq119 eq117) | exact superpose eq117 eq119 | exact mod_symm (superpose eq117 eq119)
  have eq2291 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e (v (X0 ◇ X0))) ◇ (X1 ◇ (e (v X0))))))) := by first | exact superpose eq39 eq117 | exact mod_symm (superpose eq39 eq117) | exact superpose eq117 eq39 | exact mod_symm (superpose eq117 eq39)
  have eq2295 (X0 X1 : G) : (w (e (v X1)) (X0 ◇ (e (v X1)))) = (e (v (v ((e X1) ◇ X0)))) := by first | exact superpose eq78 eq117 | exact mod_symm (superpose eq78 eq117) | exact superpose eq117 eq78 | exact mod_symm (superpose eq117 eq78)
  have eq2297 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (v ((e X1) ◇ (e (X0 ◇ (v X1))))))) := by first | exact superpose eq14 eq117 | exact mod_symm (superpose eq14 eq117) | exact superpose eq117 eq14 | exact mod_symm (superpose eq117 eq14)
  have eq2298 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v (v ((e X1) ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq34 eq117 | exact mod_symm (superpose eq34 eq117) | exact superpose eq117 eq34 | exact mod_symm (superpose eq117 eq34)
  have eq2334 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (w (e (v (e X1))) (e (v X0))) := by first | exact superpose eq1968 eq2298 | exact mod_symm (superpose eq1968 eq2298) | exact superpose eq2298 eq1968 | exact mod_symm (superpose eq2298 eq1968)
  have eq2335 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (v (e (X1 ◇ (X0 ◇ (v X1))))))) := by first | exact superpose eq14 eq2297 | exact mod_symm (superpose eq14 eq2297) | exact superpose eq2297 eq14 | exact mod_symm (superpose eq2297 eq14)
  have eq2337 (X0 X1 : G) : (e (v (v ((e X1) ◇ X0)))) = (e (v ((v X1) ◇ (v X0)))) := by first | exact superpose eq1813 eq2295 | exact mod_symm (superpose eq1813 eq2295) | exact superpose eq2295 eq1813 | exact mod_symm (superpose eq2295 eq1813)
  have eq2341 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e (v X0)) ◇ (X1 ◇ (e (v (X0 ◇ X0)))))))) := by first | exact superpose eq85 eq2291 | exact mod_symm (superpose eq85 eq2291) | exact superpose eq2291 eq85 | exact mod_symm (superpose eq2291 eq85)
  have eq2344 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w (e (e X0)) (e X1)) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq1923 eq2288 | exact mod_symm (superpose eq1923 eq2288) | exact superpose eq2288 eq1923 | exact mod_symm (superpose eq2288 eq1923)
  have eq2374 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (w (v X0) (v (e X1))) := by first | exact superpose eq1989 eq2334 | exact mod_symm (superpose eq1989 eq2334) | exact superpose eq2334 eq1989 | exact mod_symm (superpose eq2334 eq1989)
  have eq2375 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (e (v (X1 ◇ (X0 ◇ (v X1))))))) := by first | exact superpose eq17 eq2335 | exact mod_symm (superpose eq17 eq2335) | exact superpose eq2335 eq17 | exact mod_symm (superpose eq2335 eq17)
  have eq2377 (X0 X1 : G) : (e (v (v (X1 ◇ X0)))) = (e (v (v ((e X1) ◇ X0)))) := by first | exact superpose eq15 eq2337 | exact mod_symm (superpose eq15 eq2337) | exact superpose eq2337 eq15 | exact mod_symm (superpose eq2337 eq15)
  have eq2381 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e (v X0)) ◇ (X1 ◇ (e X0)))))) := by first | exact superpose eq29 eq2341 | exact mod_symm (superpose eq29 eq2341) | exact superpose eq2341 eq29 | exact mod_symm (superpose eq2341 eq29)
  have eq2384 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w (e (e X0)) X1) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq2223 eq2344 | exact mod_symm (superpose eq2223 eq2344) | exact superpose eq2344 eq2223 | exact mod_symm (superpose eq2344 eq2223)
  have eq2399 (X0 X1 : G) : (v (w X0 (e X1))) = (w (e (v X1)) (v X0)) := by first | exact superpose eq127 eq2374 | exact mod_symm (superpose eq127 eq2374) | exact superpose eq2374 eq127 | exact mod_symm (superpose eq2374 eq127)
  have eq2400 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (e (v (v (X1 ◇ (X0 ◇ (v X1))))))) := by first | exact superpose eq17 eq2375 | exact mod_symm (superpose eq17 eq2375) | exact superpose eq2375 eq17 | exact mod_symm (superpose eq2375 eq17)
  have eq2404 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((v X0) ◇ (X1 ◇ (e X0)))))) := by first | exact superpose eq2377 eq2381 | exact mod_symm (superpose eq2377 eq2381) | exact superpose eq2381 eq2377 | exact mod_symm (superpose eq2381 eq2377)
  have eq2406 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w X1 (e X0)) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq2054 eq2384 | exact mod_symm (superpose eq2054 eq2384) | exact superpose eq2384 eq2054 | exact mod_symm (superpose eq2384 eq2054)
  have eq2416 (X0 X1 : G) : (v (w X0 X1)) = (w (e (v X1)) (v X0)) := by first | exact superpose eq2064 eq2399 | exact mod_symm (superpose eq2064 eq2399) | exact superpose eq2399 eq2064 | exact mod_symm (superpose eq2399 eq2064)
  have eq2417 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq16 eq2400 | exact mod_symm (superpose eq16 eq2400) | exact superpose eq2400 eq16 | exact mod_symm (superpose eq2400 eq16)
  have eq2418 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e X0) ◇ (X1 ◇ (v X0)))))) := by first | exact superpose eq85 eq2404 | exact mod_symm (superpose eq85 eq2404) | exact superpose eq2404 eq85 | exact mod_symm (superpose eq2404 eq85)
  have eq2420 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w X1 X0) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq2223 eq2406 | exact mod_symm (superpose eq2223 eq2406) | exact superpose eq2406 eq2223 | exact mod_symm (superpose eq2406 eq2223)
  have eq2429 (X0 X1 : G) : (w X0 (v X1)) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq1989 eq2417 | exact mod_symm (superpose eq1989 eq2417) | exact superpose eq2417 eq1989 | exact mod_symm (superpose eq2417 eq1989)
  have eq2430 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v (X0 ◇ (X1 ◇ (v X0)))))) := by first | exact superpose eq2377 eq2418 | exact mod_symm (superpose eq2377 eq2418) | exact superpose eq2418 eq2377 | exact mod_symm (superpose eq2418 eq2377)
  have eq2431 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w X1 X0) ◇ (v (X2 ◇ (w X1 X0)))))) := by first | exact superpose eq2053 eq2420 | exact mod_symm (superpose eq2053 eq2420) | exact superpose eq2420 eq2053 | exact mod_symm (superpose eq2420 eq2053)
  have eq2438 (X0 X1 : G) : (w (e (v X0)) X1) = (w X1 (v X0)) := by first | exact superpose eq2429 eq2430 | exact mod_symm (superpose eq2429 eq2430) | exact superpose eq2430 eq2429 | exact mod_symm (superpose eq2430 eq2429)
  have eq2439 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (w (e (w X1 X0)) (e X2)) := by first | exact superpose eq1825 eq2431 | exact mod_symm (superpose eq1825 eq2431) | exact superpose eq2431 eq1825 | exact mod_symm (superpose eq2431 eq1825)
  have eq2441 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (w (w X1 X0) (e X2)) := by first | exact superpose eq103 eq2439 | exact mod_symm (superpose eq103 eq2439) | exact superpose eq2439 eq103 | exact mod_symm (superpose eq2439 eq103)
  have eq2443 (X0 X1 : G) : (w X1 (e X0)) = (w (e (e X0)) X1) := by first | exact superpose eq19 eq2438 | exact mod_symm (superpose eq19 eq2438) | exact superpose eq2438 eq19 | exact mod_symm (superpose eq2438 eq19)
  have eq2453 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (w X2 (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq119 eq2438 | exact mod_symm (superpose eq119 eq2438) | exact superpose eq2438 eq119 | exact mod_symm (superpose eq2438 eq119)
  have eq2480 (X0 X1 X2 : G) : (w X2 (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w X1 X0) (e X2)) := by first | exact superpose eq2441 eq2453 | exact mod_symm (superpose eq2441 eq2453) | exact superpose eq2453 eq2441 | exact mod_symm (superpose eq2453 eq2441)
  have eq2485 (X0 X1 : G) : (w (e X0) X1) = (w X1 (e X0)) := by first | exact superpose eq16 eq2443 | exact mod_symm (superpose eq16 eq2443) | exact superpose eq2443 eq16 | exact mod_symm (superpose eq2443 eq16)
  have eq2515 (X0 X1 : G) : (w (v (e (X0 ◇ X0))) X1) = (e (v (v ((v (e (X0 ◇ X0))) ◇ (X1 ◇ ((v (e (X0 ◇ X0))) ◇ (e X0))))))) := by first | exact superpose eq36 eq118 | exact mod_symm (superpose eq36 eq118) | exact superpose eq118 eq36 | exact mod_symm (superpose eq118 eq36)
  have eq2554 (X0 X1 : G) : (w X1 (e X0)) = (w (v (e (X0 ◇ X0))) X1) := by first | exact superpose eq364 eq2515 | exact mod_symm (superpose eq364 eq2515) | exact superpose eq2515 eq364 | exact mod_symm (superpose eq2515 eq364)
  have eq2572 (X0 X1 : G) : (w X1 (e X0)) = (w (e (v (X0 ◇ X0))) X1) := by first | exact superpose eq17 eq2554 | exact mod_symm (superpose eq17 eq2554) | exact superpose eq2554 eq17 | exact mod_symm (superpose eq2554 eq17)
  have eq2586 (X0 X1 : G) : (w X1 (e X0)) = (w X1 (v (X0 ◇ X0))) := by first | exact superpose eq2438 eq2572 | exact mod_symm (superpose eq2438 eq2572) | exact superpose eq2572 eq2438 | exact mod_symm (superpose eq2572 eq2438)
  have eq2638 (X0 X1 : G) : (w X0 (e (v X1))) = (w X0 (v X1)) := by first | exact superpose eq2485 eq2438 | exact mod_symm (superpose eq2485 eq2438) | exact superpose eq2438 eq2485 | exact mod_symm (superpose eq2438 eq2485)
  have eq2825 (X0 X1 X2 : G) : (v (w (e (X0 ◇ X1)) X2)) = (v (w (X0 ◇ (e X1)) X2)) := by first | exact superpose eq30 eq2224 | exact mod_symm (superpose eq30 eq2224) | exact superpose eq2224 eq30 | exact mod_symm (superpose eq2224 eq30)
  have eq2827 (X0 X1 X2 : G) : (v (w (e (X0 ◇ X1)) X2)) = (v (w ((e X0) ◇ X1) X2)) := by first | exact superpose eq31 eq2224 | exact mod_symm (superpose eq31 eq2224) | exact superpose eq2224 eq31 | exact mod_symm (superpose eq2224 eq31)
  have eq2901 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ X1))) = (v (w ((e X0) ◇ X1) X2)) := by first | exact superpose eq2007 eq2827 | exact mod_symm (superpose eq2007 eq2827) | exact superpose eq2827 eq2007 | exact mod_symm (superpose eq2827 eq2007)
  have eq2903 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ X1))) = (v (w (X0 ◇ (e X1)) X2)) := by first | exact superpose eq2007 eq2825 | exact mod_symm (superpose eq2007 eq2825) | exact superpose eq2825 eq2007 | exact mod_symm (superpose eq2825 eq2007)
  have eq2982 (X0 X1 X2 : G) : (w X2 X1) = (((w X1 X2) ◇ X0) ◇ X0) := by first | exact superpose eq2162 eq233 | exact mod_symm (superpose eq2162 eq233) | exact superpose eq233 eq2162 | exact mod_symm (superpose eq233 eq2162)
  have eq2983 (X1 X2 : G) : (w X1 X2) = (w X2 X1) := by first | exact superpose eq78 eq2982 | exact mod_symm (superpose eq78 eq2982) | exact superpose eq2982 eq78 | exact mod_symm (superpose eq2982 eq78)
  have eq3063 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w (e X0) X1) (v X2)) := by first | exact superpose eq119 eq2416 | exact mod_symm (superpose eq119 eq2416) | exact superpose eq2416 eq119 | exact mod_symm (superpose eq2416 eq119)
  have eq3072 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w (e (v X1)) (e X0)) := by first | exact superpose eq19 eq2416 | exact mod_symm (superpose eq19 eq2416) | exact superpose eq2416 eq19 | exact mod_symm (superpose eq2416 eq19)
  have eq3111 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w X0 (v X1)) := by first | exact superpose eq1989 eq3072 | exact mod_symm (superpose eq1989 eq3072) | exact superpose eq3072 eq1989 | exact mod_symm (superpose eq3072 eq1989)
  have eq3118 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w X1 X0) (e (v X2))) := by first | exact superpose eq2441 eq3063 | exact mod_symm (superpose eq2441 eq3063) | exact superpose eq3063 eq2441 | exact mod_symm (superpose eq3063 eq2441)
  have eq3131 (X0 X1 : G) : (w X0 (v X1)) = (v (w X1 ((e X0) ◇ X0))) := by first | exact superpose eq2903 eq3111 | exact mod_symm (superpose eq2903 eq3111) | exact superpose eq3111 eq2903 | exact mod_symm (superpose eq3111 eq2903)
  have eq3135 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w X1 X0) (v X2)) := by first | exact superpose eq2638 eq3118 | exact mod_symm (superpose eq2638 eq3118) | exact superpose eq3118 eq2638 | exact mod_symm (superpose eq3118 eq2638)
  have eq3144 (X0 X1 : G) : (w X0 (v X1)) = (v (w X1 (X0 ◇ X0))) := by first | exact superpose eq2065 eq3131 | exact mod_symm (superpose eq2065 eq3131) | exact superpose eq3131 eq2065 | exact mod_symm (superpose eq3131 eq2065)
  have eq3146 (X0 X1 X2 : G) : (w (w X1 X0) (v X2)) = (v (w X2 (X0 ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq2065 eq3135 | exact mod_symm (superpose eq2065 eq3135) | exact superpose eq3135 eq2065 | exact mod_symm (superpose eq3135 eq2065)
  have eq3326 (X0 X1 : G) : (w (v X0) (e X1)) = (v (w X0 (X1 ◇ X1))) := by first | exact superpose eq2586 eq127 | exact mod_symm (superpose eq2586 eq127) | exact superpose eq127 eq2586 | exact mod_symm (superpose eq127 eq2586)
  have eq3327 (X0 X1 : G) : (w (v X0) (e X1)) = (w X1 (v X0)) := by first | exact superpose eq3144 eq3326 | exact mod_symm (superpose eq3144 eq3326) | exact superpose eq3326 eq3144 | exact mod_symm (superpose eq3326 eq3144)
  have eq3364 (X0 X1 : G) : (w (e X0) (e X1)) = (w X1 (e X0)) := by first | exact superpose eq19 eq3327 | exact mod_symm (superpose eq19 eq3327) | exact superpose eq3327 eq19 | exact mod_symm (superpose eq3327 eq19)
  have eq3382 (X0 X1 X2 : G) : (w (v ((e X0) ◇ (v (X1 ◇ (e X0))))) (v X2)) = (w (v X2) (w (e X0) X1)) := by first | exact superpose eq119 eq3327 | exact mod_symm (superpose eq119 eq3327) | exact superpose eq3327 eq119 | exact mod_symm (superpose eq3327 eq119)
  have eq3413 (X0 X1 X2 : G) : (w (v X2) (w (e X0) X1)) = (v (w ((e X0) ◇ (v (X1 ◇ (e X0)))) X2)) := by first | exact superpose eq127 eq3382 | exact mod_symm (superpose eq127 eq3382) | exact superpose eq3382 eq127 | exact mod_symm (superpose eq3382 eq127)
  have eq3426 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ (v (X1 ◇ (e X0)))))) = (w (v X2) (w (e X0) X1)) := by first | exact superpose eq2901 eq3413 | exact mod_symm (superpose eq2901 eq3413) | exact superpose eq3413 eq2901 | exact mod_symm (superpose eq3413 eq2901)
  have eq3434 (X0 X1 X2 : G) : (w (w X1 X0) (v X2)) = (w (v X2) (w (e X0) X1)) := by first | exact superpose eq3146 eq3426 | exact mod_symm (superpose eq3146 eq3426) | exact superpose eq3426 eq3146 | exact mod_symm (superpose eq3426 eq3146)
  have eq3756 (X0 : G) : (e (e X0)) = (w X0 (e X0)) := by first | exact superpose eq3364 eq217 | exact mod_symm (superpose eq3364 eq217) | exact superpose eq217 eq3364 | exact mod_symm (superpose eq217 eq3364)
  have eq3768 (X0 : G) : (e X0) = (w X0 (e X0)) := by first | exact superpose eq16 eq3756 | exact mod_symm (superpose eq16 eq3756) | exact superpose eq3756 eq16 | exact mod_symm (superpose eq3756 eq16)
  have eq3974 (X0 X1 : G) : (w (e X0) X1) = (w (v ((e X0) ◇ (v (X1 ◇ (e X0))))) (w (e X0) X1)) := by first | exact superpose eq119 eq3768 | exact mod_symm (superpose eq119 eq3768) | exact superpose eq3768 eq119 | exact mod_symm (superpose eq3768 eq119)
  have eq4014 (X0 X1 : G) : (w (e X0) X1) = (w (w X1 X0) (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq3434 eq3974 | exact mod_symm (superpose eq3434 eq3974) | exact superpose eq3974 eq3434 | exact mod_symm (superpose eq3974 eq3434)
  have eq4040 (X0 X1 : G) : (w (e X0) X1) = (w (w X1 X0) (e (w X1 X0))) := by first | exact superpose eq2480 eq4014 | exact mod_symm (superpose eq2480 eq4014) | exact superpose eq4014 eq2480 | exact mod_symm (superpose eq4014 eq2480)
  have eq4063 (X0 X1 : G) : (w (e X0) X1) = (e (w X1 X0)) := by first | exact superpose eq3768 eq4040 | exact mod_symm (superpose eq3768 eq4040) | exact superpose eq4040 eq3768 | exact mod_symm (superpose eq4040 eq3768)
  have eq4084 (X0 X1 : G) : (w (e X0) X1) = (w X1 X0) := by first | exact superpose eq103 eq4063 | exact mod_symm (superpose eq103 eq4063) | exact superpose eq4063 eq103 | exact mod_symm (superpose eq4063 eq103)
  have eq4327 (X0 X1 : G) : (w X0 X1) = (w X0 (e X1)) := by first | exact superpose eq4084 eq2983 | exact mod_symm (superpose eq4084 eq2983) | exact superpose eq2983 eq4084 | exact mod_symm (superpose eq2983 eq4084)
  have eq4621 : (w x y) ≠ (w y x) := by first | exact superpose eq4327 eq258 | exact mod_symm (superpose eq4327 eq258) | exact superpose eq258 eq4327 | exact mod_symm (superpose eq258 eq4327)
  subsumption eq4621 eq2983


/-- Equation 3342 `x ◇ y = y ◇ (x ◇ (x ◇ x))` is term-definable from equation 546 over finite magmas, via the term
`x □ y := u^[3N+1] ((x ◇ x) ◇ (y ◇ x))` where `u a = a ◇ a`. -/
private theorem aux546_3342 [Magma G] (h : Equation546 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, v (e a) ◇ v (e a) = e a) (hvue : ∀ a : G, v (e a ◇ e a) = e a)
    (hw : ∀ a b : G, w a b = (e (v (v ((a ◇ a) ◇ (b ◇ a))))))
    (x y : G) :
    (w x y) =
      (w y (w x (w x x))) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ (v (e X0))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ (e X0))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (v ((X0 ◇ X0) ◇ (X1 ◇ X0))))) := mod_symm (hw ..)
  have eq21 : (w x y) ≠ (w y (w x (w x x))) := mod_symm nh
  have eq26 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq27 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq28 (X0 : G) : (e X0) = (v (e (X0 ◇ X0))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq29 (X0 : G) : (e X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq17 eq28 | exact mod_symm (superpose eq17 eq28) | exact superpose eq28 eq17 | exact mod_symm (superpose eq28 eq17)
  have eq30 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq27 | exact mod_symm (superpose eq14 eq27) | exact superpose eq27 eq14 | exact mod_symm (superpose eq27 eq14)
  have eq31 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq32 (X0 X1 : G) : (v ((e X0) ◇ X1)) = ((e (v X0)) ◇ (v X1)) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq33 (X0 X1 : G) : (v (((e X0) ◇ (e X0)) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq34 (X0 X1 : G) : (v (X1 ◇ (e X0))) = ((v X1) ◇ (e (v X0))) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq35 (X0 X1 : G) : (v (X1 ◇ ((e X0) ◇ (e X0)))) = ((v X1) ◇ (e X0)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq36 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X1 ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35) | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14)
  have eq37 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v ((e (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq33 | exact mod_symm (superpose eq14 eq33) | exact superpose eq33 eq14 | exact mod_symm (superpose eq33 eq14)
  have eq39 (X0 : G) : (e (v X0)) = (e (v (v (X0 ◇ X0)))) := by first | exact superpose eq15 eq29 | exact mod_symm (superpose eq15 eq29) | exact superpose eq29 eq15 | exact mod_symm (superpose eq29 eq15)
  have eq64 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq30 eq17 | exact mod_symm (superpose eq30 eq17) | exact superpose eq17 eq30 | exact mod_symm (superpose eq17 eq30)
  have eq67 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq17 eq64 | exact mod_symm (superpose eq17 eq64) | exact superpose eq64 eq17 | exact mod_symm (superpose eq64 eq17)
  have eq75 (X0 X1 : G) : ((v (e X0)) ◇ ((v (e X0)) ◇ (X1 ◇ (e X0)))) = X1 := by first | exact superpose eq18 eq13 | exact mod_symm (superpose eq18 eq13) | exact superpose eq13 eq18 | exact mod_symm (superpose eq13 eq18)
  have eq77 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X2 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq78 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq79 (X0 X1 : G) : ((e (v X0)) ◇ ((e (v X0)) ◇ (X1 ◇ (e X0)))) = X1 := by first | exact superpose eq17 eq75 | exact mod_symm (superpose eq17 eq75) | exact superpose eq75 eq17 | exact mod_symm (superpose eq75 eq17)
  have eq83 (X0 : G) : (v (e X0)) = ((e X0) ◇ (v (e X0))) := by first | exact superpose eq18 eq78 | exact mod_symm (superpose eq18 eq78) | exact superpose eq78 eq18 | exact mod_symm (superpose eq78 eq18)
  have eq85 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X1 ◇ (X2 ◇ X0)) := by first | exact superpose eq78 eq13 | exact mod_symm (superpose eq78 eq13) | exact superpose eq13 eq78 | exact mod_symm (superpose eq13 eq78)
  have eq89 (X0 : G) : (e (v X0)) = ((e X0) ◇ (e (v X0))) := by first | exact superpose eq17 eq83 | exact mod_symm (superpose eq17 eq83) | exact superpose eq83 eq17 | exact mod_symm (superpose eq83 eq17)
  have eq92 (X0 : G) : (e (v X0)) = (e (X0 ◇ (v X0))) := by first | exact superpose eq14 eq89 | exact mod_symm (superpose eq14 eq89) | exact superpose eq89 eq14 | exact mod_symm (superpose eq89 eq14)
  have eq93 (X0 X1 : G) : (w (e X0) X1) = (e (v (v ((e (X0 ◇ X0)) ◇ (X1 ◇ (e X0)))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq94 (X0 X1 : G) : (w (v X0) X1) = (e (v (v ((v (X0 ◇ X0)) ◇ (X1 ◇ (v X0)))))) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  have eq95 (X0 X1 : G) : (w (v (e X0)) X1) = (e (v (v ((e X0) ◇ (X1 ◇ (v (e X0))))))) := by first | exact superpose eq18 eq20 | exact mod_symm (superpose eq18 eq20) | exact superpose eq20 eq18 | exact mod_symm (superpose eq20 eq18)
  have eq98 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (v (((e X1) ◇ (e X1)) ◇ (e (X0 ◇ X1)))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq99 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (((v X1) ◇ (v X1)) ◇ (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  have eq103 (X0 X1 : G) : (w X0 X1) = (e (w X0 X1)) := by first | exact superpose eq20 eq16 | exact mod_symm (superpose eq20 eq16) | exact superpose eq16 eq20 | exact mod_symm (superpose eq16 eq20)
  have eq104 (X0 X1 : G) : (e (v (v (v ((X0 ◇ X0) ◇ (X1 ◇ X0)))))) = (v (w X0 X1)) := by first | exact superpose eq20 eq17 | exact mod_symm (superpose eq20 eq17) | exact superpose eq17 eq20 | exact mod_symm (superpose eq17 eq20)
  have eq106 (X0 X1 : G) : (w X0 X1) = (v ((w X0 X1) ◇ (w X0 X1))) := by first | exact superpose eq20 eq19 | exact mod_symm (superpose eq20 eq19) | exact superpose eq19 eq20 | exact mod_symm (superpose eq19 eq20)
  have eq110 (X0 X1 : G) : (v (w X0 X1)) = (e (v (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by first | exact superpose eq85 eq104 | exact mod_symm (superpose eq85 eq104) | exact superpose eq104 eq85 | exact mod_symm (superpose eq104 eq85)
  have eq114 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v ((v (X1 ◇ X1)) ◇ (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq99 | exact mod_symm (superpose eq15 eq99) | exact superpose eq99 eq15 | exact mod_symm (superpose eq99 eq15)
  have eq115 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (v ((e (X1 ◇ X1)) ◇ (e (X0 ◇ X1)))))) := by first | exact superpose eq14 eq98 | exact mod_symm (superpose eq14 eq98) | exact superpose eq98 eq14 | exact mod_symm (superpose eq98 eq14)
  have eq117 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e X0) ◇ (X1 ◇ (e (v X0))))))) := by first | exact superpose eq17 eq95 | exact mod_symm (superpose eq17 eq95) | exact superpose eq95 eq17 | exact mod_symm (superpose eq95 eq17)
  have eq118 (X0 X1 : G) : (w (v X0) X1) = (e (v (v ((v X0) ◇ (X1 ◇ (v (X0 ◇ X0))))))) := by first | exact superpose eq85 eq94 | exact mod_symm (superpose eq85 eq94) | exact superpose eq94 eq85 | exact mod_symm (superpose eq94 eq85)
  have eq119 (X0 X1 : G) : (w (e X0) X1) = (e (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq37 eq93 | exact mod_symm (superpose eq37 eq93) | exact superpose eq93 eq37 | exact mod_symm (superpose eq93 eq37)
  have eq122 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (v ((X1 ◇ X1) ◇ (X0 ◇ X1)))))) := by first | exact superpose eq15 eq114 | exact mod_symm (superpose eq15 eq114) | exact superpose eq114 eq15 | exact mod_symm (superpose eq114 eq15)
  have eq123 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (v (e (X0 ◇ X1)))))) := by first | exact superpose eq37 eq115 | exact mod_symm (superpose eq37 eq115) | exact superpose eq115 eq37 | exact mod_symm (superpose eq115 eq37)
  have eq125 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (v (X1 ◇ (X0 ◇ (X1 ◇ X1))))))) := by first | exact superpose eq85 eq122 | exact mod_symm (superpose eq85 eq122) | exact superpose eq122 eq85 | exact mod_symm (superpose eq122 eq85)
  have eq126 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (e (v (X0 ◇ X1)))))) := by first | exact superpose eq17 eq123 | exact mod_symm (superpose eq17 eq123) | exact superpose eq123 eq17 | exact mod_symm (superpose eq123 eq17)
  have eq127 (X0 X1 : G) : (w (v X1) (v X0)) = (v (w X1 X0)) := by first | exact superpose eq110 eq125 | exact mod_symm (superpose eq110 eq125) | exact superpose eq125 eq110 | exact mod_symm (superpose eq125 eq110)
  have eq128 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (v (X0 ◇ X1))))) := by first | exact superpose eq67 eq126 | exact mod_symm (superpose eq67 eq126) | exact superpose eq126 eq67 | exact mod_symm (superpose eq126 eq67)
  have eq147 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq31 eq17 | exact mod_symm (superpose eq31 eq17) | exact superpose eq17 eq31 | exact mod_symm (superpose eq17 eq31)
  have eq152 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq17 eq147 | exact mod_symm (superpose eq17 eq147) | exact superpose eq147 eq17 | exact mod_symm (superpose eq147 eq17)
  have eq193 (X0 X1 : G) : (v (w (e X0) X1)) = (w (e (v X0)) (v X1)) := by first | exact superpose eq17 eq127 | exact mod_symm (superpose eq17 eq127) | exact superpose eq127 eq17 | exact mod_symm (superpose eq127 eq17)
  have eq203 (X0 : G) : (w X0 X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq39 eq20 | exact mod_symm (superpose eq39 eq20) | exact superpose eq20 eq39 | exact mod_symm (superpose eq20 eq39)
  have eq217 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq29 eq203 | exact mod_symm (superpose eq29 eq203) | exact superpose eq203 eq29 | exact mod_symm (superpose eq203 eq29)
  have eq233 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X2 := by first | exact superpose eq78 eq77 | exact mod_symm (superpose eq78 eq77) | exact superpose eq77 eq78 | exact mod_symm (superpose eq77 eq78)
  have eq238 (X0 X1 : G) : (e (v (v X0))) = (w (X1 ◇ X0) X1) := by first | exact superpose eq77 eq20 | exact mod_symm (superpose eq77 eq20) | exact superpose eq20 eq77 | exact mod_symm (superpose eq20 eq77)
  have eq258 : (w x y) ≠ (w y (w x (e x))) := by first | exact superpose eq217 eq21 | exact mod_symm (superpose eq217 eq21) | exact superpose eq21 eq217 | exact mod_symm (superpose eq21 eq217)
  have eq364 (X0 X1 X2 : G) : (e (v (v (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) = (w X0 X2) := by first | exact superpose eq13 eq238 | exact mod_symm (superpose eq13 eq238) | exact superpose eq238 eq13 | exact mod_symm (superpose eq238 eq13)
  have eq609 (X0 X1 X2 : G) : (X2 ◇ (v (X0 ◇ X1))) = ((v X1) ◇ ((v X0) ◇ X2)) := by first | exact superpose eq15 eq85 | exact mod_symm (superpose eq15 eq85) | exact superpose eq85 eq15 | exact mod_symm (superpose eq85 eq15)
  have eq1772 (X0 X1 : G) : (w (e X1) (X0 ◇ (e X1))) = (e (v ((e X1) ◇ (v X0)))) := by first | exact superpose eq78 eq119 | exact mod_symm (superpose eq78 eq119) | exact superpose eq119 eq78 | exact mod_symm (superpose eq119 eq78)
  have eq1774 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (v (e (X0 ◇ X1)))))) := by first | exact superpose eq14 eq119 | exact mod_symm (superpose eq14 eq119) | exact superpose eq119 eq14 | exact mod_symm (superpose eq119 eq14)
  have eq1775 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v ((e (v X1)) ◇ (v (v (X0 ◇ (e X1))))))) := by first | exact superpose eq34 eq119 | exact mod_symm (superpose eq34 eq119) | exact superpose eq119 eq34 | exact mod_symm (superpose eq119 eq34)
  have eq1810 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v ((v X1) ◇ (v (v (X0 ◇ (e X1))))))) := by first | exact superpose eq152 eq1775 | exact mod_symm (superpose eq152 eq1775) | exact superpose eq1775 eq152 | exact mod_symm (superpose eq1775 eq152)
  have eq1811 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (X1 ◇ (v (e (X0 ◇ X1)))))) := by first | exact superpose eq152 eq1774 | exact mod_symm (superpose eq152 eq1774) | exact superpose eq1774 eq152 | exact mod_symm (superpose eq1774 eq152)
  have eq1813 (X0 X1 : G) : (w (e X1) (X0 ◇ (e X1))) = (e (v (X1 ◇ (v X0)))) := by first | exact superpose eq152 eq1772 | exact mod_symm (superpose eq152 eq1772) | exact superpose eq1772 eq152 | exact mod_symm (superpose eq1772 eq152)
  have eq1819 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq15 eq1810 | exact mod_symm (superpose eq15 eq1810) | exact superpose eq1810 eq15 | exact mod_symm (superpose eq1810 eq15)
  have eq1820 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (X1 ◇ (e (v (X0 ◇ X1)))))) := by first | exact superpose eq17 eq1811 | exact mod_symm (superpose eq17 eq1811) | exact superpose eq1811 eq17 | exact mod_symm (superpose eq1811 eq17)
  have eq1824 (X0 X1 : G) : (v (w (e X1) X0)) = (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq193 eq1819 | exact mod_symm (superpose eq193 eq1819) | exact superpose eq1819 eq193 | exact mod_symm (superpose eq1819 eq193)
  have eq1825 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (X1 ◇ (v (X0 ◇ X1))))) := by first | exact superpose eq67 eq1820 | exact mod_symm (superpose eq67 eq1820) | exact superpose eq1820 eq67 | exact mod_symm (superpose eq1820 eq67)
  have eq1864 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (e (v ((e (v X0)) ◇ (v (X1 ◇ (X0 ◇ (v X0))))))) := by first | exact superpose eq92 eq128 | exact mod_symm (superpose eq92 eq128) | exact superpose eq128 eq92 | exact mod_symm (superpose eq128 eq92)
  have eq1891 (X0 X1 : G) : (w (e (v X1)) (e (v X0))) = (e (v ((e (v X1)) ◇ (v (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq128 | exact mod_symm (superpose eq15 eq128) | exact superpose eq128 eq15 | exact mod_symm (superpose eq128 eq15)
  have eq1893 (X0 X1 : G) : (w (e (e (v X1))) (e (v X0))) = (e (v ((e (e (v X1))) ◇ (v (v (X0 ◇ (e X1))))))) := by first | exact superpose eq34 eq128 | exact mod_symm (superpose eq34 eq128) | exact superpose eq128 eq34 | exact mod_symm (superpose eq128 eq34)
  have eq1903 (X0 X1 X2 : G) : (v ((e ((e X0) ◇ (v (X1 ◇ X0)))) ◇ X2)) = ((w (e X0) (e X1)) ◇ (v X2)) := by first | exact superpose eq128 eq32 | exact mod_symm (superpose eq128 eq32) | exact superpose eq32 eq128 | exact mod_symm (superpose eq32 eq128)
  have eq1923 (X0 X1 X2 : G) : ((w (e X0) (e X1)) ◇ (v X2)) = (v ((e (X0 ◇ (v (X1 ◇ X0)))) ◇ X2)) := by first | exact superpose eq31 eq1903 | exact mod_symm (superpose eq31 eq1903) | exact superpose eq1903 eq31 | exact mod_symm (superpose eq1903 eq31)
  have eq1932 (X0 X1 : G) : (e (v ((e (v X1)) ◇ (v (v (X0 ◇ (e X1))))))) = (w (e (e (v X1))) (e (v X0))) := by first | exact superpose eq152 eq1893 | exact mod_symm (superpose eq152 eq1893) | exact superpose eq1893 eq152 | exact mod_symm (superpose eq1893 eq152)
  have eq1934 (X0 X1 : G) : (w (e (v X1)) (e (v X0))) = (e (v ((v X1) ◇ (v (v (X0 ◇ X1)))))) := by first | exact superpose eq152 eq1891 | exact mod_symm (superpose eq152 eq1891) | exact superpose eq1891 eq152 | exact mod_symm (superpose eq1891 eq152)
  have eq1959 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (e (v ((v X0) ◇ (v (X1 ◇ (X0 ◇ (v X0))))))) := by first | exact superpose eq152 eq1864 | exact mod_symm (superpose eq152 eq1864) | exact superpose eq1864 eq152 | exact mod_symm (superpose eq1864 eq152)
  have eq1966 (X0 X1 : G) : (e (v ((e (v X1)) ◇ (v (v (X0 ◇ (e X1))))))) = (w (e (v X1)) (e (v X0))) := by first | exact superpose eq16 eq1932 | exact mod_symm (superpose eq16 eq1932) | exact superpose eq1932 eq16 | exact mod_symm (superpose eq1932 eq16)
  have eq1968 (X0 X1 : G) : (w (e (v X1)) (e (v X0))) = (e (v (v (X1 ◇ (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq1934 | exact mod_symm (superpose eq15 eq1934) | exact superpose eq1934 eq15 | exact mod_symm (superpose eq1934 eq15)
  have eq1977 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ (v X0))))))) := by first | exact superpose eq15 eq1959 | exact mod_symm (superpose eq15 eq1959) | exact superpose eq1959 eq15 | exact mod_symm (superpose eq1959 eq15)
  have eq1982 (X0 X1 : G) : (e (v ((v X1) ◇ (v (v (X0 ◇ (e X1))))))) = (w (e (v X1)) (e (v X0))) := by first | exact superpose eq152 eq1966 | exact mod_symm (superpose eq152 eq1966) | exact superpose eq1966 eq152 | exact mod_symm (superpose eq1966 eq152)
  have eq1989 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (w X1 (v X0)) := by first | exact superpose eq364 eq1977 | exact mod_symm (superpose eq364 eq1977) | exact superpose eq1977 eq364 | exact mod_symm (superpose eq1977 eq364)
  have eq1993 (X0 X1 : G) : (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) = (w (e (v X1)) (e (v X0))) := by first | exact superpose eq15 eq1982 | exact mod_symm (superpose eq15 eq1982) | exact superpose eq1982 eq15 | exact mod_symm (superpose eq1982 eq15)
  have eq2000 (X0 X1 : G) : (w (v X0) (v X1)) = (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq1989 eq1993 | exact mod_symm (superpose eq1989 eq1993) | exact superpose eq1993 eq1989 | exact mod_symm (superpose eq1993 eq1989)
  have eq2005 (X0 X1 : G) : (w (v X0) (v X1)) = (v (w (e X1) X0)) := by first | exact superpose eq1824 eq2000 | exact mod_symm (superpose eq1824 eq2000) | exact superpose eq2000 eq1824 | exact mod_symm (superpose eq2000 eq1824)
  have eq2007 (X0 X1 : G) : (v (w X0 X1)) = (v (w (e X1) X0)) := by first | exact superpose eq127 eq2005 | exact mod_symm (superpose eq127 eq2005) | exact superpose eq2005 eq127 | exact mod_symm (superpose eq2005 eq127)
  have eq2010 (X0 X1 X2 : G) : (v (w (e (X0 ◇ X1)) X2)) = (v (w X2 ((e X0) ◇ X1))) := by first | exact superpose eq31 eq2007 | exact mod_symm (superpose eq31 eq2007) | exact superpose eq2007 eq31 | exact mod_symm (superpose eq2007 eq31)
  have eq2011 (X0 X1 : G) : (v (w (e X0) X1)) = (v (w X1 (e X0))) := by first | exact superpose eq16 eq2007 | exact mod_symm (superpose eq16 eq2007) | exact superpose eq2007 eq16 | exact mod_symm (superpose eq2007 eq16)
  have eq2026 (X0 X1 X2 : G) : ((v (w X0 X1)) ◇ (v X2)) = (v ((w (e X1) X0) ◇ X2)) := by first | exact superpose eq2007 eq15 | exact mod_symm (superpose eq2007 eq15) | exact superpose eq15 eq2007 | exact mod_symm (superpose eq15 eq2007)
  have eq2027 (X0 X1 X2 : G) : ((v X2) ◇ (v (w X0 X1))) = (v (X2 ◇ (w (e X1) X0))) := by first | exact superpose eq2007 eq15 | exact mod_symm (superpose eq2007 eq15) | exact superpose eq15 eq2007 | exact mod_symm (superpose eq15 eq2007)
  have eq2053 (X0 X1 X2 : G) : (v (X2 ◇ (w X0 X1))) = (v (X2 ◇ (w (e X1) X0))) := by first | exact superpose eq15 eq2027 | exact mod_symm (superpose eq15 eq2027) | exact superpose eq2027 eq15 | exact mod_symm (superpose eq2027 eq15)
  have eq2054 (X0 X1 X2 : G) : (v ((w X0 X1) ◇ X2)) = (v ((w (e X1) X0) ◇ X2)) := by first | exact superpose eq15 eq2026 | exact mod_symm (superpose eq15 eq2026) | exact superpose eq2026 eq15 | exact mod_symm (superpose eq2026 eq15)
  have eq2064 (X0 X1 : G) : (v (w X1 X0)) = (v (w X1 (e X0))) := by first | exact superpose eq2007 eq2011 | exact mod_symm (superpose eq2007 eq2011) | exact superpose eq2011 eq2007 | exact mod_symm (superpose eq2011 eq2007)
  have eq2065 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ X1))) = (v (w X2 (X0 ◇ X1))) := by first | exact superpose eq2007 eq2010 | exact mod_symm (superpose eq2007 eq2010) | exact superpose eq2010 eq2007 | exact mod_symm (superpose eq2010 eq2007)
  have eq2104 (X0 X1 X2 : G) : ((v (w X0 X1)) ◇ ((v (w X0 X1)) ◇ (X2 ◇ (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))))) = X2 := by first | exact superpose eq110 eq79 | exact mod_symm (superpose eq110 eq79) | exact superpose eq79 eq110 | exact mod_symm (superpose eq79 eq110)
  have eq2133 (X0 X1 X2 : G) : ((X2 ◇ (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) ◇ (v ((w X0 X1) ◇ (w X0 X1)))) = X2 := by first | exact superpose eq609 eq2104 | exact mod_symm (superpose eq609 eq2104) | exact superpose eq2104 eq609 | exact mod_symm (superpose eq2104 eq609)
  have eq2152 (X0 X1 X2 : G) : ((X2 ◇ (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) ◇ (w X0 X1)) = X2 := by first | exact superpose eq106 eq2133 | exact mod_symm (superpose eq106 eq2133) | exact superpose eq2133 eq106 | exact mod_symm (superpose eq2133 eq106)
  have eq2162 (X0 X1 X2 : G) : ((X2 ◇ (w X1 X0)) ◇ (w X0 X1)) = X2 := by first | exact superpose eq364 eq2152 | exact mod_symm (superpose eq364 eq2152) | exact superpose eq2152 eq364 | exact mod_symm (superpose eq2152 eq364)
  have eq2194 (X0 X1 : G) : (v (w (e X0) X1)) = (v (w (e X1) X0)) := by first | exact superpose eq2064 eq2007 | exact mod_symm (superpose eq2064 eq2007) | exact superpose eq2007 eq2064 | exact mod_symm (superpose eq2007 eq2064)
  have eq2195 (X0 X1 X2 : G) : ((v (w X0 X1)) ◇ (v X2)) = (v ((w X0 (e X1)) ◇ X2)) := by first | exact superpose eq2064 eq15 | exact mod_symm (superpose eq2064 eq15) | exact superpose eq15 eq2064 | exact mod_symm (superpose eq15 eq2064)
  have eq2223 (X0 X1 X2 : G) : (v ((w X0 X1) ◇ X2)) = (v ((w X0 (e X1)) ◇ X2)) := by first | exact superpose eq15 eq2195 | exact mod_symm (superpose eq15 eq2195) | exact superpose eq2195 eq15 | exact mod_symm (superpose eq2195 eq15)
  have eq2224 (X0 X1 : G) : (v (w X0 X1)) = (v (w (e X0) X1)) := by first | exact superpose eq2007 eq2194 | exact mod_symm (superpose eq2007 eq2194) | exact superpose eq2194 eq2007 | exact mod_symm (superpose eq2194 eq2007)
  have eq2288 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v (v ((e ((e X0) ◇ (v (X1 ◇ (e X0))))) ◇ (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq119 eq117 | exact mod_symm (superpose eq119 eq117) | exact superpose eq117 eq119 | exact mod_symm (superpose eq117 eq119)
  have eq2291 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e (v (X0 ◇ X0))) ◇ (X1 ◇ (e (v X0))))))) := by first | exact superpose eq39 eq117 | exact mod_symm (superpose eq39 eq117) | exact superpose eq117 eq39 | exact mod_symm (superpose eq117 eq39)
  have eq2295 (X0 X1 : G) : (w (e (v X1)) (X0 ◇ (e (v X1)))) = (e (v (v ((e X1) ◇ X0)))) := by first | exact superpose eq78 eq117 | exact mod_symm (superpose eq78 eq117) | exact superpose eq117 eq78 | exact mod_symm (superpose eq117 eq78)
  have eq2297 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (v ((e X1) ◇ (e (X0 ◇ (v X1))))))) := by first | exact superpose eq14 eq117 | exact mod_symm (superpose eq14 eq117) | exact superpose eq117 eq14 | exact mod_symm (superpose eq117 eq14)
  have eq2298 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v (v ((e X1) ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq34 eq117 | exact mod_symm (superpose eq34 eq117) | exact superpose eq117 eq34 | exact mod_symm (superpose eq117 eq34)
  have eq2334 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (w (e (v (e X1))) (e (v X0))) := by first | exact superpose eq1968 eq2298 | exact mod_symm (superpose eq1968 eq2298) | exact superpose eq2298 eq1968 | exact mod_symm (superpose eq2298 eq1968)
  have eq2335 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (v (e (X1 ◇ (X0 ◇ (v X1))))))) := by first | exact superpose eq14 eq2297 | exact mod_symm (superpose eq14 eq2297) | exact superpose eq2297 eq14 | exact mod_symm (superpose eq2297 eq14)
  have eq2337 (X0 X1 : G) : (e (v (v ((e X1) ◇ X0)))) = (e (v ((v X1) ◇ (v X0)))) := by first | exact superpose eq1813 eq2295 | exact mod_symm (superpose eq1813 eq2295) | exact superpose eq2295 eq1813 | exact mod_symm (superpose eq2295 eq1813)
  have eq2341 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e (v X0)) ◇ (X1 ◇ (e (v (X0 ◇ X0)))))))) := by first | exact superpose eq85 eq2291 | exact mod_symm (superpose eq85 eq2291) | exact superpose eq2291 eq85 | exact mod_symm (superpose eq2291 eq85)
  have eq2344 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w (e (e X0)) (e X1)) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq1923 eq2288 | exact mod_symm (superpose eq1923 eq2288) | exact superpose eq2288 eq1923 | exact mod_symm (superpose eq2288 eq1923)
  have eq2374 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (w (v X0) (v (e X1))) := by first | exact superpose eq1989 eq2334 | exact mod_symm (superpose eq1989 eq2334) | exact superpose eq2334 eq1989 | exact mod_symm (superpose eq2334 eq1989)
  have eq2375 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (e (v (X1 ◇ (X0 ◇ (v X1))))))) := by first | exact superpose eq17 eq2335 | exact mod_symm (superpose eq17 eq2335) | exact superpose eq2335 eq17 | exact mod_symm (superpose eq2335 eq17)
  have eq2377 (X0 X1 : G) : (e (v (v (X1 ◇ X0)))) = (e (v (v ((e X1) ◇ X0)))) := by first | exact superpose eq15 eq2337 | exact mod_symm (superpose eq15 eq2337) | exact superpose eq2337 eq15 | exact mod_symm (superpose eq2337 eq15)
  have eq2381 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e (v X0)) ◇ (X1 ◇ (e X0)))))) := by first | exact superpose eq29 eq2341 | exact mod_symm (superpose eq29 eq2341) | exact superpose eq2341 eq29 | exact mod_symm (superpose eq2341 eq29)
  have eq2384 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w (e (e X0)) X1) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq2223 eq2344 | exact mod_symm (superpose eq2223 eq2344) | exact superpose eq2344 eq2223 | exact mod_symm (superpose eq2344 eq2223)
  have eq2399 (X0 X1 : G) : (v (w X0 (e X1))) = (w (e (v X1)) (v X0)) := by first | exact superpose eq127 eq2374 | exact mod_symm (superpose eq127 eq2374) | exact superpose eq2374 eq127 | exact mod_symm (superpose eq2374 eq127)
  have eq2400 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (e (v (v (X1 ◇ (X0 ◇ (v X1))))))) := by first | exact superpose eq17 eq2375 | exact mod_symm (superpose eq17 eq2375) | exact superpose eq2375 eq17 | exact mod_symm (superpose eq2375 eq17)
  have eq2404 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((v X0) ◇ (X1 ◇ (e X0)))))) := by first | exact superpose eq2377 eq2381 | exact mod_symm (superpose eq2377 eq2381) | exact superpose eq2381 eq2377 | exact mod_symm (superpose eq2381 eq2377)
  have eq2406 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w X1 (e X0)) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq2054 eq2384 | exact mod_symm (superpose eq2054 eq2384) | exact superpose eq2384 eq2054 | exact mod_symm (superpose eq2384 eq2054)
  have eq2416 (X0 X1 : G) : (v (w X0 X1)) = (w (e (v X1)) (v X0)) := by first | exact superpose eq2064 eq2399 | exact mod_symm (superpose eq2064 eq2399) | exact superpose eq2399 eq2064 | exact mod_symm (superpose eq2399 eq2064)
  have eq2417 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq16 eq2400 | exact mod_symm (superpose eq16 eq2400) | exact superpose eq2400 eq16 | exact mod_symm (superpose eq2400 eq16)
  have eq2418 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e X0) ◇ (X1 ◇ (v X0)))))) := by first | exact superpose eq85 eq2404 | exact mod_symm (superpose eq85 eq2404) | exact superpose eq2404 eq85 | exact mod_symm (superpose eq2404 eq85)
  have eq2420 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w X1 X0) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq2223 eq2406 | exact mod_symm (superpose eq2223 eq2406) | exact superpose eq2406 eq2223 | exact mod_symm (superpose eq2406 eq2223)
  have eq2429 (X0 X1 : G) : (w X0 (v X1)) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq1989 eq2417 | exact mod_symm (superpose eq1989 eq2417) | exact superpose eq2417 eq1989 | exact mod_symm (superpose eq2417 eq1989)
  have eq2430 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v (X0 ◇ (X1 ◇ (v X0)))))) := by first | exact superpose eq2377 eq2418 | exact mod_symm (superpose eq2377 eq2418) | exact superpose eq2418 eq2377 | exact mod_symm (superpose eq2418 eq2377)
  have eq2431 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w X1 X0) ◇ (v (X2 ◇ (w X1 X0)))))) := by first | exact superpose eq2053 eq2420 | exact mod_symm (superpose eq2053 eq2420) | exact superpose eq2420 eq2053 | exact mod_symm (superpose eq2420 eq2053)
  have eq2438 (X0 X1 : G) : (w (e (v X0)) X1) = (w X1 (v X0)) := by first | exact superpose eq2429 eq2430 | exact mod_symm (superpose eq2429 eq2430) | exact superpose eq2430 eq2429 | exact mod_symm (superpose eq2430 eq2429)
  have eq2439 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (w (e (w X1 X0)) (e X2)) := by first | exact superpose eq1825 eq2431 | exact mod_symm (superpose eq1825 eq2431) | exact superpose eq2431 eq1825 | exact mod_symm (superpose eq2431 eq1825)
  have eq2441 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (w (w X1 X0) (e X2)) := by first | exact superpose eq103 eq2439 | exact mod_symm (superpose eq103 eq2439) | exact superpose eq2439 eq103 | exact mod_symm (superpose eq2439 eq103)
  have eq2443 (X0 X1 : G) : (w X1 (e X0)) = (w (e (e X0)) X1) := by first | exact superpose eq19 eq2438 | exact mod_symm (superpose eq19 eq2438) | exact superpose eq2438 eq19 | exact mod_symm (superpose eq2438 eq19)
  have eq2453 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (w X2 (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq119 eq2438 | exact mod_symm (superpose eq119 eq2438) | exact superpose eq2438 eq119 | exact mod_symm (superpose eq2438 eq119)
  have eq2480 (X0 X1 X2 : G) : (w X2 (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w X1 X0) (e X2)) := by first | exact superpose eq2441 eq2453 | exact mod_symm (superpose eq2441 eq2453) | exact superpose eq2453 eq2441 | exact mod_symm (superpose eq2453 eq2441)
  have eq2485 (X0 X1 : G) : (w (e X0) X1) = (w X1 (e X0)) := by first | exact superpose eq16 eq2443 | exact mod_symm (superpose eq16 eq2443) | exact superpose eq2443 eq16 | exact mod_symm (superpose eq2443 eq16)
  have eq2515 (X0 X1 : G) : (w (v (e (X0 ◇ X0))) X1) = (e (v (v ((v (e (X0 ◇ X0))) ◇ (X1 ◇ ((v (e (X0 ◇ X0))) ◇ (e X0))))))) := by first | exact superpose eq36 eq118 | exact mod_symm (superpose eq36 eq118) | exact superpose eq118 eq36 | exact mod_symm (superpose eq118 eq36)
  have eq2554 (X0 X1 : G) : (w X1 (e X0)) = (w (v (e (X0 ◇ X0))) X1) := by first | exact superpose eq364 eq2515 | exact mod_symm (superpose eq364 eq2515) | exact superpose eq2515 eq364 | exact mod_symm (superpose eq2515 eq364)
  have eq2572 (X0 X1 : G) : (w X1 (e X0)) = (w (e (v (X0 ◇ X0))) X1) := by first | exact superpose eq17 eq2554 | exact mod_symm (superpose eq17 eq2554) | exact superpose eq2554 eq17 | exact mod_symm (superpose eq2554 eq17)
  have eq2586 (X0 X1 : G) : (w X1 (e X0)) = (w X1 (v (X0 ◇ X0))) := by first | exact superpose eq2438 eq2572 | exact mod_symm (superpose eq2438 eq2572) | exact superpose eq2572 eq2438 | exact mod_symm (superpose eq2572 eq2438)
  have eq2638 (X0 X1 : G) : (w X0 (e (v X1))) = (w X0 (v X1)) := by first | exact superpose eq2485 eq2438 | exact mod_symm (superpose eq2485 eq2438) | exact superpose eq2438 eq2485 | exact mod_symm (superpose eq2438 eq2485)
  have eq2825 (X0 X1 X2 : G) : (v (w (e (X0 ◇ X1)) X2)) = (v (w (X0 ◇ (e X1)) X2)) := by first | exact superpose eq30 eq2224 | exact mod_symm (superpose eq30 eq2224) | exact superpose eq2224 eq30 | exact mod_symm (superpose eq2224 eq30)
  have eq2827 (X0 X1 X2 : G) : (v (w (e (X0 ◇ X1)) X2)) = (v (w ((e X0) ◇ X1) X2)) := by first | exact superpose eq31 eq2224 | exact mod_symm (superpose eq31 eq2224) | exact superpose eq2224 eq31 | exact mod_symm (superpose eq2224 eq31)
  have eq2901 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ X1))) = (v (w ((e X0) ◇ X1) X2)) := by first | exact superpose eq2007 eq2827 | exact mod_symm (superpose eq2007 eq2827) | exact superpose eq2827 eq2007 | exact mod_symm (superpose eq2827 eq2007)
  have eq2903 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ X1))) = (v (w (X0 ◇ (e X1)) X2)) := by first | exact superpose eq2007 eq2825 | exact mod_symm (superpose eq2007 eq2825) | exact superpose eq2825 eq2007 | exact mod_symm (superpose eq2825 eq2007)
  have eq2982 (X0 X1 X2 : G) : (w X2 X1) = (((w X1 X2) ◇ X0) ◇ X0) := by first | exact superpose eq2162 eq233 | exact mod_symm (superpose eq2162 eq233) | exact superpose eq233 eq2162 | exact mod_symm (superpose eq233 eq2162)
  have eq2983 (X1 X2 : G) : (w X1 X2) = (w X2 X1) := by first | exact superpose eq78 eq2982 | exact mod_symm (superpose eq78 eq2982) | exact superpose eq2982 eq78 | exact mod_symm (superpose eq2982 eq78)
  have eq3063 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w (e X0) X1) (v X2)) := by first | exact superpose eq119 eq2416 | exact mod_symm (superpose eq119 eq2416) | exact superpose eq2416 eq119 | exact mod_symm (superpose eq2416 eq119)
  have eq3072 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w (e (v X1)) (e X0)) := by first | exact superpose eq19 eq2416 | exact mod_symm (superpose eq19 eq2416) | exact superpose eq2416 eq19 | exact mod_symm (superpose eq2416 eq19)
  have eq3111 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w X0 (v X1)) := by first | exact superpose eq1989 eq3072 | exact mod_symm (superpose eq1989 eq3072) | exact superpose eq3072 eq1989 | exact mod_symm (superpose eq3072 eq1989)
  have eq3118 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w X1 X0) (e (v X2))) := by first | exact superpose eq2441 eq3063 | exact mod_symm (superpose eq2441 eq3063) | exact superpose eq3063 eq2441 | exact mod_symm (superpose eq3063 eq2441)
  have eq3131 (X0 X1 : G) : (w X0 (v X1)) = (v (w X1 ((e X0) ◇ X0))) := by first | exact superpose eq2903 eq3111 | exact mod_symm (superpose eq2903 eq3111) | exact superpose eq3111 eq2903 | exact mod_symm (superpose eq3111 eq2903)
  have eq3135 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w X1 X0) (v X2)) := by first | exact superpose eq2638 eq3118 | exact mod_symm (superpose eq2638 eq3118) | exact superpose eq3118 eq2638 | exact mod_symm (superpose eq3118 eq2638)
  have eq3144 (X0 X1 : G) : (w X0 (v X1)) = (v (w X1 (X0 ◇ X0))) := by first | exact superpose eq2065 eq3131 | exact mod_symm (superpose eq2065 eq3131) | exact superpose eq3131 eq2065 | exact mod_symm (superpose eq3131 eq2065)
  have eq3146 (X0 X1 X2 : G) : (w (w X1 X0) (v X2)) = (v (w X2 (X0 ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq2065 eq3135 | exact mod_symm (superpose eq2065 eq3135) | exact superpose eq3135 eq2065 | exact mod_symm (superpose eq3135 eq2065)
  have eq3326 (X0 X1 : G) : (w (v X0) (e X1)) = (v (w X0 (X1 ◇ X1))) := by first | exact superpose eq2586 eq127 | exact mod_symm (superpose eq2586 eq127) | exact superpose eq127 eq2586 | exact mod_symm (superpose eq127 eq2586)
  have eq3327 (X0 X1 : G) : (w (v X0) (e X1)) = (w X1 (v X0)) := by first | exact superpose eq3144 eq3326 | exact mod_symm (superpose eq3144 eq3326) | exact superpose eq3326 eq3144 | exact mod_symm (superpose eq3326 eq3144)
  have eq3364 (X0 X1 : G) : (w (e X0) (e X1)) = (w X1 (e X0)) := by first | exact superpose eq19 eq3327 | exact mod_symm (superpose eq19 eq3327) | exact superpose eq3327 eq19 | exact mod_symm (superpose eq3327 eq19)
  have eq3382 (X0 X1 X2 : G) : (w (v ((e X0) ◇ (v (X1 ◇ (e X0))))) (v X2)) = (w (v X2) (w (e X0) X1)) := by first | exact superpose eq119 eq3327 | exact mod_symm (superpose eq119 eq3327) | exact superpose eq3327 eq119 | exact mod_symm (superpose eq3327 eq119)
  have eq3413 (X0 X1 X2 : G) : (w (v X2) (w (e X0) X1)) = (v (w ((e X0) ◇ (v (X1 ◇ (e X0)))) X2)) := by first | exact superpose eq127 eq3382 | exact mod_symm (superpose eq127 eq3382) | exact superpose eq3382 eq127 | exact mod_symm (superpose eq3382 eq127)
  have eq3426 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ (v (X1 ◇ (e X0)))))) = (w (v X2) (w (e X0) X1)) := by first | exact superpose eq2901 eq3413 | exact mod_symm (superpose eq2901 eq3413) | exact superpose eq3413 eq2901 | exact mod_symm (superpose eq3413 eq2901)
  have eq3434 (X0 X1 X2 : G) : (w (w X1 X0) (v X2)) = (w (v X2) (w (e X0) X1)) := by first | exact superpose eq3146 eq3426 | exact mod_symm (superpose eq3146 eq3426) | exact superpose eq3426 eq3146 | exact mod_symm (superpose eq3426 eq3146)
  have eq3756 (X0 : G) : (e (e X0)) = (w X0 (e X0)) := by first | exact superpose eq3364 eq217 | exact mod_symm (superpose eq3364 eq217) | exact superpose eq217 eq3364 | exact mod_symm (superpose eq217 eq3364)
  have eq3768 (X0 : G) : (e X0) = (w X0 (e X0)) := by first | exact superpose eq16 eq3756 | exact mod_symm (superpose eq16 eq3756) | exact superpose eq3756 eq16 | exact mod_symm (superpose eq3756 eq16)
  have eq3974 (X0 X1 : G) : (w (e X0) X1) = (w (v ((e X0) ◇ (v (X1 ◇ (e X0))))) (w (e X0) X1)) := by first | exact superpose eq119 eq3768 | exact mod_symm (superpose eq119 eq3768) | exact superpose eq3768 eq119 | exact mod_symm (superpose eq3768 eq119)
  have eq3998 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq3768 eq258 | exact mod_symm (superpose eq3768 eq258) | exact superpose eq258 eq3768 | exact mod_symm (superpose eq258 eq3768)
  have eq4015 (X0 X1 : G) : (w (e X0) X1) = (w (w X1 X0) (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq3434 eq3974 | exact mod_symm (superpose eq3434 eq3974) | exact superpose eq3974 eq3434 | exact mod_symm (superpose eq3974 eq3434)
  have eq4041 (X0 X1 : G) : (w (e X0) X1) = (w (w X1 X0) (e (w X1 X0))) := by first | exact superpose eq2480 eq4015 | exact mod_symm (superpose eq2480 eq4015) | exact superpose eq4015 eq2480 | exact mod_symm (superpose eq4015 eq2480)
  have eq4064 (X0 X1 : G) : (w (e X0) X1) = (e (w X1 X0)) := by first | exact superpose eq3768 eq4041 | exact mod_symm (superpose eq3768 eq4041) | exact superpose eq4041 eq3768 | exact mod_symm (superpose eq4041 eq3768)
  have eq4085 (X0 X1 : G) : (w (e X0) X1) = (w X1 X0) := by first | exact superpose eq103 eq4064 | exact mod_symm (superpose eq103 eq4064) | exact superpose eq4064 eq103 | exact mod_symm (superpose eq4064 eq103)
  have eq4506 (X0 X1 : G) : (w X0 X1) = (w X0 (e X1)) := by first | exact superpose eq4085 eq2983 | exact mod_symm (superpose eq4085 eq2983) | exact superpose eq2983 eq4085 | exact mod_symm (superpose eq2983 eq4085)
  have eq4785 : (w x y) ≠ (w y x) := by first | exact superpose eq4506 eq3998 | exact mod_symm (superpose eq4506 eq3998) | exact superpose eq3998 eq4506 | exact mod_symm (superpose eq3998 eq4506)
  subsumption eq4785 eq2983


/-- Equation 3345 `x ◇ y = y ◇ (x ◇ (y ◇ x))` is term-definable from equation 546 over finite magmas, via the term
`x □ y := u^[3N+1] (((x ◇ x) ◇ (y ◇ x)) ◇ y)` where `u a = a ◇ a`. -/
private theorem aux546_3345 [Magma G] (h : Equation546 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, v (e a) ◇ v (e a) = e a) (hvue : ∀ a : G, v (e a ◇ e a) = e a)
    (hw : ∀ a b : G, w a b = (e (v (v (((a ◇ a) ◇ (b ◇ a)) ◇ b)))))
    (x y : G) :
    (w x y) =
      (w y (w x (w y x))) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ (v (e X0))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ (e X0))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (v (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1)))) := mod_symm (hw ..)
  have eq21 : (w x y) ≠ (w y (w x (w y x))) := mod_symm nh
  have eq26 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq27 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq28 (X0 : G) : (e X0) = (v (e (X0 ◇ X0))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq29 (X0 : G) : (e X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq17 eq28 | exact mod_symm (superpose eq17 eq28) | exact superpose eq28 eq17 | exact mod_symm (superpose eq28 eq17)
  have eq30 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq27 | exact mod_symm (superpose eq14 eq27) | exact superpose eq27 eq14 | exact mod_symm (superpose eq27 eq14)
  have eq31 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq32 (X0 X1 : G) : (v ((e X0) ◇ X1)) = ((e (v X0)) ◇ (v X1)) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq33 (X0 X1 : G) : (v (((e X0) ◇ (e X0)) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq34 (X0 X1 : G) : (v (X1 ◇ (e X0))) = ((v X1) ◇ (e (v X0))) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq35 (X0 X1 : G) : (v (X1 ◇ ((e X0) ◇ (e X0)))) = ((v X1) ◇ (e X0)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq36 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X1 ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35) | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14)
  have eq37 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v ((e (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq33 | exact mod_symm (superpose eq14 eq33) | exact superpose eq33 eq14 | exact mod_symm (superpose eq33 eq14)
  have eq39 (X0 : G) : (e (v X0)) = (e (v (v (X0 ◇ X0)))) := by first | exact superpose eq15 eq29 | exact mod_symm (superpose eq15 eq29) | exact superpose eq29 eq15 | exact mod_symm (superpose eq29 eq15)
  have eq40 (X0 X1 : G) : ((e X1) ◇ (e X0)) = (e (X1 ◇ (v (X0 ◇ X0)))) := by first | exact superpose eq29 eq14 | exact mod_symm (superpose eq29 eq14) | exact superpose eq14 eq29 | exact mod_symm (superpose eq14 eq29)
  have eq41 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((v (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq29 eq14 | exact mod_symm (superpose eq29 eq14) | exact superpose eq14 eq29 | exact mod_symm (superpose eq14 eq29)
  have eq46 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((v (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq41 | exact mod_symm (superpose eq14 eq41) | exact superpose eq41 eq14 | exact mod_symm (superpose eq41 eq14)
  have eq47 (X0 X1 : G) : (e (X1 ◇ X0)) = (e (X1 ◇ (v (X0 ◇ X0)))) := by first | exact superpose eq14 eq40 | exact mod_symm (superpose eq14 eq40) | exact superpose eq40 eq14 | exact mod_symm (superpose eq40 eq14)
  have eq64 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq30 eq17 | exact mod_symm (superpose eq30 eq17) | exact superpose eq17 eq30 | exact mod_symm (superpose eq17 eq30)
  have eq67 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq17 eq64 | exact mod_symm (superpose eq17 eq64) | exact superpose eq64 eq17 | exact mod_symm (superpose eq64 eq17)
  have eq73 (X0 X1 X2 : G) : ((e X1) ◇ ((e X0) ◇ (X2 ◇ (e (X0 ◇ X1))))) = X2 := by first | exact superpose eq14 eq13 | exact mod_symm (superpose eq14 eq13) | exact superpose eq13 eq14 | exact mod_symm (superpose eq13 eq14)
  have eq75 (X0 X1 : G) : ((v (e X0)) ◇ ((v (e X0)) ◇ (X1 ◇ (e X0)))) = X1 := by first | exact superpose eq18 eq13 | exact mod_symm (superpose eq18 eq13) | exact superpose eq13 eq18 | exact mod_symm (superpose eq13 eq18)
  have eq76 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0))) = X3 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq77 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X2 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq78 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq79 (X0 X1 : G) : ((e (v X0)) ◇ ((e (v X0)) ◇ (X1 ◇ (e X0)))) = X1 := by first | exact superpose eq17 eq75 | exact mod_symm (superpose eq17 eq75) | exact superpose eq75 eq17 | exact mod_symm (superpose eq75 eq17)
  have eq80 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X1 := by first | exact superpose eq13 eq78 | exact mod_symm (superpose eq13 eq78) | exact superpose eq78 eq13 | exact mod_symm (superpose eq78 eq13)
  have eq83 (X0 : G) : (v (e X0)) = ((e X0) ◇ (v (e X0))) := by first | exact superpose eq18 eq78 | exact mod_symm (superpose eq18 eq78) | exact superpose eq78 eq18 | exact mod_symm (superpose eq78 eq18)
  have eq85 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X1 ◇ (X2 ◇ X0)) := by first | exact superpose eq78 eq13 | exact mod_symm (superpose eq78 eq13) | exact superpose eq13 eq78 | exact mod_symm (superpose eq13 eq78)
  have eq89 (X0 : G) : (e (v X0)) = ((e X0) ◇ (e (v X0))) := by first | exact superpose eq17 eq83 | exact mod_symm (superpose eq17 eq83) | exact superpose eq83 eq17 | exact mod_symm (superpose eq83 eq17)
  have eq92 (X0 : G) : (e (v X0)) = (e (X0 ◇ (v X0))) := by first | exact superpose eq14 eq89 | exact mod_symm (superpose eq14 eq89) | exact superpose eq89 eq14 | exact mod_symm (superpose eq89 eq14)
  have eq96 (X0 X1 X2 : G) : (w (X1 ◇ (X0 ◇ (X1 ◇ X2))) X2) = (e (v (v ((((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X0) ◇ X2)))) := by first | exact superpose eq13 eq20 | exact mod_symm (superpose eq13 eq20) | exact superpose eq20 eq13 | exact mod_symm (superpose eq20 eq13)
  have eq98 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (v ((((e X1) ◇ (e X1)) ◇ (e (X0 ◇ X1))) ◇ (e X0))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq99 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v ((((v X1) ◇ (v X1)) ◇ (v (X0 ◇ X1))) ◇ (v X0))))) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  have eq103 (X0 X1 : G) : (w X0 X1) = (e (w X0 X1)) := by first | exact superpose eq20 eq16 | exact mod_symm (superpose eq20 eq16) | exact superpose eq16 eq20 | exact mod_symm (superpose eq16 eq20)
  have eq104 (X0 X1 : G) : (e (v (v (v (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1))))) = (v (w X0 X1)) := by first | exact superpose eq20 eq17 | exact mod_symm (superpose eq20 eq17) | exact superpose eq17 eq20 | exact mod_symm (superpose eq17 eq20)
  have eq110 (X0 X1 : G) : (v (w X0 X1)) = (e (v (v (v ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1))))) := by first | exact superpose eq85 eq104 | exact mod_symm (superpose eq85 eq104) | exact superpose eq104 eq85 | exact mod_symm (superpose eq104 eq85)
  have eq114 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (((v (X1 ◇ X1)) ◇ (v (X0 ◇ X1))) ◇ (v X0))))) := by first | exact superpose eq15 eq99 | exact mod_symm (superpose eq15 eq99) | exact superpose eq99 eq15 | exact mod_symm (superpose eq99 eq15)
  have eq115 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (v (((e (X1 ◇ X1)) ◇ (e (X0 ◇ X1))) ◇ (e X0))))) := by first | exact superpose eq14 eq98 | exact mod_symm (superpose eq14 eq98) | exact superpose eq98 eq14 | exact mod_symm (superpose eq98 eq14)
  have eq117 (X0 X1 X2 : G) : (w (X1 ◇ (X0 ◇ (X1 ◇ X2))) X2) = (e (v (v ((((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) ◇ X0) ◇ X2)))) := by first | exact superpose eq85 eq96 | exact mod_symm (superpose eq85 eq96) | exact superpose eq96 eq85 | exact mod_symm (superpose eq96 eq85)
  have eq123 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v ((v ((X1 ◇ X1) ◇ (X0 ◇ X1))) ◇ (v X0))))) := by first | exact superpose eq15 eq114 | exact mod_symm (superpose eq15 eq114) | exact superpose eq114 eq15 | exact mod_symm (superpose eq114 eq15)
  have eq124 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (v ((e ((X1 ◇ X1) ◇ (X0 ◇ X1))) ◇ (e X0))))) := by first | exact superpose eq14 eq115 | exact mod_symm (superpose eq14 eq115) | exact superpose eq115 eq14 | exact mod_symm (superpose eq115 eq14)
  have eq126 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (v (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0))))) := by first | exact superpose eq15 eq123 | exact mod_symm (superpose eq15 eq123) | exact superpose eq123 eq15 | exact mod_symm (superpose eq123 eq15)
  have eq127 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (v (e (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0))))) := by first | exact superpose eq14 eq124 | exact mod_symm (superpose eq14 eq124) | exact superpose eq124 eq14 | exact mod_symm (superpose eq124 eq14)
  have eq129 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (v ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0))))) := by first | exact superpose eq85 eq126 | exact mod_symm (superpose eq85 eq126) | exact superpose eq126 eq85 | exact mod_symm (superpose eq126 eq85)
  have eq130 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (e (v (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0))))) := by first | exact superpose eq17 eq127 | exact mod_symm (superpose eq17 eq127) | exact superpose eq127 eq17 | exact mod_symm (superpose eq127 eq17)
  have eq132 (X0 X1 : G) : (w (v X1) (v X0)) = (v (w X1 X0)) := by first | exact superpose eq110 eq129 | exact mod_symm (superpose eq110 eq129) | exact superpose eq129 eq110 | exact mod_symm (superpose eq129 eq110)
  have eq133 (X0 X1 : G) : (w (e X1) (e X0)) = (e (e (v (v (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0))))) := by first | exact superpose eq17 eq130 | exact mod_symm (superpose eq17 eq130) | exact superpose eq130 eq17 | exact mod_symm (superpose eq130 eq17)
  have eq134 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (v (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)))) := by first | exact superpose eq16 eq133 | exact mod_symm (superpose eq16 eq133) | exact superpose eq133 eq16 | exact mod_symm (superpose eq133 eq16)
  have eq135 (X0 X1 : G) : (w X1 X0) = (w (e X1) (e X0)) := by first | exact superpose eq20 eq134 | exact mod_symm (superpose eq20 eq134) | exact superpose eq134 eq20 | exact mod_symm (superpose eq134 eq20)
  have eq143 (X0 X1 X2 : G) : (w (X0 ◇ (e X1)) X2) = (w (e (X0 ◇ X1)) (e X2)) := by first | exact superpose eq30 eq135 | exact mod_symm (superpose eq30 eq135) | exact superpose eq135 eq30 | exact mod_symm (superpose eq135 eq30)
  have eq144 (X0 X1 : G) : (w (e X0) X1) = (w (e X0) (e X1)) := by first | exact superpose eq16 eq135 | exact mod_symm (superpose eq16 eq135) | exact superpose eq135 eq16 | exact mod_symm (superpose eq135 eq16)
  have eq148 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w (e X2) (e (X0 ◇ X1))) := by first | exact superpose eq30 eq135 | exact mod_symm (superpose eq30 eq135) | exact superpose eq135 eq30 | exact mod_symm (superpose eq135 eq30)
  have eq149 (X0 X1 : G) : (w (e X1) (e X0)) = (w X1 (e X0)) := by first | exact superpose eq16 eq135 | exact mod_symm (superpose eq16 eq135) | exact superpose eq135 eq16 | exact mod_symm (superpose eq135 eq16)
  have eq151 (X0 X1 X2 : G) : (w X2 (v (v (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1)))) = (w (e X2) (w X0 X1)) := by first | exact superpose eq20 eq135 | exact mod_symm (superpose eq20 eq135) | exact superpose eq135 eq20 | exact mod_symm (superpose eq135 eq20)
  have eq152 (X0 X1 X2 : G) : (w (e X2) (w X0 X1)) = (w X2 (w X0 X1)) := by first | exact superpose eq103 eq135 | exact mod_symm (superpose eq103 eq135) | exact superpose eq135 eq103 | exact mod_symm (superpose eq135 eq103)
  have eq154 (X0 X1 X2 : G) : (w X2 (v (v (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1)))) = (w X2 (w X0 X1)) := by first | exact superpose eq152 eq151 | exact mod_symm (superpose eq152 eq151) | exact superpose eq151 eq152 | exact mod_symm (superpose eq151 eq152)
  have eq156 (X0 X1 : G) : (w X1 X0) = (w X1 (e X0)) := by first | exact superpose eq135 eq149 | exact mod_symm (superpose eq135 eq149) | exact superpose eq149 eq135 | exact mod_symm (superpose eq149 eq135)
  have eq157 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w X2 (X0 ◇ X1)) := by first | exact superpose eq135 eq148 | exact mod_symm (superpose eq135 eq148) | exact superpose eq148 eq135 | exact mod_symm (superpose eq148 eq135)
  have eq160 (X0 X1 : G) : (w X0 X1) = (w (e X0) X1) := by first | exact superpose eq135 eq144 | exact mod_symm (superpose eq135 eq144) | exact superpose eq144 eq135 | exact mod_symm (superpose eq144 eq135)
  have eq161 (X0 X1 X2 : G) : (w (X0 ◇ (e X1)) X2) = (w (X0 ◇ X1) X2) := by first | exact superpose eq135 eq143 | exact mod_symm (superpose eq135 eq143) | exact superpose eq143 eq135 | exact mod_symm (superpose eq143 eq135)
  have eq162 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w X2 (v (v ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)))) := by first | exact superpose eq85 eq154 | exact mod_symm (superpose eq85 eq154) | exact superpose eq154 eq85 | exact mod_symm (superpose eq154 eq85)
  have eq184 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq31 eq17 | exact mod_symm (superpose eq31 eq17) | exact superpose eq17 eq31 | exact mod_symm (superpose eq17 eq31)
  have eq189 (X0 X1 X2 : G) : (w (e (X0 ◇ X1)) (e X2)) = (w ((e X0) ◇ X1) X2) := by first | exact superpose eq31 eq135 | exact mod_symm (superpose eq31 eq135) | exact superpose eq135 eq31 | exact mod_symm (superpose eq135 eq31)
  have eq190 (X0 X1 X2 : G) : (w X2 (e (X0 ◇ X1))) = (w X2 ((e X0) ◇ X1)) := by first | exact superpose eq31 eq156 | exact mod_symm (superpose eq31 eq156) | exact superpose eq156 eq31 | exact mod_symm (superpose eq156 eq31)
  have eq191 (X0 X1 X2 : G) : (w X2 (X0 ◇ X1)) = (w X2 ((e X0) ◇ X1)) := by first | exact superpose eq156 eq190 | exact mod_symm (superpose eq156 eq190) | exact superpose eq190 eq156 | exact mod_symm (superpose eq190 eq156)
  have eq192 (X0 X1 X2 : G) : (w (X0 ◇ X1) X2) = (w ((e X0) ◇ X1) X2) := by first | exact superpose eq135 eq189 | exact mod_symm (superpose eq135 eq189) | exact superpose eq189 eq135 | exact mod_symm (superpose eq189 eq135)
  have eq195 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq17 eq184 | exact mod_symm (superpose eq17 eq184) | exact superpose eq184 eq17 | exact mod_symm (superpose eq184 eq17)
  have eq221 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w (e X0) (v X1)) := by first | exact superpose eq19 eq132 | exact mod_symm (superpose eq19 eq132) | exact superpose eq132 eq19 | exact mod_symm (superpose eq132 eq19)
  have eq227 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w X0 (v X1)) := by first | exact superpose eq160 eq221 | exact mod_symm (superpose eq160 eq221) | exact superpose eq221 eq160 | exact mod_symm (superpose eq221 eq160)
  have eq231 (X0 X1 : G) : (w X0 (v X1)) = (v (w ((e X0) ◇ X0) X1)) := by first | exact superpose eq161 eq227 | exact mod_symm (superpose eq161 eq227) | exact superpose eq227 eq161 | exact mod_symm (superpose eq227 eq161)
  have eq234 (X0 X1 : G) : (w X0 (v X1)) = (v (w (X0 ◇ X0) X1)) := by first | exact superpose eq192 eq231 | exact mod_symm (superpose eq192 eq231) | exact superpose eq231 eq192 | exact mod_symm (superpose eq231 eq192)
  have eq237 (X0 : G) : (e (v (v X0))) = (e (v (X0 ◇ (v X0)))) := by first | exact superpose eq15 eq92 | exact mod_symm (superpose eq15 eq92) | exact superpose eq92 eq15 | exact mod_symm (superpose eq92 eq15)
  have eq246 (X0 X1 : G) : (e (X1 ◇ (X0 ◇ (v X0)))) = (e (X1 ◇ (e (v X0)))) := by first | exact superpose eq92 eq30 | exact mod_symm (superpose eq92 eq30) | exact superpose eq30 eq92 | exact mod_symm (superpose eq30 eq92)
  have eq257 (X0 X1 : G) : (e (X1 ◇ (X0 ◇ (v X0)))) = (e (X1 ◇ (v X0))) := by first | exact superpose eq30 eq246 | exact mod_symm (superpose eq30 eq246) | exact superpose eq246 eq30 | exact mod_symm (superpose eq246 eq30)
  have eq274 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X2))) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := by first | exact superpose eq13 eq77 | exact mod_symm (superpose eq13 eq77) | exact superpose eq77 eq13 | exact mod_symm (superpose eq77 eq13)
  have eq278 (X0 X1 X2 : G) : (v X1) = ((X2 ◇ (v (X0 ◇ X1))) ◇ ((v X0) ◇ X2)) := by first | exact superpose eq15 eq77 | exact mod_symm (superpose eq15 eq77) | exact superpose eq77 eq15 | exact mod_symm (superpose eq77 eq15)
  have eq283 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X2 := by first | exact superpose eq78 eq77 | exact mod_symm (superpose eq78 eq77) | exact superpose eq77 eq78 | exact mod_symm (superpose eq77 eq78)
  have eq285 (X0 X1 X2 : G) : (((e X1) ◇ ((e X0) ◇ X2)) ◇ (e (X0 ◇ X1))) = X2 := by first | exact superpose eq14 eq77 | exact mod_symm (superpose eq14 eq77) | exact superpose eq77 eq14 | exact mod_symm (superpose eq77 eq14)
  have eq288 (X0 X1 : G) : (w (X1 ◇ X0) X1) = (e (v (v (X0 ◇ X1)))) := by first | exact superpose eq77 eq20 | exact mod_symm (superpose eq77 eq20) | exact superpose eq20 eq77 | exact mod_symm (superpose eq20 eq77)
  have eq296 (X0 X1 X2 : G) : (v X1) = (X2 ◇ ((v X0) ◇ (X2 ◇ (v (X0 ◇ X1))))) := by first | exact superpose eq85 eq278 | exact mod_symm (superpose eq85 eq278) | exact superpose eq278 eq85 | exact mod_symm (superpose eq278 eq85)
  have eq300 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = (X3 ◇ (X0 ◇ (X3 ◇ X2))) := by first | exact superpose eq85 eq274 | exact mod_symm (superpose eq85 eq274) | exact superpose eq274 eq85 | exact mod_symm (superpose eq274 eq85)
  have eq307 (X0 : G) : (e (v (v X0))) = (e (v (v (v (X0 ◇ X0))))) := by first | exact superpose eq15 eq39 | exact mod_symm (superpose eq15 eq39) | exact superpose eq39 eq15 | exact mod_symm (superpose eq39 eq15)
  have eq396 (X0 X1 X2 : G) : (v (X2 ◇ (e (v (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1))))) = ((v X2) ◇ (w X0 X1)) := by first | exact superpose eq20 eq34 | exact mod_symm (superpose eq20 eq34) | exact superpose eq34 eq20 | exact mod_symm (superpose eq34 eq20)
  have eq411 (X0 X1 X2 : G) : ((v X2) ◇ (w X0 X1)) = (v (X2 ◇ (e (v ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1))))) := by first | exact superpose eq85 eq396 | exact mod_symm (superpose eq85 eq396) | exact superpose eq396 eq85 | exact mod_symm (superpose eq396 eq85)
  have eq486 (X0 X1 : G) : ((v (e X0)) ◇ (e X1)) = (v (e (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq14 eq36 | exact mod_symm (superpose eq14 eq36) | exact superpose eq36 eq14 | exact mod_symm (superpose eq36 eq14)
  have eq496 (X0 X1 X2 : G) : (v ((e (X0 ◇ (e (X1 ◇ X1)))) ◇ X2)) = ((e ((v X0) ◇ (e X1))) ◇ (v X2)) := by first | exact superpose eq36 eq32 | exact mod_symm (superpose eq36 eq32) | exact superpose eq32 eq36 | exact mod_symm (superpose eq32 eq36)
  have eq498 (X0 X1 X2 : G) : (v (X2 ◇ (e (X0 ◇ (e (X1 ◇ X1)))))) = ((v X2) ◇ (e ((v X0) ◇ (e X1)))) := by first | exact superpose eq36 eq34 | exact mod_symm (superpose eq36 eq34) | exact superpose eq34 eq36 | exact mod_symm (superpose eq34 eq36)
  have eq506 (X0 X1 X2 : G) : (v (X2 ◇ (e (X0 ◇ (e (X1 ◇ X1)))))) = ((v X2) ◇ (e ((v X0) ◇ X1))) := by first | exact superpose eq30 eq498 | exact mod_symm (superpose eq30 eq498) | exact superpose eq498 eq30 | exact mod_symm (superpose eq498 eq30)
  have eq507 (X0 X1 X2 : G) : (v ((e (X0 ◇ (e (X1 ◇ X1)))) ◇ X2)) = ((e ((v X0) ◇ X1)) ◇ (v X2)) := by first | exact superpose eq30 eq496 | exact mod_symm (superpose eq30 eq496) | exact superpose eq496 eq30 | exact mod_symm (superpose eq496 eq30)
  have eq515 (X0 X1 : G) : ((v (e X0)) ◇ (e X1)) = (e (v (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq17 eq486 | exact mod_symm (superpose eq17 eq486) | exact superpose eq486 eq17 | exact mod_symm (superpose eq486 eq17)
  have eq524 (X0 X1 X2 : G) : ((v X2) ◇ (e ((v X0) ◇ X1))) = (v (X2 ◇ (e (X0 ◇ (X1 ◇ X1))))) := by first | exact superpose eq30 eq506 | exact mod_symm (superpose eq30 eq506) | exact superpose eq506 eq30 | exact mod_symm (superpose eq506 eq30)
  have eq525 (X0 X1 X2 : G) : ((e ((v X0) ◇ X1)) ◇ (v X2)) = (v ((e (X0 ◇ (X1 ◇ X1))) ◇ X2)) := by first | exact superpose eq30 eq507 | exact mod_symm (superpose eq30 eq507) | exact superpose eq507 eq30 | exact mod_symm (superpose eq507 eq30)
  have eq533 (X0 X1 : G) : ((e (v X0)) ◇ (e X1)) = (e (v (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq17 eq515 | exact mod_symm (superpose eq17 eq515) | exact superpose eq515 eq17 | exact mod_symm (superpose eq515 eq17)
  have eq543 (X0 X1 : G) : (e ((v X0) ◇ X1)) = (e (v (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq14 eq533 | exact mod_symm (superpose eq14 eq533) | exact superpose eq533 eq14 | exact mod_symm (superpose eq533 eq14)
  have eq583 (X0 X1 : G) : ((e X0) ◇ (v (e X1))) = (v (e ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq14 eq37 | exact mod_symm (superpose eq14 eq37) | exact superpose eq37 eq14 | exact mod_symm (superpose eq37 eq14)
  have eq602 (X0 X1 X2 : G) : (v (w ((e (X0 ◇ X0)) ◇ X1) X2)) = (w ((e X0) ◇ (v X1)) (v X2)) := by first | exact superpose eq37 eq132 | exact mod_symm (superpose eq37 eq132) | exact superpose eq132 eq37 | exact mod_symm (superpose eq132 eq37)
  have eq603 (X0 X1 X2 : G) : (v (w ((e (X0 ◇ X0)) ◇ X1) X2)) = (w (X0 ◇ (v X1)) (v X2)) := by first | exact superpose eq192 eq602 | exact mod_symm (superpose eq192 eq602) | exact superpose eq602 eq192 | exact mod_symm (superpose eq602 eq192)
  have eq617 (X0 X1 : G) : ((e X0) ◇ (v (e X1))) = (e (v ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq17 eq583 | exact mod_symm (superpose eq17 eq583) | exact superpose eq583 eq17 | exact mod_symm (superpose eq583 eq17)
  have eq622 (X0 X1 X2 : G) : (w (X0 ◇ (v X1)) (v X2)) = (v (w ((X0 ◇ X0) ◇ X1) X2)) := by first | exact superpose eq192 eq603 | exact mod_symm (superpose eq192 eq603) | exact superpose eq603 eq192 | exact mod_symm (superpose eq603 eq192)
  have eq635 (X0 X1 : G) : ((e X0) ◇ (e (v X1))) = (e (v ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq17 eq617 | exact mod_symm (superpose eq17 eq617) | exact superpose eq617 eq17 | exact mod_symm (superpose eq617 eq17)
  have eq646 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (e (v ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq14 eq635 | exact mod_symm (superpose eq14 eq635) | exact superpose eq635 eq14 | exact mod_symm (superpose eq635 eq14)
  have eq674 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq78 eq85 | exact mod_symm (superpose eq78 eq85) | exact superpose eq85 eq78 | exact mod_symm (superpose eq85 eq78)
  have eq678 (X0 X1 X2 : G) : (X2 ◇ (v (X0 ◇ X1))) = ((v X1) ◇ ((v X0) ◇ X2)) := by first | exact superpose eq15 eq85 | exact mod_symm (superpose eq15 eq85) | exact superpose eq85 eq15 | exact mod_symm (superpose eq85 eq15)
  have eq711 (X0 X1 : G) : (e (X1 ◇ X0)) = (e (v (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by first | exact superpose eq85 eq29 | exact mod_symm (superpose eq85 eq29) | exact superpose eq29 eq85 | exact mod_symm (superpose eq29 eq85)
  have eq714 (X0 X1 : G) : (e (v (X1 ◇ X0))) = (e (v (v (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := by first | exact superpose eq85 eq39 | exact mod_symm (superpose eq85 eq39) | exact superpose eq39 eq85 | exact mod_symm (superpose eq39 eq85)
  have eq868 (X0 X1 X2 : G) : (v X0) = ((e X1) ◇ (v ((e X2) ◇ (X0 ◇ (e (X2 ◇ (X1 ◇ X1))))))) := by first | exact superpose eq73 eq37 | exact mod_symm (superpose eq73 eq37) | exact superpose eq37 eq73 | exact mod_symm (superpose eq37 eq73)
  have eq1128 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1)))) := by first | exact superpose eq13 eq283 | exact mod_symm (superpose eq13 eq283) | exact superpose eq283 eq13 | exact mod_symm (superpose eq283 eq13)
  have eq1129 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (X3 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) := by first | exact superpose eq80 eq283 | exact mod_symm (superpose eq80 eq283) | exact superpose eq283 eq80 | exact mod_symm (superpose eq283 eq80)
  have eq1212 (X0 X1 X2 : G) : ((w X0 X1) ◇ ((w X0 X1) ◇ (X2 ◇ (e (v (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1)))))) = X2 := by first | exact superpose eq20 eq79 | exact mod_symm (superpose eq20 eq79) | exact superpose eq79 eq20 | exact mod_symm (superpose eq79 eq20)
  have eq1281 (X0 X1 X2 : G) : ((w X0 X1) ◇ ((w X0 X1) ◇ (X2 ◇ (e (v ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)))))) = X2 := by first | exact superpose eq85 eq1212 | exact mod_symm (superpose eq85 eq1212) | exact superpose eq1212 eq85 | exact mod_symm (superpose eq1212 eq85)
  have eq1393 (X0 X1 : G) : (e (X1 ◇ (v (X0 ◇ (v X0))))) = (e (X1 ◇ (e (v (v X0))))) := by first | exact superpose eq237 eq30 | exact mod_symm (superpose eq237 eq30) | exact superpose eq30 eq237 | exact mod_symm (superpose eq30 eq237)
  have eq1394 (X0 X1 : G) : (e ((v (X0 ◇ (v X0))) ◇ X1)) = (e ((e (v (v X0))) ◇ X1)) := by first | exact superpose eq237 eq31 | exact mod_symm (superpose eq237 eq31) | exact superpose eq31 eq237 | exact mod_symm (superpose eq31 eq237)
  have eq1401 (X0 X1 : G) : (w X1 (v (X0 ◇ (v X0)))) = (w X1 (e (v (v X0)))) := by first | exact superpose eq237 eq156 | exact mod_symm (superpose eq237 eq156) | exact superpose eq156 eq237 | exact mod_symm (superpose eq156 eq237)
  have eq1404 (X0 X1 : G) : (w X1 (v (X0 ◇ (v X0)))) = (w X1 (v (v X0))) := by first | exact superpose eq156 eq1401 | exact mod_symm (superpose eq156 eq1401) | exact superpose eq1401 eq156 | exact mod_symm (superpose eq1401 eq156)
  have eq1411 (X0 X1 : G) : (e ((v (X0 ◇ (v X0))) ◇ X1)) = (e ((v (v X0)) ◇ X1)) := by first | exact superpose eq31 eq1394 | exact mod_symm (superpose eq31 eq1394) | exact superpose eq1394 eq31 | exact mod_symm (superpose eq1394 eq31)
  have eq1412 (X0 X1 : G) : (e (X1 ◇ (v (X0 ◇ (v X0))))) = (e (X1 ◇ (v (v X0)))) := by first | exact superpose eq30 eq1393 | exact mod_symm (superpose eq30 eq1393) | exact superpose eq1393 eq30 | exact mod_symm (superpose eq1393 eq30)
  have eq1460 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X4 ◇ X0)) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ (X5 ◇ X4))) = X5 := by first | exact superpose eq76 eq76 | exact mod_symm (superpose eq76 eq76) | exact superpose eq76 eq76 | exact mod_symm (superpose eq76 eq76)
  have eq3279 (X0 X1 : G) : (w (X1 ◇ (X0 ◇ (X1 ◇ X0))) X0) = (e (v (v ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))))) := by first | exact superpose eq78 eq117 | exact mod_symm (superpose eq78 eq117) | exact superpose eq117 eq78 | exact mod_symm (superpose eq117 eq78)
  have eq3320 (X0 X1 : G) : (w (X1 ◇ (X0 ◇ (X1 ◇ X0))) X0) = (e (v (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by first | exact superpose eq714 eq3279 | exact mod_symm (superpose eq714 eq3279) | exact superpose eq3279 eq714 | exact mod_symm (superpose eq3279 eq714)
  have eq3537 (X0 X1 X2 : G) : (e (X2 ◇ (X1 ◇ X0))) = (e (X0 ◇ (X1 ◇ (v (X2 ◇ X2))))) := by first | exact superpose eq85 eq46 | exact mod_symm (superpose eq85 eq46) | exact superpose eq46 eq85 | exact mod_symm (superpose eq46 eq85)
  have eq3567 (X0 X1 X2 : G) : (w (e (X0 ◇ X1)) X2) = (w ((v (X0 ◇ X0)) ◇ X1) X2) := by first | exact superpose eq46 eq160 | exact mod_symm (superpose eq46 eq160) | exact superpose eq160 eq46 | exact mod_symm (superpose eq160 eq46)
  have eq3569 (X0 X1 X2 : G) : (w (X0 ◇ X1) X2) = (w ((v (X0 ◇ X0)) ◇ X1) X2) := by first | exact superpose eq160 eq3567 | exact mod_symm (superpose eq160 eq3567) | exact superpose eq3567 eq160 | exact mod_symm (superpose eq3567 eq160)
  have eq3657 (X0 X1 X2 : G) : (e (X2 ◇ (e (X0 ◇ X1)))) = (e (X2 ◇ (X0 ◇ (v (X1 ◇ X1))))) := by first | exact superpose eq47 eq30 | exact mod_symm (superpose eq47 eq30) | exact superpose eq30 eq47 | exact mod_symm (superpose eq30 eq47)
  have eq3683 (X0 X1 X2 : G) : (e (X2 ◇ (e (X0 ◇ X1)))) = (e (X1 ◇ (X0 ◇ X2))) := by first | exact superpose eq3537 eq3657 | exact mod_symm (superpose eq3537 eq3657) | exact superpose eq3657 eq3537 | exact mod_symm (superpose eq3657 eq3537)
  have eq3709 (X0 X1 X2 : G) : (e (X2 ◇ (X0 ◇ X1))) = (e (X1 ◇ (X0 ◇ X2))) := by first | exact superpose eq30 eq3683 | exact mod_symm (superpose eq30 eq3683) | exact superpose eq3683 eq30 | exact mod_symm (superpose eq3683 eq30)
  have eq3753 (X0 X1 : G) : (e (v X0)) = (e (v ((X0 ◇ (e X1)) ◇ X1))) := by first | exact superpose eq78 eq67 | exact mod_symm (superpose eq78 eq67) | exact superpose eq67 eq78 | exact mod_symm (superpose eq67 eq78)
  have eq3771 (X0 X1 : G) : (e (v (v (X0 ◇ (e X1))))) = (v (e (v (X0 ◇ X1)))) := by first | exact superpose eq67 eq17 | exact mod_symm (superpose eq67 eq17) | exact superpose eq17 eq67 | exact mod_symm (superpose eq17 eq67)
  have eq3774 (X0 X1 X2 : G) : (e (X2 ◇ (v (X0 ◇ (e X1))))) = (e (X2 ◇ (e (v (X0 ◇ X1))))) := by first | exact superpose eq67 eq30 | exact mod_symm (superpose eq67 eq30) | exact superpose eq30 eq67 | exact mod_symm (superpose eq30 eq67)
  have eq3785 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ (e X1)))) = (w X2 (e (v (X0 ◇ X1)))) := by first | exact superpose eq67 eq156 | exact mod_symm (superpose eq67 eq156) | exact superpose eq156 eq67 | exact mod_symm (superpose eq156 eq67)
  have eq3790 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ (e X1)))) = (w X2 (v (X0 ◇ X1))) := by first | exact superpose eq156 eq3785 | exact mod_symm (superpose eq156 eq3785) | exact superpose eq3785 eq156 | exact mod_symm (superpose eq3785 eq156)
  have eq3801 (X0 X1 X2 : G) : (e (X2 ◇ (v (X0 ◇ (e X1))))) = (e (X2 ◇ (v (X0 ◇ X1)))) := by first | exact superpose eq30 eq3774 | exact mod_symm (superpose eq30 eq3774) | exact superpose eq3774 eq30 | exact mod_symm (superpose eq3774 eq30)
  have eq3802 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (e (v (v (X0 ◇ (e X1))))) := by first | exact superpose eq17 eq3771 | exact mod_symm (superpose eq17 eq3771) | exact superpose eq3771 eq17 | exact mod_symm (superpose eq3771 eq17)
  have eq3976 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ (e (X0 ◇ X1)))) = (w X2 (X3 ◇ ((e X0) ◇ X1))) := by first | exact superpose eq31 eq157 | exact mod_symm (superpose eq31 eq157) | exact superpose eq157 eq31 | exact mod_symm (superpose eq157 eq31)
  have eq3978 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ (e (X0 ◇ X1)))) = (w X2 (X3 ◇ ((v (X0 ◇ X0)) ◇ X1))) := by first | exact superpose eq46 eq157 | exact mod_symm (superpose eq46 eq157) | exact superpose eq157 eq46 | exact mod_symm (superpose eq157 eq46)
  have eq3993 (X0 X1 X2 : G) : (w X1 X0) = (w X1 ((X0 ◇ (e X2)) ◇ X2)) := by first | exact superpose eq78 eq157 | exact mod_symm (superpose eq78 eq157) | exact superpose eq157 eq78 | exact mod_symm (superpose eq157 eq78)
  have eq4033 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ ((v (X0 ◇ X0)) ◇ X1))) = (w X2 (X3 ◇ (X0 ◇ X1))) := by first | exact superpose eq157 eq3978 | exact mod_symm (superpose eq157 eq3978) | exact superpose eq3978 eq157 | exact mod_symm (superpose eq3978 eq157)
  have eq4035 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ ((e X0) ◇ X1))) = (w X2 (X3 ◇ (X0 ◇ X1))) := by first | exact superpose eq157 eq3976 | exact mod_symm (superpose eq157 eq3976) | exact superpose eq3976 eq157 | exact mod_symm (superpose eq3976 eq157)
  have eq4120 (X0 X1 X2 X3 : G) : (w ((X0 ◇ (e X1)) ◇ X2) X3) = (w ((e (X0 ◇ X1)) ◇ X2) X3) := by first | exact superpose eq30 eq192 | exact mod_symm (superpose eq30 eq192) | exact superpose eq192 eq30 | exact mod_symm (superpose eq192 eq30)
  have eq4205 (X0 X1 X2 X3 : G) : (w ((X0 ◇ (e X1)) ◇ X2) X3) = (w ((X0 ◇ X1) ◇ X2) X3) := by first | exact superpose eq192 eq4120 | exact mod_symm (superpose eq192 eq4120) | exact superpose eq4120 eq192 | exact mod_symm (superpose eq4120 eq192)
  have eq4267 (X0 X1 : G) : (v (e (v (X0 ◇ X1)))) = (e (v (v ((e X0) ◇ X1)))) := by first | exact superpose eq195 eq17 | exact mod_symm (superpose eq195 eq17) | exact superpose eq17 eq195 | exact mod_symm (superpose eq17 eq195)
  have eq4284 (X0 X1 X2 : G) : (w X2 (e (v (X0 ◇ X1)))) = (w X2 (v ((e X0) ◇ X1))) := by first | exact superpose eq195 eq156 | exact mod_symm (superpose eq195 eq156) | exact superpose eq156 eq195 | exact mod_symm (superpose eq156 eq195)
  have eq4295 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ X1))) = (w X2 (v ((e X0) ◇ X1))) := by first | exact superpose eq156 eq4284 | exact mod_symm (superpose eq156 eq4284) | exact superpose eq4284 eq156 | exact mod_symm (superpose eq4284 eq156)
  have eq4310 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (e (v (v ((e X0) ◇ X1)))) := by first | exact superpose eq17 eq4267 | exact mod_symm (superpose eq17 eq4267) | exact superpose eq4267 eq17 | exact mod_symm (superpose eq4267 eq17)
  have eq4423 (X0 X1 : G) : (e (v ((e X0) ◇ (v X1)))) = (w (X1 ◇ (e (X0 ◇ X0))) X1) := by first | exact superpose eq37 eq288 | exact mod_symm (superpose eq37 eq288) | exact superpose eq288 eq37 | exact mod_symm (superpose eq288 eq37)
  have eq4430 (X0 : G) : (v (e (v (v (X0 ◇ X0))))) = (w X0 (v X0)) := by first | exact superpose eq288 eq234 | exact mod_symm (superpose eq288 eq234) | exact superpose eq234 eq288 | exact mod_symm (superpose eq234 eq288)
  have eq4442 (X0 X1 X2 : G) : (e (v (v (X0 ◇ (X1 ◇ (e X2)))))) = (w ((X1 ◇ (e X2)) ◇ X0) (X1 ◇ X2)) := by first | exact superpose eq288 eq157 | exact mod_symm (superpose eq288 eq157) | exact superpose eq157 eq288 | exact mod_symm (superpose eq157 eq288)
  have eq4498 (X0 X1 X2 : G) : (e (v (v (X0 ◇ (X1 ◇ (e X2)))))) = (w ((X1 ◇ X2) ◇ X0) (X1 ◇ X2)) := by first | exact superpose eq4205 eq4442 | exact mod_symm (superpose eq4205 eq4442) | exact superpose eq4442 eq4205 | exact mod_symm (superpose eq4442 eq4205)
  have eq4504 (X0 : G) : (e (v (v (v (X0 ◇ X0))))) = (w X0 (v X0)) := by first | exact superpose eq17 eq4430 | exact mod_symm (superpose eq17 eq4430) | exact superpose eq4430 eq17 | exact mod_symm (superpose eq4430 eq17)
  have eq4508 (X0 X1 : G) : (e (v ((e X0) ◇ (v X1)))) = (w (X1 ◇ (X0 ◇ X0)) X1) := by first | exact superpose eq161 eq4423 | exact mod_symm (superpose eq161 eq4423) | exact superpose eq4423 eq161 | exact mod_symm (superpose eq4423 eq161)
  have eq4530 (X0 X1 X2 : G) : (e (v (v (X0 ◇ (X1 ◇ (e X2)))))) = (e (v (v (X0 ◇ (X1 ◇ X2))))) := by first | exact superpose eq288 eq4498 | exact mod_symm (superpose eq288 eq4498) | exact superpose eq4498 eq288 | exact mod_symm (superpose eq4498 eq288)
  have eq4532 (X0 : G) : (e (v (v X0))) = (w X0 (v X0)) := by first | exact superpose eq307 eq4504 | exact mod_symm (superpose eq307 eq4504) | exact superpose eq4504 eq307 | exact mod_symm (superpose eq4504 eq307)
  have eq4535 (X0 X1 : G) : (e (v (X0 ◇ (v X1)))) = (w (X1 ◇ (X0 ◇ X0)) X1) := by first | exact superpose eq195 eq4508 | exact mod_symm (superpose eq195 eq4508) | exact superpose eq4508 eq195 | exact mod_symm (superpose eq4508 eq195)
  have eq5129 (X0 X1 : G) : (e ((v X1) ◇ X0)) = (e (v (X0 ◇ (X0 ◇ X1)))) := by first | exact superpose eq85 eq543 | exact mod_symm (superpose eq85 eq543) | exact superpose eq543 eq85 | exact mod_symm (superpose eq543 eq85)
  have eq5364 (X0 X1 X2 : G) : (e (v X0)) = (e (X1 ◇ (v (X2 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0)))))) := by first | exact superpose eq80 eq646 | exact mod_symm (superpose eq80 eq646) | exact superpose eq646 eq80 | exact mod_symm (superpose eq646 eq80)
  have eq5453 (X0 X1 : G) : (e (v X0)) = (e (X1 ◇ (v ((X1 ◇ X0) ◇ X1)))) := by first | exact superpose eq1129 eq5364 | exact mod_symm (superpose eq1129 eq5364) | exact superpose eq5364 eq1129 | exact mod_symm (superpose eq5364 eq1129)
  have eq7088 (X0 X1 X2 : G) : (w X1 (e (v X0))) = (w X1 (v ((X0 ◇ (e X2)) ◇ X2))) := by first | exact superpose eq3753 eq156 | exact mod_symm (superpose eq3753 eq156) | exact superpose eq156 eq3753 | exact mod_symm (superpose eq156 eq3753)
  have eq7107 (X0 X1 X2 : G) : (w X1 (v X0)) = (w X1 (v ((X0 ◇ (e X2)) ◇ X2))) := by first | exact superpose eq156 eq7088 | exact mod_symm (superpose eq156 eq7088) | exact superpose eq7088 eq156 | exact mod_symm (superpose eq7088 eq156)
  have eq7782 (X0 X1 X2 X3 : G) : (w X1 ((e X2) ◇ ((e X3) ◇ X0))) = (w X1 (X0 ◇ (X3 ◇ X2))) := by first | exact superpose eq285 eq3993 | exact mod_symm (superpose eq285 eq3993) | exact superpose eq3993 eq285 | exact mod_symm (superpose eq3993 eq285)
  have eq7820 (X0 X1 X2 X3 : G) : (w X1 (X0 ◇ (X3 ◇ X2))) = (w X1 ((e X2) ◇ (X3 ◇ X0))) := by first | exact superpose eq4035 eq7782 | exact mod_symm (superpose eq4035 eq7782) | exact superpose eq7782 eq4035 | exact mod_symm (superpose eq7782 eq4035)
  have eq7963 (X0 X1 X2 X3 : G) : (w X1 (X0 ◇ (X3 ◇ X2))) = (w X1 (X2 ◇ (X3 ◇ X0))) := by first | exact superpose eq191 eq7820 | exact mod_symm (superpose eq191 eq7820) | exact superpose eq7820 eq191 | exact mod_symm (superpose eq7820 eq191)
  have eq9309 (X0 X1 X2 X3 : G) : (v ((X1 ◇ X2) ◇ X0)) = (X3 ◇ ((v X2) ◇ (X3 ◇ (v (X0 ◇ X1))))) := by first | exact superpose eq674 eq296 | exact mod_symm (superpose eq674 eq296) | exact superpose eq296 eq674 | exact mod_symm (superpose eq296 eq674)
  have eq11014 (X0 X1 X2 X3 : G) : (w ((e (X0 ◇ (v X1))) ◇ X2) X3) = (w ((X0 ◇ (X1 ◇ (v X1))) ◇ X2) X3) := by first | exact superpose eq257 eq192 | exact mod_symm (superpose eq257 eq192) | exact superpose eq192 eq257 | exact mod_symm (superpose eq192 eq257)
  have eq11039 (X0 X1 X2 X3 : G) : (w ((X0 ◇ (v X1)) ◇ X2) X3) = (w ((X0 ◇ (X1 ◇ (v X1))) ◇ X2) X3) := by first | exact superpose eq192 eq11014 | exact mod_symm (superpose eq192 eq11014) | exact superpose eq11014 eq192 | exact mod_symm (superpose eq11014 eq192)
  have eq12683 (X0 X1 X2 X3 X4 : G) : (w X3 (X4 ◇ (e (X0 ◇ (X1 ◇ X2))))) = (w X3 (X4 ◇ (X2 ◇ (X1 ◇ X0)))) := by first | exact superpose eq3709 eq157 | exact mod_symm (superpose eq3709 eq157) | exact superpose eq157 eq3709 | exact mod_symm (superpose eq157 eq3709)
  have eq12717 (X0 X1 X2 X3 X4 : G) : (w X3 (X4 ◇ (X0 ◇ (X1 ◇ X2)))) = (w X3 (X4 ◇ (X2 ◇ (X1 ◇ X0)))) := by first | exact superpose eq157 eq12683 | exact mod_symm (superpose eq157 eq12683) | exact superpose eq12683 eq157 | exact mod_symm (superpose eq12683 eq157)
  have eq15595 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ (e ((v X0) ◇ X1)))) = (w X2 (X3 ◇ (v (X1 ◇ (X1 ◇ X0))))) := by first | exact superpose eq5129 eq157 | exact mod_symm (superpose eq5129 eq157) | exact superpose eq157 eq5129 | exact mod_symm (superpose eq157 eq5129)
  have eq15632 (X0 X1 X2 X3 : G) : (w X2 (X3 ◇ ((v X0) ◇ X1))) = (w X2 (X3 ◇ (v (X1 ◇ (X1 ◇ X0))))) := by first | exact superpose eq157 eq15595 | exact mod_symm (superpose eq157 eq15595) | exact superpose eq15595 eq157 | exact mod_symm (superpose eq15595 eq157)
  have eq17971 (X0 X1 X2 : G) : (e (v ((X1 ◇ X2) ◇ X0))) = (e (X2 ◇ (v ((X0 ◇ X1) ◇ X2)))) := by first | exact superpose eq674 eq5453 | exact mod_symm (superpose eq674 eq5453) | exact superpose eq5453 eq674 | exact mod_symm (superpose eq5453 eq674)
  have eq45353 (X0 X1 X2 : G) : (e ((e X2) ◇ (v ((v X0) ◇ (e X2))))) = (e (v (v ((e X1) ◇ (X0 ◇ (e (X1 ◇ (X2 ◇ X2)))))))) := by first | exact superpose eq868 eq5453 | exact mod_symm (superpose eq868 eq5453) | exact superpose eq5453 eq868 | exact mod_symm (superpose eq5453 eq868)
  have eq45364 (X0 X1 X2 : G) : (e ((e X2) ◇ (v ((v X0) ◇ (e X2))))) = (e (v (v ((e X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by first | exact superpose eq4530 eq45353 | exact mod_symm (superpose eq4530 eq45353) | exact superpose eq45353 eq4530 | exact mod_symm (superpose eq45353 eq4530)
  have eq45622 (X0 X1 X2 : G) : (e ((e X2) ◇ (v ((v X0) ◇ (e X2))))) = (e (v (v (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by first | exact superpose eq4310 eq45364 | exact mod_symm (superpose eq4310 eq45364) | exact superpose eq45364 eq4310 | exact mod_symm (superpose eq45364 eq4310)
  have eq45865 (X0 X2 : G) : (e ((e X2) ◇ (v ((v X0) ◇ (e X2))))) = (e (v (v ((X2 ◇ X0) ◇ X2)))) := by first | exact superpose eq1128 eq45622 | exact mod_symm (superpose eq1128 eq45622) | exact superpose eq45622 eq1128 | exact mod_symm (superpose eq45622 eq1128)
  have eq46093 (X0 X2 : G) : (e ((e X2) ◇ (v ((v X0) ◇ X2)))) = (e (v (v ((X2 ◇ X0) ◇ X2)))) := by first | exact superpose eq3801 eq45865 | exact mod_symm (superpose eq3801 eq45865) | exact superpose eq45865 eq3801 | exact mod_symm (superpose eq45865 eq3801)
  have eq46304 (X0 X2 : G) : (e (X2 ◇ (v ((v X0) ◇ X2)))) = (e (v (v ((X2 ◇ X0) ◇ X2)))) := by first | exact superpose eq31 eq46093 | exact mod_symm (superpose eq31 eq46093) | exact superpose eq46093 eq31 | exact mod_symm (superpose eq46093 eq31)
  have eq48317 (X0 X1 : G) : (e (X1 ◇ X1)) = (e (v (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by first | exact superpose eq300 eq711 | exact mod_symm (superpose eq300 eq711) | exact superpose eq711 eq300 | exact mod_symm (superpose eq711 eq300)
  have eq61611 (X0 X1 X2 X3 X4 : G) : (w X3 (v (X4 ◇ (X2 ◇ (X1 ◇ X0))))) = (w X3 (v (X4 ◇ (e (X0 ◇ (X1 ◇ X2)))))) := by first | exact superpose eq3709 eq3790 | exact mod_symm (superpose eq3709 eq3790) | exact superpose eq3790 eq3709 | exact mod_symm (superpose eq3790 eq3709)
  have eq61625 (X0 X1 X2 X3 : G) : (w X2 (v (X3 ◇ (e (X0 ◇ X1))))) = (w X2 (v (X3 ◇ ((e X0) ◇ X1)))) := by first | exact superpose eq31 eq3790 | exact mod_symm (superpose eq31 eq3790) | exact superpose eq3790 eq31 | exact mod_symm (superpose eq3790 eq31)
  have eq61698 (X0 X1 X2 X3 : G) : (w X3 (v ((e (X0 ◇ (X1 ◇ X1))) ◇ X2))) = (w X3 ((e ((v X0) ◇ X1)) ◇ (v (e X2)))) := by first | exact superpose eq525 eq3790 | exact mod_symm (superpose eq525 eq3790) | exact superpose eq3790 eq525 | exact mod_symm (superpose eq3790 eq525)
  have eq61839 (X0 X1 X2 X3 : G) : (w X3 (v ((e (X0 ◇ (X1 ◇ X1))) ◇ X2))) = (w X3 (((v X0) ◇ X1) ◇ (v (e X2)))) := by first | exact superpose eq191 eq61698 | exact mod_symm (superpose eq191 eq61698) | exact superpose eq61698 eq191 | exact mod_symm (superpose eq61698 eq191)
  have eq61895 (X0 X1 X2 X3 : G) : (w X2 (v (X3 ◇ ((e X0) ◇ X1)))) = (w X2 (v (X3 ◇ (X0 ◇ X1)))) := by first | exact superpose eq3790 eq61625 | exact mod_symm (superpose eq3790 eq61625) | exact superpose eq61625 eq3790 | exact mod_symm (superpose eq61625 eq3790)
  have eq61909 (X0 X1 X2 X3 X4 : G) : (w X3 (v (X4 ◇ (X2 ◇ (X1 ◇ X0))))) = (w X3 (v (X4 ◇ (X0 ◇ (X1 ◇ X2))))) := by first | exact superpose eq3790 eq61611 | exact mod_symm (superpose eq3790 eq61611) | exact superpose eq61611 eq3790 | exact mod_symm (superpose eq61611 eq3790)
  have eq61953 (X0 X1 X2 X3 : G) : (w X3 (v ((e (X0 ◇ (X1 ◇ X1))) ◇ X2))) = (w X3 (((v X0) ◇ X1) ◇ (e (v X2)))) := by first | exact superpose eq17 eq61839 | exact mod_symm (superpose eq17 eq61839) | exact superpose eq61839 eq17 | exact mod_symm (superpose eq61839 eq17)
  have eq61997 (X0 X1 X2 X3 : G) : (w X3 (((v X0) ◇ X1) ◇ (v X2))) = (w X3 (v ((e (X0 ◇ (X1 ◇ X1))) ◇ X2))) := by first | exact superpose eq157 eq61953 | exact mod_symm (superpose eq157 eq61953) | exact superpose eq61953 eq157 | exact mod_symm (superpose eq61953 eq157)
  have eq62014 (X0 X1 X2 X3 : G) : (w X3 (((v X0) ◇ X1) ◇ (v X2))) = (w X3 (v ((X0 ◇ (X1 ◇ X1)) ◇ X2))) := by first | exact superpose eq4295 eq61997 | exact mod_symm (superpose eq4295 eq61997) | exact superpose eq61997 eq4295 | exact mod_symm (superpose eq61997 eq4295)
  have eq63441 (X0 X1 X2 : G) : (e (v (v (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (e (v ((v X0) ◇ (e ((v X1) ◇ X2))))) := by first | exact superpose eq524 eq3802 | exact mod_symm (superpose eq524 eq3802) | exact superpose eq3802 eq524 | exact mod_symm (superpose eq3802 eq524)
  have eq63669 (X0 X1 X2 : G) : (e (v (v (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (e (v ((v X0) ◇ ((v X1) ◇ X2)))) := by first | exact superpose eq67 eq63441 | exact mod_symm (superpose eq67 eq63441) | exact superpose eq63441 eq67 | exact mod_symm (superpose eq63441 eq67)
  have eq63810 (X0 X1 X2 : G) : (e (v (v (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (e (v (X2 ◇ (v (X1 ◇ X0))))) := by first | exact superpose eq678 eq63669 | exact mod_symm (superpose eq678 eq63669) | exact superpose eq63669 eq678 | exact mod_symm (superpose eq63669 eq678)
  have eq64077 (X0 X1 : G) : (w (X0 ◇ ((v (X1 ◇ (v X1))) ◇ (X0 ◇ (v (X1 ◇ (v X1)))))) (v (v X1))) = (e (v (X0 ◇ ((v (X1 ◇ (v X1))) ◇ (X0 ◇ (v (X1 ◇ (v X1)))))))) := by first | exact superpose eq3320 eq1404 | exact mod_symm (superpose eq3320 eq1404) | exact superpose eq1404 eq3320 | exact mod_symm (superpose eq1404 eq3320)
  have eq64090 (X0 X1 : G) : (w (X0 ◇ ((v (X1 ◇ (v X1))) ◇ (X0 ◇ (v (X1 ◇ (v X1)))))) (v (v X1))) = (e ((v (X1 ◇ (v X1))) ◇ (v (X1 ◇ (v X1))))) := by first | exact superpose eq48317 eq64077 | exact mod_symm (superpose eq48317 eq64077) | exact superpose eq64077 eq48317 | exact mod_symm (superpose eq64077 eq48317)
  have eq64206 (X0 X1 : G) : (w (X0 ◇ ((v (X1 ◇ (v X1))) ◇ (X0 ◇ (v (X1 ◇ (v X1)))))) (v (v X1))) = (e ((v (X1 ◇ (v X1))) ◇ (v (v X1)))) := by first | exact superpose eq1412 eq64090 | exact mod_symm (superpose eq1412 eq64090) | exact superpose eq64090 eq1412 | exact mod_symm (superpose eq64090 eq1412)
  have eq64306 (X0 X1 : G) : (e ((v (v X1)) ◇ (v (v X1)))) = (w (X0 ◇ ((v (X1 ◇ (v X1))) ◇ (X0 ◇ (v (X1 ◇ (v X1)))))) (v (v X1))) := by first | exact superpose eq1411 eq64206 | exact mod_symm (superpose eq1411 eq64206) | exact superpose eq64206 eq1411 | exact mod_symm (superpose eq64206 eq1411)
  have eq64393 (X1 : G) : (e ((v (v X1)) ◇ (v (v X1)))) = (w (v (((v X1) ◇ (X1 ◇ (v X1))) ◇ X1)) (v (v X1))) := by first | exact superpose eq9309 eq64306 | exact mod_symm (superpose eq9309 eq64306) | exact superpose eq64306 eq9309 | exact mod_symm (superpose eq64306 eq9309)
  have eq64468 (X1 : G) : (e ((v (v X1)) ◇ (v (v X1)))) = (v (w (((v X1) ◇ (X1 ◇ (v X1))) ◇ X1) (v X1))) := by first | exact superpose eq132 eq64393 | exact mod_symm (superpose eq132 eq64393) | exact superpose eq64393 eq132 | exact mod_symm (superpose eq64393 eq132)
  have eq64534 (X1 : G) : (e ((v (v X1)) ◇ (v (v X1)))) = (v (w (((v X1) ◇ (v X1)) ◇ X1) (v X1))) := by first | exact superpose eq11039 eq64468 | exact mod_symm (superpose eq11039 eq64468) | exact superpose eq64468 eq11039 | exact mod_symm (superpose eq64468 eq11039)
  have eq64586 (X1 : G) : (e ((v (v X1)) ◇ (v (v X1)))) = (w ((v X1) ◇ (v X1)) (v (v X1))) := by first | exact superpose eq622 eq64534 | exact mod_symm (superpose eq622 eq64534) | exact superpose eq64534 eq622 | exact mod_symm (superpose eq64534 eq622)
  have eq64624 (X1 : G) : (e ((v (v X1)) ◇ (v (v X1)))) = (w (v (X1 ◇ X1)) (v (v X1))) := by first | exact superpose eq15 eq64586 | exact mod_symm (superpose eq15 eq64586) | exact superpose eq64586 eq15 | exact mod_symm (superpose eq64586 eq15)
  have eq64656 (X1 : G) : (e ((v (v X1)) ◇ (v (v X1)))) = (v (w (X1 ◇ X1) (v X1))) := by first | exact superpose eq132 eq64624 | exact mod_symm (superpose eq132 eq64624) | exact superpose eq64624 eq132 | exact mod_symm (superpose eq64624 eq132)
  have eq64679 (X1 : G) : (e ((v (v X1)) ◇ (v (v X1)))) = (w X1 (v (v X1))) := by first | exact superpose eq234 eq64656 | exact mod_symm (superpose eq234 eq64656) | exact superpose eq64656 eq234 | exact mod_symm (superpose eq64656 eq234)
  have eq64694 (X1 : G) : (e (v ((v X1) ◇ (v X1)))) = (w X1 (v (v X1))) := by first | exact superpose eq15 eq64679 | exact mod_symm (superpose eq15 eq64679) | exact superpose eq64679 eq15 | exact mod_symm (superpose eq64679 eq15)
  have eq64708 (X1 : G) : (e (v X1)) = (w X1 (v (v X1))) := by first | exact superpose eq29 eq64694 | exact mod_symm (superpose eq29 eq64694) | exact superpose eq64694 eq29 | exact mod_symm (superpose eq64694 eq29)
  have eq116557 (X0 X1 X2 X3 : G) : (w X1 (v ((e X2) ◇ ((e X3) ◇ X0)))) = (w X1 (v (X0 ◇ (X3 ◇ X2)))) := by first | exact superpose eq285 eq7107 | exact mod_symm (superpose eq285 eq7107) | exact superpose eq7107 eq285 | exact mod_symm (superpose eq7107 eq285)
  have eq116767 (X0 X1 X2 X3 : G) : (w X1 (v (X0 ◇ (X3 ◇ X2)))) = (w X1 (v ((e X2) ◇ (X3 ◇ X0)))) := by first | exact superpose eq61895 eq116557 | exact mod_symm (superpose eq61895 eq116557) | exact superpose eq116557 eq61895 | exact mod_symm (superpose eq116557 eq61895)
  have eq116938 (X0 X1 X2 X3 : G) : (w X1 (v (X0 ◇ (X3 ◇ X2)))) = (w X1 (v (X2 ◇ (X3 ◇ X0)))) := by first | exact superpose eq4295 eq116767 | exact mod_symm (superpose eq4295 eq116767) | exact superpose eq116767 eq4295 | exact mod_symm (superpose eq116767 eq4295)
  have eq147055 (X0 X1 X2 : G) : (w X0 (w X1 X2)) = (e (v (v (((w X1 X2) ◇ (X0 ◇ (e (v ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X2))))) ◇ (w X1 X2))))) := by first | exact superpose eq1281 eq288 | exact mod_symm (superpose eq1281 eq288) | exact superpose eq288 eq1281 | exact mod_symm (superpose eq288 eq1281)
  have eq147168 (X0 X1 X2 : G) : (w X0 (w X1 X2)) = (e ((w X1 X2) ◇ (v ((v (X0 ◇ (e (v ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X2))))) ◇ (w X1 X2))))) := by first | exact superpose eq46304 eq147055 | exact mod_symm (superpose eq46304 eq147055) | exact superpose eq147055 eq46304 | exact mod_symm (superpose eq147055 eq46304)
  have eq147396 (X0 X1 X2 : G) : (w X0 (w X1 X2)) = (e ((w X1 X2) ◇ (v (((v X0) ◇ (w X1 X2)) ◇ (w X1 X2))))) := by first | exact superpose eq411 eq147168 | exact mod_symm (superpose eq411 eq147168) | exact superpose eq147168 eq411 | exact mod_symm (superpose eq147168 eq411)
  have eq147579 (X0 X1 X2 : G) : (w X0 (w X1 X2)) = (e (v (((w X1 X2) ◇ (w X1 X2)) ◇ (v X0)))) := by first | exact superpose eq17971 eq147396 | exact mod_symm (superpose eq17971 eq147396) | exact superpose eq147396 eq17971 | exact mod_symm (superpose eq147396 eq17971)
  have eq147736 (X0 X1 X2 : G) : (w X0 (w X1 X2)) = (e ((w X1 X2) ◇ (v (v X0)))) := by first | exact superpose eq646 eq147579 | exact mod_symm (superpose eq646 eq147579) | exact superpose eq147579 eq646 | exact mod_symm (superpose eq147579 eq646)
  have eq148138 (X0 X1 : G) : (w X1 (e (v (v X0)))) = (e ((e (v (v X0))) ◇ (v (v X1)))) := by first | exact superpose eq4532 eq147736 | exact mod_symm (superpose eq4532 eq147736) | exact superpose eq147736 eq4532 | exact mod_symm (superpose eq147736 eq4532)
  have eq148142 (X0 X1 : G) : (w X1 (e (v X0))) = (e ((e (v X0)) ◇ (v (v X1)))) := by first | exact superpose eq64708 eq147736 | exact mod_symm (superpose eq64708 eq147736) | exact superpose eq147736 eq64708 | exact mod_symm (superpose eq147736 eq64708)
  have eq148409 (X0 X1 : G) : (w X1 (e (v X0))) = (e ((v X0) ◇ (v (v X1)))) := by first | exact superpose eq31 eq148142 | exact mod_symm (superpose eq31 eq148142) | exact superpose eq148142 eq31 | exact mod_symm (superpose eq148142 eq31)
  have eq148410 (X0 X1 : G) : (w X1 (e (v (v X0)))) = (e ((v (v X0)) ◇ (v (v X1)))) := by first | exact superpose eq31 eq148138 | exact mod_symm (superpose eq31 eq148138) | exact superpose eq148138 eq31 | exact mod_symm (superpose eq148138 eq31)
  have eq148485 (X0 X1 : G) : (w X1 (e (v X0))) = (e (v (X0 ◇ (v X1)))) := by first | exact superpose eq15 eq148409 | exact mod_symm (superpose eq15 eq148409) | exact superpose eq148409 eq15 | exact mod_symm (superpose eq148409 eq15)
  have eq148486 (X0 X1 : G) : (w X1 (e (v (v X0)))) = (e (v ((v X0) ◇ (v X1)))) := by first | exact superpose eq15 eq148410 | exact mod_symm (superpose eq15 eq148410) | exact superpose eq148410 eq15 | exact mod_symm (superpose eq148410 eq15)
  have eq148536 (X0 X1 : G) : (w X1 (v X0)) = (e (v (X0 ◇ (v X1)))) := by first | exact superpose eq156 eq148485 | exact mod_symm (superpose eq156 eq148485) | exact superpose eq148485 eq156 | exact mod_symm (superpose eq148485 eq156)
  have eq148537 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (w X1 (e (v (v X0)))) := by first | exact superpose eq15 eq148486 | exact mod_symm (superpose eq15 eq148486) | exact superpose eq148486 eq15 | exact mod_symm (superpose eq148486 eq15)
  have eq148569 (X0 X1 : G) : (e (v (v (X0 ◇ X1)))) = (w X1 (v (v X0))) := by first | exact superpose eq156 eq148537 | exact mod_symm (superpose eq156 eq148537) | exact superpose eq148537 eq156 | exact mod_symm (superpose eq148537 eq156)
  have eq149200 (X0 X1 : G) : (w (X1 ◇ (X0 ◇ X0)) X1) = (e (v (((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (v X1)))) := by first | exact superpose eq1460 eq4535 | exact mod_symm (superpose eq1460 eq4535) | exact superpose eq4535 eq1460 | exact mod_symm (superpose eq4535 eq1460)
  have eq149389 (X0 X1 : G) : (w (X1 ◇ (X0 ◇ X0)) X1) = (w X1 (v ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := by first | exact superpose eq148536 eq149200 | exact mod_symm (superpose eq148536 eq149200) | exact superpose eq149200 eq148536 | exact mod_symm (superpose eq149200 eq148536)
  have eq150024 (X0 X1 : G) : (w (X1 ◇ (X0 ◇ X0)) X1) = (w X1 (v ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by first | exact superpose eq61909 eq149389 | exact mod_symm (superpose eq61909 eq149389) | exact superpose eq149389 eq61909 | exact mod_symm (superpose eq149389 eq61909)
  have eq150540 (X0 X1 : G) : (w (X1 ◇ (X0 ◇ X0)) X1) = (w X1 (v ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))))) := by first | exact superpose eq116938 eq150024 | exact mod_symm (superpose eq116938 eq150024) | exact superpose eq150024 eq116938 | exact mod_symm (superpose eq150024 eq116938)
  have eq150960 (X0 X1 : G) : (w (X1 ◇ (X0 ◇ X0)) X1) = (w X1 (((v X0) ◇ X0) ◇ (v (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))))) := by first | exact superpose eq62014 eq150540 | exact mod_symm (superpose eq62014 eq150540) | exact superpose eq150540 eq62014 | exact mod_symm (superpose eq150540 eq62014)
  have eq151302 (X0 X1 : G) : (w (X1 ◇ (X0 ◇ X0)) X1) = (w X1 (((v X0) ◇ X0) ◇ ((v ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0))) := by first | exact superpose eq15632 eq150960 | exact mod_symm (superpose eq15632 eq150960) | exact superpose eq150960 eq15632 | exact mod_symm (superpose eq150960 eq15632)
  have eq151591 (X0 X1 : G) : (w (X1 ◇ (X0 ◇ X0)) X1) = (w X1 (((v X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by first | exact superpose eq4033 eq151302 | exact mod_symm (superpose eq4033 eq151302) | exact superpose eq151302 eq4033 | exact mod_symm (superpose eq151302 eq4033)
  have eq151821 (X0 X1 : G) : (w (X1 ◇ (X0 ◇ X0)) X1) = (w X1 (X0 ◇ ((X0 ◇ X0) ◇ ((v X0) ◇ X0)))) := by first | exact superpose eq7963 eq151591 | exact mod_symm (superpose eq7963 eq151591) | exact superpose eq151591 eq7963 | exact mod_symm (superpose eq151591 eq7963)
  have eq151994 (X0 X1 : G) : (w (X1 ◇ (X0 ◇ X0)) X1) = (w X1 (X0 ◇ (X0 ◇ ((v X0) ◇ (X0 ◇ X0))))) := by first | exact superpose eq12717 eq151821 | exact mod_symm (superpose eq12717 eq151821) | exact superpose eq151821 eq12717 | exact mod_symm (superpose eq151821 eq12717)
  have eq152110 (X0 X1 : G) : (w X1 (v X0)) = (w (X1 ◇ (X0 ◇ X0)) X1) := by first | exact superpose eq13 eq151994 | exact mod_symm (superpose eq13 eq151994) | exact superpose eq151994 eq13 | exact mod_symm (superpose eq151994 eq13)
  have eq155646 (X0 X1 X2 : G) : (w X2 (w X0 (v X1))) = (w X2 (v (X1 ◇ (v X0)))) := by first | exact superpose eq148536 eq156 | exact mod_symm (superpose eq148536 eq156) | exact superpose eq156 eq148536 | exact mod_symm (superpose eq156 eq148536)
  have eq159131 (X0 X1 : G) : (e (v (v X0))) = (w X1 (v (v (X0 ◇ X1)))) := by first | exact superpose eq78 eq148569 | exact mod_symm (superpose eq78 eq148569) | exact superpose eq148569 eq78 | exact mod_symm (superpose eq148569 eq78)
  have eq169930 (X0 X1 X2 : G) : (w (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) X2) = (w X2 (v (X2 ◇ X1))) := by first | exact superpose eq300 eq152110 | exact mod_symm (superpose eq300 eq152110) | exact superpose eq152110 eq300 | exact mod_symm (superpose eq152110 eq300)
  have eq170131 (X1 X2 : G) : (w ((X1 ◇ X1) ◇ X2) X2) = (w X2 (v (X2 ◇ X1))) := by first | exact superpose eq1128 eq169930 | exact mod_symm (superpose eq1128 eq169930) | exact superpose eq169930 eq1128 | exact mod_symm (superpose eq169930 eq1128)
  have eq174277 (X0 X1 : G) : (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) = (w X1 (w X0 X1)) := by first | exact superpose eq159131 eq162 | exact mod_symm (superpose eq159131 eq162) | exact superpose eq162 eq159131 | exact mod_symm (superpose eq162 eq159131)
  have eq174361 (X0 X1 : G) : (e (v (X0 ◇ (v (X1 ◇ X0))))) = (w X1 (w X0 X1)) := by first | exact superpose eq63810 eq174277 | exact mod_symm (superpose eq63810 eq174277) | exact superpose eq174277 eq63810 | exact mod_symm (superpose eq174277 eq63810)
  have eq174473 (X0 X1 : G) : (w (X1 ◇ X0) (v X0)) = (w X1 (w X0 X1)) := by first | exact superpose eq148536 eq174361 | exact mod_symm (superpose eq148536 eq174361) | exact superpose eq174361 eq148536 | exact mod_symm (superpose eq174361 eq148536)
  have eq283301 (X0 X1 : G) : (w X1 (v (X1 ◇ (v X0)))) = (w ((v (X0 ◇ X0)) ◇ X1) X1) := by first | exact superpose eq15 eq170131 | exact mod_symm (superpose eq15 eq170131) | exact superpose eq170131 eq15 | exact mod_symm (superpose eq170131 eq15)
  have eq283381 (X0 X1 : G) : (w (X0 ◇ X1) X1) = (w X1 (v (X1 ◇ (v X0)))) := by first | exact superpose eq3569 eq283301 | exact mod_symm (superpose eq3569 eq283301) | exact superpose eq283301 eq3569 | exact mod_symm (superpose eq283301 eq3569)
  have eq283409 (X0 X1 : G) : (w (X0 ◇ X1) X1) = (w X1 (w X0 (v X1))) := by first | exact superpose eq155646 eq283381 | exact mod_symm (superpose eq155646 eq283381) | exact superpose eq283381 eq155646 | exact mod_symm (superpose eq283381 eq155646)
  have eq283710 (X0 X1 : G) : (w X1 (w X0 (w X1 X0))) = (w ((X0 ◇ X1) ◇ X1) X1) := by first | exact superpose eq174473 eq283409 | exact mod_symm (superpose eq174473 eq283409) | exact superpose eq283409 eq174473 | exact mod_symm (superpose eq283409 eq174473)
  have eq283851 (X0 X1 : G) : (w X0 X1) = (w X1 (w X0 (w X1 X0))) := by first | exact superpose eq78 eq283710 | exact mod_symm (superpose eq78 eq283710) | exact superpose eq283710 eq78 | exact mod_symm (superpose eq283710 eq78)
  have eq284593 : (w x y) ≠ (w x y) := by first | exact superpose eq283851 eq21 | exact mod_symm (superpose eq283851 eq21) | exact superpose eq21 eq283851 | exact mod_symm (superpose eq21 eq283851)
  first | exact eq284593 rfl | exact eq284593 _ rfl | exact eq284593 _ _ rfl | exact eq284593 _ _ _ rfl


/-- Equation 3545 `x ◇ y = y ◇ ((x ◇ x) ◇ x)` is term-definable from equation 546 over finite magmas, via the term
`x □ y := u^[3N+1] ((x ◇ x) ◇ (y ◇ x))` where `u a = a ◇ a`. -/
private theorem aux546_3545 [Magma G] (h : Equation546 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, v (e a) ◇ v (e a) = e a) (hvue : ∀ a : G, v (e a ◇ e a) = e a)
    (hw : ∀ a b : G, w a b = (e (v (v ((a ◇ a) ◇ (b ◇ a))))))
    (x y : G) :
    (w x y) =
      (w y (w (w x x) x)) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ (v (e X0))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ (e X0))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (v ((X0 ◇ X0) ◇ (X1 ◇ X0))))) := mod_symm (hw ..)
  have eq21 : (w x y) ≠ (w y (w (w x x) x)) := mod_symm nh
  have eq26 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq27 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq28 (X0 : G) : (e X0) = (v (e (X0 ◇ X0))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq29 (X0 : G) : (e X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq17 eq28 | exact mod_symm (superpose eq17 eq28) | exact superpose eq28 eq17 | exact mod_symm (superpose eq28 eq17)
  have eq30 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq27 | exact mod_symm (superpose eq14 eq27) | exact superpose eq27 eq14 | exact mod_symm (superpose eq27 eq14)
  have eq31 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq32 (X0 X1 : G) : (v ((e X0) ◇ X1)) = ((e (v X0)) ◇ (v X1)) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq33 (X0 X1 : G) : (v (((e X0) ◇ (e X0)) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq34 (X0 X1 : G) : (v (X1 ◇ (e X0))) = ((v X1) ◇ (e (v X0))) := by first | exact superpose eq17 eq15 | exact mod_symm (superpose eq17 eq15) | exact superpose eq15 eq17 | exact mod_symm (superpose eq15 eq17)
  have eq35 (X0 X1 : G) : (v (X1 ◇ ((e X0) ◇ (e X0)))) = ((v X1) ◇ (e X0)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq36 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X1 ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35) | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14)
  have eq37 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v ((e (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq33 | exact mod_symm (superpose eq14 eq33) | exact superpose eq33 eq14 | exact mod_symm (superpose eq33 eq14)
  have eq39 (X0 : G) : (e (v X0)) = (e (v (v (X0 ◇ X0)))) := by first | exact superpose eq15 eq29 | exact mod_symm (superpose eq15 eq29) | exact superpose eq29 eq15 | exact mod_symm (superpose eq29 eq15)
  have eq64 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq30 eq17 | exact mod_symm (superpose eq30 eq17) | exact superpose eq17 eq30 | exact mod_symm (superpose eq17 eq30)
  have eq67 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq17 eq64 | exact mod_symm (superpose eq17 eq64) | exact superpose eq64 eq17 | exact mod_symm (superpose eq64 eq17)
  have eq75 (X0 X1 : G) : ((v (e X0)) ◇ ((v (e X0)) ◇ (X1 ◇ (e X0)))) = X1 := by first | exact superpose eq18 eq13 | exact mod_symm (superpose eq18 eq13) | exact superpose eq13 eq18 | exact mod_symm (superpose eq13 eq18)
  have eq77 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X2 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq78 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq79 (X0 X1 : G) : ((e (v X0)) ◇ ((e (v X0)) ◇ (X1 ◇ (e X0)))) = X1 := by first | exact superpose eq17 eq75 | exact mod_symm (superpose eq17 eq75) | exact superpose eq75 eq17 | exact mod_symm (superpose eq75 eq17)
  have eq83 (X0 : G) : (v (e X0)) = ((e X0) ◇ (v (e X0))) := by first | exact superpose eq18 eq78 | exact mod_symm (superpose eq18 eq78) | exact superpose eq78 eq18 | exact mod_symm (superpose eq78 eq18)
  have eq85 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X1 ◇ (X2 ◇ X0)) := by first | exact superpose eq78 eq13 | exact mod_symm (superpose eq78 eq13) | exact superpose eq13 eq78 | exact mod_symm (superpose eq13 eq78)
  have eq89 (X0 : G) : (e (v X0)) = ((e X0) ◇ (e (v X0))) := by first | exact superpose eq17 eq83 | exact mod_symm (superpose eq17 eq83) | exact superpose eq83 eq17 | exact mod_symm (superpose eq83 eq17)
  have eq92 (X0 : G) : (e (v X0)) = (e (X0 ◇ (v X0))) := by first | exact superpose eq14 eq89 | exact mod_symm (superpose eq14 eq89) | exact superpose eq89 eq14 | exact mod_symm (superpose eq89 eq14)
  have eq93 (X0 X1 : G) : (w (e X0) X1) = (e (v (v ((e (X0 ◇ X0)) ◇ (X1 ◇ (e X0)))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq94 (X0 X1 : G) : (w (v X0) X1) = (e (v (v ((v (X0 ◇ X0)) ◇ (X1 ◇ (v X0)))))) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  have eq95 (X0 X1 : G) : (w (v (e X0)) X1) = (e (v (v ((e X0) ◇ (X1 ◇ (v (e X0))))))) := by first | exact superpose eq18 eq20 | exact mod_symm (superpose eq18 eq20) | exact superpose eq20 eq18 | exact mod_symm (superpose eq20 eq18)
  have eq98 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (v (((e X1) ◇ (e X1)) ◇ (e (X0 ◇ X1)))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq99 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (((v X1) ◇ (v X1)) ◇ (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq20 | exact mod_symm (superpose eq15 eq20) | exact superpose eq20 eq15 | exact mod_symm (superpose eq20 eq15)
  have eq103 (X0 X1 : G) : (w X0 X1) = (e (w X0 X1)) := by first | exact superpose eq20 eq16 | exact mod_symm (superpose eq20 eq16) | exact superpose eq16 eq20 | exact mod_symm (superpose eq16 eq20)
  have eq104 (X0 X1 : G) : (e (v (v (v ((X0 ◇ X0) ◇ (X1 ◇ X0)))))) = (v (w X0 X1)) := by first | exact superpose eq20 eq17 | exact mod_symm (superpose eq20 eq17) | exact superpose eq17 eq20 | exact mod_symm (superpose eq17 eq20)
  have eq106 (X0 X1 : G) : (w X0 X1) = (v ((w X0 X1) ◇ (w X0 X1))) := by first | exact superpose eq20 eq19 | exact mod_symm (superpose eq20 eq19) | exact superpose eq19 eq20 | exact mod_symm (superpose eq19 eq20)
  have eq110 (X0 X1 : G) : (v (w X0 X1)) = (e (v (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by first | exact superpose eq85 eq104 | exact mod_symm (superpose eq85 eq104) | exact superpose eq104 eq85 | exact mod_symm (superpose eq104 eq85)
  have eq114 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v ((v (X1 ◇ X1)) ◇ (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq99 | exact mod_symm (superpose eq15 eq99) | exact superpose eq99 eq15 | exact mod_symm (superpose eq99 eq15)
  have eq115 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (v ((e (X1 ◇ X1)) ◇ (e (X0 ◇ X1)))))) := by first | exact superpose eq14 eq98 | exact mod_symm (superpose eq14 eq98) | exact superpose eq98 eq14 | exact mod_symm (superpose eq98 eq14)
  have eq117 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e X0) ◇ (X1 ◇ (e (v X0))))))) := by first | exact superpose eq17 eq95 | exact mod_symm (superpose eq17 eq95) | exact superpose eq95 eq17 | exact mod_symm (superpose eq95 eq17)
  have eq118 (X0 X1 : G) : (w (v X0) X1) = (e (v (v ((v X0) ◇ (X1 ◇ (v (X0 ◇ X0))))))) := by first | exact superpose eq85 eq94 | exact mod_symm (superpose eq85 eq94) | exact superpose eq94 eq85 | exact mod_symm (superpose eq94 eq85)
  have eq119 (X0 X1 : G) : (w (e X0) X1) = (e (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq37 eq93 | exact mod_symm (superpose eq37 eq93) | exact superpose eq93 eq37 | exact mod_symm (superpose eq93 eq37)
  have eq122 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (v ((X1 ◇ X1) ◇ (X0 ◇ X1)))))) := by first | exact superpose eq15 eq114 | exact mod_symm (superpose eq15 eq114) | exact superpose eq114 eq15 | exact mod_symm (superpose eq114 eq15)
  have eq123 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (v (e (X0 ◇ X1)))))) := by first | exact superpose eq37 eq115 | exact mod_symm (superpose eq37 eq115) | exact superpose eq115 eq37 | exact mod_symm (superpose eq115 eq37)
  have eq125 (X0 X1 : G) : (w (v X1) (v X0)) = (e (v (v (v (X1 ◇ (X0 ◇ (X1 ◇ X1))))))) := by first | exact superpose eq85 eq122 | exact mod_symm (superpose eq85 eq122) | exact superpose eq122 eq85 | exact mod_symm (superpose eq122 eq85)
  have eq126 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (e (v (X0 ◇ X1)))))) := by first | exact superpose eq17 eq123 | exact mod_symm (superpose eq17 eq123) | exact superpose eq123 eq17 | exact mod_symm (superpose eq123 eq17)
  have eq127 (X0 X1 : G) : (w (v X1) (v X0)) = (v (w X1 X0)) := by first | exact superpose eq110 eq125 | exact mod_symm (superpose eq110 eq125) | exact superpose eq125 eq110 | exact mod_symm (superpose eq125 eq110)
  have eq128 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (v (X0 ◇ X1))))) := by first | exact superpose eq67 eq126 | exact mod_symm (superpose eq67 eq126) | exact superpose eq126 eq67 | exact mod_symm (superpose eq126 eq67)
  have eq147 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq31 eq17 | exact mod_symm (superpose eq31 eq17) | exact superpose eq17 eq31 | exact mod_symm (superpose eq17 eq31)
  have eq152 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq17 eq147 | exact mod_symm (superpose eq17 eq147) | exact superpose eq147 eq17 | exact mod_symm (superpose eq147 eq17)
  have eq193 (X0 X1 : G) : (v (w (e X0) X1)) = (w (e (v X0)) (v X1)) := by first | exact superpose eq17 eq127 | exact mod_symm (superpose eq17 eq127) | exact superpose eq127 eq17 | exact mod_symm (superpose eq127 eq17)
  have eq203 (X0 : G) : (w X0 X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq39 eq20 | exact mod_symm (superpose eq39 eq20) | exact superpose eq20 eq39 | exact mod_symm (superpose eq20 eq39)
  have eq217 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq29 eq203 | exact mod_symm (superpose eq29 eq203) | exact superpose eq203 eq29 | exact mod_symm (superpose eq203 eq29)
  have eq233 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X2 := by first | exact superpose eq78 eq77 | exact mod_symm (superpose eq78 eq77) | exact superpose eq77 eq78 | exact mod_symm (superpose eq77 eq78)
  have eq238 (X0 X1 : G) : (e (v (v X0))) = (w (X1 ◇ X0) X1) := by first | exact superpose eq77 eq20 | exact mod_symm (superpose eq77 eq20) | exact superpose eq20 eq77 | exact mod_symm (superpose eq20 eq77)
  have eq258 : (w x y) ≠ (w y (w (e x) x)) := by first | exact superpose eq217 eq21 | exact mod_symm (superpose eq217 eq21) | exact superpose eq21 eq217 | exact mod_symm (superpose eq21 eq217)
  have eq364 (X0 X1 X2 : G) : (e (v (v (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) = (w X0 X2) := by first | exact superpose eq13 eq238 | exact mod_symm (superpose eq13 eq238) | exact superpose eq238 eq13 | exact mod_symm (superpose eq238 eq13)
  have eq609 (X0 X1 X2 : G) : (X2 ◇ (v (X0 ◇ X1))) = ((v X1) ◇ ((v X0) ◇ X2)) := by first | exact superpose eq15 eq85 | exact mod_symm (superpose eq15 eq85) | exact superpose eq85 eq15 | exact mod_symm (superpose eq85 eq15)
  have eq1772 (X0 X1 : G) : (w (e X1) (X0 ◇ (e X1))) = (e (v ((e X1) ◇ (v X0)))) := by first | exact superpose eq78 eq119 | exact mod_symm (superpose eq78 eq119) | exact superpose eq119 eq78 | exact mod_symm (superpose eq119 eq78)
  have eq1774 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v ((e X1) ◇ (v (e (X0 ◇ X1)))))) := by first | exact superpose eq14 eq119 | exact mod_symm (superpose eq14 eq119) | exact superpose eq119 eq14 | exact mod_symm (superpose eq119 eq14)
  have eq1775 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v ((e (v X1)) ◇ (v (v (X0 ◇ (e X1))))))) := by first | exact superpose eq34 eq119 | exact mod_symm (superpose eq34 eq119) | exact superpose eq119 eq34 | exact mod_symm (superpose eq119 eq34)
  have eq1810 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v ((v X1) ◇ (v (v (X0 ◇ (e X1))))))) := by first | exact superpose eq152 eq1775 | exact mod_symm (superpose eq152 eq1775) | exact superpose eq1775 eq152 | exact mod_symm (superpose eq1775 eq152)
  have eq1811 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (X1 ◇ (v (e (X0 ◇ X1)))))) := by first | exact superpose eq152 eq1774 | exact mod_symm (superpose eq152 eq1774) | exact superpose eq1774 eq152 | exact mod_symm (superpose eq1774 eq152)
  have eq1813 (X0 X1 : G) : (w (e X1) (X0 ◇ (e X1))) = (e (v (X1 ◇ (v X0)))) := by first | exact superpose eq152 eq1772 | exact mod_symm (superpose eq152 eq1772) | exact superpose eq1772 eq152 | exact mod_symm (superpose eq1772 eq152)
  have eq1819 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq15 eq1810 | exact mod_symm (superpose eq15 eq1810) | exact superpose eq1810 eq15 | exact mod_symm (superpose eq1810 eq15)
  have eq1820 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (X1 ◇ (e (v (X0 ◇ X1)))))) := by first | exact superpose eq17 eq1811 | exact mod_symm (superpose eq17 eq1811) | exact superpose eq1811 eq17 | exact mod_symm (superpose eq1811 eq17)
  have eq1824 (X0 X1 : G) : (v (w (e X1) X0)) = (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq193 eq1819 | exact mod_symm (superpose eq193 eq1819) | exact superpose eq1819 eq193 | exact mod_symm (superpose eq1819 eq193)
  have eq1825 (X0 X1 : G) : (w (e X1) (e X0)) = (e (v (X1 ◇ (v (X0 ◇ X1))))) := by first | exact superpose eq67 eq1820 | exact mod_symm (superpose eq67 eq1820) | exact superpose eq1820 eq67 | exact mod_symm (superpose eq1820 eq67)
  have eq1864 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (e (v ((e (v X0)) ◇ (v (X1 ◇ (X0 ◇ (v X0))))))) := by first | exact superpose eq92 eq128 | exact mod_symm (superpose eq92 eq128) | exact superpose eq128 eq92 | exact mod_symm (superpose eq128 eq92)
  have eq1891 (X0 X1 : G) : (w (e (v X1)) (e (v X0))) = (e (v ((e (v X1)) ◇ (v (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq128 | exact mod_symm (superpose eq15 eq128) | exact superpose eq128 eq15 | exact mod_symm (superpose eq128 eq15)
  have eq1893 (X0 X1 : G) : (w (e (e (v X1))) (e (v X0))) = (e (v ((e (e (v X1))) ◇ (v (v (X0 ◇ (e X1))))))) := by first | exact superpose eq34 eq128 | exact mod_symm (superpose eq34 eq128) | exact superpose eq128 eq34 | exact mod_symm (superpose eq128 eq34)
  have eq1903 (X0 X1 X2 : G) : (v ((e ((e X0) ◇ (v (X1 ◇ X0)))) ◇ X2)) = ((w (e X0) (e X1)) ◇ (v X2)) := by first | exact superpose eq128 eq32 | exact mod_symm (superpose eq128 eq32) | exact superpose eq32 eq128 | exact mod_symm (superpose eq32 eq128)
  have eq1923 (X0 X1 X2 : G) : ((w (e X0) (e X1)) ◇ (v X2)) = (v ((e (X0 ◇ (v (X1 ◇ X0)))) ◇ X2)) := by first | exact superpose eq31 eq1903 | exact mod_symm (superpose eq31 eq1903) | exact superpose eq1903 eq31 | exact mod_symm (superpose eq1903 eq31)
  have eq1932 (X0 X1 : G) : (e (v ((e (v X1)) ◇ (v (v (X0 ◇ (e X1))))))) = (w (e (e (v X1))) (e (v X0))) := by first | exact superpose eq152 eq1893 | exact mod_symm (superpose eq152 eq1893) | exact superpose eq1893 eq152 | exact mod_symm (superpose eq1893 eq152)
  have eq1934 (X0 X1 : G) : (w (e (v X1)) (e (v X0))) = (e (v ((v X1) ◇ (v (v (X0 ◇ X1)))))) := by first | exact superpose eq152 eq1891 | exact mod_symm (superpose eq152 eq1891) | exact superpose eq1891 eq152 | exact mod_symm (superpose eq1891 eq152)
  have eq1959 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (e (v ((v X0) ◇ (v (X1 ◇ (X0 ◇ (v X0))))))) := by first | exact superpose eq152 eq1864 | exact mod_symm (superpose eq152 eq1864) | exact superpose eq1864 eq152 | exact mod_symm (superpose eq1864 eq152)
  have eq1966 (X0 X1 : G) : (e (v ((e (v X1)) ◇ (v (v (X0 ◇ (e X1))))))) = (w (e (v X1)) (e (v X0))) := by first | exact superpose eq16 eq1932 | exact mod_symm (superpose eq16 eq1932) | exact superpose eq1932 eq16 | exact mod_symm (superpose eq1932 eq16)
  have eq1968 (X0 X1 : G) : (w (e (v X1)) (e (v X0))) = (e (v (v (X1 ◇ (v (X0 ◇ X1)))))) := by first | exact superpose eq15 eq1934 | exact mod_symm (superpose eq15 eq1934) | exact superpose eq1934 eq15 | exact mod_symm (superpose eq1934 eq15)
  have eq1977 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ (v X0))))))) := by first | exact superpose eq15 eq1959 | exact mod_symm (superpose eq15 eq1959) | exact superpose eq1959 eq15 | exact mod_symm (superpose eq1959 eq15)
  have eq1982 (X0 X1 : G) : (e (v ((v X1) ◇ (v (v (X0 ◇ (e X1))))))) = (w (e (v X1)) (e (v X0))) := by first | exact superpose eq152 eq1966 | exact mod_symm (superpose eq152 eq1966) | exact superpose eq1966 eq152 | exact mod_symm (superpose eq1966 eq152)
  have eq1989 (X0 X1 : G) : (w (e (v X0)) (e X1)) = (w X1 (v X0)) := by first | exact superpose eq364 eq1977 | exact mod_symm (superpose eq364 eq1977) | exact superpose eq1977 eq364 | exact mod_symm (superpose eq1977 eq364)
  have eq1993 (X0 X1 : G) : (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) = (w (e (v X1)) (e (v X0))) := by first | exact superpose eq15 eq1982 | exact mod_symm (superpose eq15 eq1982) | exact superpose eq1982 eq15 | exact mod_symm (superpose eq1982 eq15)
  have eq2000 (X0 X1 : G) : (w (v X0) (v X1)) = (e (v (v (X1 ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq1989 eq1993 | exact mod_symm (superpose eq1989 eq1993) | exact superpose eq1993 eq1989 | exact mod_symm (superpose eq1993 eq1989)
  have eq2005 (X0 X1 : G) : (w (v X0) (v X1)) = (v (w (e X1) X0)) := by first | exact superpose eq1824 eq2000 | exact mod_symm (superpose eq1824 eq2000) | exact superpose eq2000 eq1824 | exact mod_symm (superpose eq2000 eq1824)
  have eq2007 (X0 X1 : G) : (v (w X0 X1)) = (v (w (e X1) X0)) := by first | exact superpose eq127 eq2005 | exact mod_symm (superpose eq127 eq2005) | exact superpose eq2005 eq127 | exact mod_symm (superpose eq2005 eq127)
  have eq2010 (X0 X1 X2 : G) : (v (w (e (X0 ◇ X1)) X2)) = (v (w X2 ((e X0) ◇ X1))) := by first | exact superpose eq31 eq2007 | exact mod_symm (superpose eq31 eq2007) | exact superpose eq2007 eq31 | exact mod_symm (superpose eq2007 eq31)
  have eq2011 (X0 X1 : G) : (v (w (e X0) X1)) = (v (w X1 (e X0))) := by first | exact superpose eq16 eq2007 | exact mod_symm (superpose eq16 eq2007) | exact superpose eq2007 eq16 | exact mod_symm (superpose eq2007 eq16)
  have eq2026 (X0 X1 X2 : G) : ((v (w X0 X1)) ◇ (v X2)) = (v ((w (e X1) X0) ◇ X2)) := by first | exact superpose eq2007 eq15 | exact mod_symm (superpose eq2007 eq15) | exact superpose eq15 eq2007 | exact mod_symm (superpose eq15 eq2007)
  have eq2027 (X0 X1 X2 : G) : ((v X2) ◇ (v (w X0 X1))) = (v (X2 ◇ (w (e X1) X0))) := by first | exact superpose eq2007 eq15 | exact mod_symm (superpose eq2007 eq15) | exact superpose eq15 eq2007 | exact mod_symm (superpose eq15 eq2007)
  have eq2053 (X0 X1 X2 : G) : (v (X2 ◇ (w X0 X1))) = (v (X2 ◇ (w (e X1) X0))) := by first | exact superpose eq15 eq2027 | exact mod_symm (superpose eq15 eq2027) | exact superpose eq2027 eq15 | exact mod_symm (superpose eq2027 eq15)
  have eq2054 (X0 X1 X2 : G) : (v ((w X0 X1) ◇ X2)) = (v ((w (e X1) X0) ◇ X2)) := by first | exact superpose eq15 eq2026 | exact mod_symm (superpose eq15 eq2026) | exact superpose eq2026 eq15 | exact mod_symm (superpose eq2026 eq15)
  have eq2064 (X0 X1 : G) : (v (w X1 X0)) = (v (w X1 (e X0))) := by first | exact superpose eq2007 eq2011 | exact mod_symm (superpose eq2007 eq2011) | exact superpose eq2011 eq2007 | exact mod_symm (superpose eq2011 eq2007)
  have eq2065 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ X1))) = (v (w X2 (X0 ◇ X1))) := by first | exact superpose eq2007 eq2010 | exact mod_symm (superpose eq2007 eq2010) | exact superpose eq2010 eq2007 | exact mod_symm (superpose eq2010 eq2007)
  have eq2104 (X0 X1 X2 : G) : ((v (w X0 X1)) ◇ ((v (w X0 X1)) ◇ (X2 ◇ (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))))) = X2 := by first | exact superpose eq110 eq79 | exact mod_symm (superpose eq110 eq79) | exact superpose eq79 eq110 | exact mod_symm (superpose eq79 eq110)
  have eq2133 (X0 X1 X2 : G) : ((X2 ◇ (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) ◇ (v ((w X0 X1) ◇ (w X0 X1)))) = X2 := by first | exact superpose eq609 eq2104 | exact mod_symm (superpose eq609 eq2104) | exact superpose eq2104 eq609 | exact mod_symm (superpose eq2104 eq609)
  have eq2152 (X0 X1 X2 : G) : ((X2 ◇ (e (v (v (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) ◇ (w X0 X1)) = X2 := by first | exact superpose eq106 eq2133 | exact mod_symm (superpose eq106 eq2133) | exact superpose eq2133 eq106 | exact mod_symm (superpose eq2133 eq106)
  have eq2162 (X0 X1 X2 : G) : ((X2 ◇ (w X1 X0)) ◇ (w X0 X1)) = X2 := by first | exact superpose eq364 eq2152 | exact mod_symm (superpose eq364 eq2152) | exact superpose eq2152 eq364 | exact mod_symm (superpose eq2152 eq364)
  have eq2194 (X0 X1 : G) : (v (w (e X0) X1)) = (v (w (e X1) X0)) := by first | exact superpose eq2064 eq2007 | exact mod_symm (superpose eq2064 eq2007) | exact superpose eq2007 eq2064 | exact mod_symm (superpose eq2007 eq2064)
  have eq2195 (X0 X1 X2 : G) : ((v (w X0 X1)) ◇ (v X2)) = (v ((w X0 (e X1)) ◇ X2)) := by first | exact superpose eq2064 eq15 | exact mod_symm (superpose eq2064 eq15) | exact superpose eq15 eq2064 | exact mod_symm (superpose eq15 eq2064)
  have eq2223 (X0 X1 X2 : G) : (v ((w X0 X1) ◇ X2)) = (v ((w X0 (e X1)) ◇ X2)) := by first | exact superpose eq15 eq2195 | exact mod_symm (superpose eq15 eq2195) | exact superpose eq2195 eq15 | exact mod_symm (superpose eq2195 eq15)
  have eq2224 (X0 X1 : G) : (v (w X0 X1)) = (v (w (e X0) X1)) := by first | exact superpose eq2007 eq2194 | exact mod_symm (superpose eq2007 eq2194) | exact superpose eq2194 eq2007 | exact mod_symm (superpose eq2194 eq2007)
  have eq2288 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v (v ((e ((e X0) ◇ (v (X1 ◇ (e X0))))) ◇ (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq119 eq117 | exact mod_symm (superpose eq119 eq117) | exact superpose eq117 eq119 | exact mod_symm (superpose eq117 eq119)
  have eq2291 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e (v (X0 ◇ X0))) ◇ (X1 ◇ (e (v X0))))))) := by first | exact superpose eq39 eq117 | exact mod_symm (superpose eq39 eq117) | exact superpose eq117 eq39 | exact mod_symm (superpose eq117 eq39)
  have eq2295 (X0 X1 : G) : (w (e (v X1)) (X0 ◇ (e (v X1)))) = (e (v (v ((e X1) ◇ X0)))) := by first | exact superpose eq78 eq117 | exact mod_symm (superpose eq78 eq117) | exact superpose eq117 eq78 | exact mod_symm (superpose eq117 eq78)
  have eq2297 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (v ((e X1) ◇ (e (X0 ◇ (v X1))))))) := by first | exact superpose eq14 eq117 | exact mod_symm (superpose eq14 eq117) | exact superpose eq117 eq14 | exact mod_symm (superpose eq117 eq14)
  have eq2298 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v (v ((e X1) ◇ (v (X0 ◇ (e X1))))))) := by first | exact superpose eq34 eq117 | exact mod_symm (superpose eq34 eq117) | exact superpose eq117 eq34 | exact mod_symm (superpose eq117 eq34)
  have eq2334 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (w (e (v (e X1))) (e (v X0))) := by first | exact superpose eq1968 eq2298 | exact mod_symm (superpose eq1968 eq2298) | exact superpose eq2298 eq1968 | exact mod_symm (superpose eq2298 eq1968)
  have eq2335 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (v (e (X1 ◇ (X0 ◇ (v X1))))))) := by first | exact superpose eq14 eq2297 | exact mod_symm (superpose eq14 eq2297) | exact superpose eq2297 eq14 | exact mod_symm (superpose eq2297 eq14)
  have eq2337 (X0 X1 : G) : (e (v (v ((e X1) ◇ X0)))) = (e (v ((v X1) ◇ (v X0)))) := by first | exact superpose eq1813 eq2295 | exact mod_symm (superpose eq1813 eq2295) | exact superpose eq2295 eq1813 | exact mod_symm (superpose eq2295 eq1813)
  have eq2341 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e (v X0)) ◇ (X1 ◇ (e (v (X0 ◇ X0)))))))) := by first | exact superpose eq85 eq2291 | exact mod_symm (superpose eq85 eq2291) | exact superpose eq2291 eq85 | exact mod_symm (superpose eq2291 eq85)
  have eq2344 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w (e (e X0)) (e X1)) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq1923 eq2288 | exact mod_symm (superpose eq1923 eq2288) | exact superpose eq2288 eq1923 | exact mod_symm (superpose eq2288 eq1923)
  have eq2374 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (w (v X0) (v (e X1))) := by first | exact superpose eq1989 eq2334 | exact mod_symm (superpose eq1989 eq2334) | exact superpose eq2334 eq1989 | exact mod_symm (superpose eq2334 eq1989)
  have eq2375 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (e (v (X1 ◇ (X0 ◇ (v X1))))))) := by first | exact superpose eq17 eq2335 | exact mod_symm (superpose eq17 eq2335) | exact superpose eq2335 eq17 | exact mod_symm (superpose eq2335 eq17)
  have eq2377 (X0 X1 : G) : (e (v (v (X1 ◇ X0)))) = (e (v (v ((e X1) ◇ X0)))) := by first | exact superpose eq15 eq2337 | exact mod_symm (superpose eq15 eq2337) | exact superpose eq2337 eq15 | exact mod_symm (superpose eq2337 eq15)
  have eq2381 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e (v X0)) ◇ (X1 ◇ (e X0)))))) := by first | exact superpose eq29 eq2341 | exact mod_symm (superpose eq29 eq2341) | exact superpose eq2341 eq29 | exact mod_symm (superpose eq2341 eq29)
  have eq2384 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w (e (e X0)) X1) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq2223 eq2344 | exact mod_symm (superpose eq2223 eq2344) | exact superpose eq2344 eq2223 | exact mod_symm (superpose eq2344 eq2223)
  have eq2399 (X0 X1 : G) : (v (w X0 (e X1))) = (w (e (v X1)) (v X0)) := by first | exact superpose eq127 eq2374 | exact mod_symm (superpose eq127 eq2374) | exact superpose eq2374 eq127 | exact mod_symm (superpose eq2374 eq127)
  have eq2400 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (e (v (v (X1 ◇ (X0 ◇ (v X1))))))) := by first | exact superpose eq17 eq2375 | exact mod_symm (superpose eq17 eq2375) | exact superpose eq2375 eq17 | exact mod_symm (superpose eq2375 eq17)
  have eq2404 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((v X0) ◇ (X1 ◇ (e X0)))))) := by first | exact superpose eq2377 eq2381 | exact mod_symm (superpose eq2377 eq2381) | exact superpose eq2381 eq2377 | exact mod_symm (superpose eq2381 eq2377)
  have eq2406 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w X1 (e X0)) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq2054 eq2384 | exact mod_symm (superpose eq2054 eq2384) | exact superpose eq2384 eq2054 | exact mod_symm (superpose eq2384 eq2054)
  have eq2416 (X0 X1 : G) : (v (w X0 X1)) = (w (e (v X1)) (v X0)) := by first | exact superpose eq2064 eq2399 | exact mod_symm (superpose eq2064 eq2399) | exact superpose eq2399 eq2064 | exact mod_symm (superpose eq2399 eq2064)
  have eq2417 (X0 X1 : G) : (w (e (v X1)) (e X0)) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq16 eq2400 | exact mod_symm (superpose eq16 eq2400) | exact superpose eq2400 eq16 | exact mod_symm (superpose eq2400 eq16)
  have eq2418 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v ((e X0) ◇ (X1 ◇ (v X0)))))) := by first | exact superpose eq85 eq2404 | exact mod_symm (superpose eq85 eq2404) | exact superpose eq2404 eq85 | exact mod_symm (superpose eq2404 eq85)
  have eq2420 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w X1 X0) ◇ (v (X2 ◇ (w (e X0) X1)))))) := by first | exact superpose eq2223 eq2406 | exact mod_symm (superpose eq2223 eq2406) | exact superpose eq2406 eq2223 | exact mod_symm (superpose eq2406 eq2223)
  have eq2429 (X0 X1 : G) : (w X0 (v X1)) = (e (v (v (X1 ◇ (X0 ◇ (v X1)))))) := by first | exact superpose eq1989 eq2417 | exact mod_symm (superpose eq1989 eq2417) | exact superpose eq2417 eq1989 | exact mod_symm (superpose eq2417 eq1989)
  have eq2430 (X0 X1 : G) : (w (e (v X0)) X1) = (e (v (v (X0 ◇ (X1 ◇ (v X0)))))) := by first | exact superpose eq2377 eq2418 | exact mod_symm (superpose eq2377 eq2418) | exact superpose eq2418 eq2377 | exact mod_symm (superpose eq2418 eq2377)
  have eq2431 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (e (v ((w X1 X0) ◇ (v (X2 ◇ (w X1 X0)))))) := by first | exact superpose eq2053 eq2420 | exact mod_symm (superpose eq2053 eq2420) | exact superpose eq2420 eq2053 | exact mod_symm (superpose eq2420 eq2053)
  have eq2438 (X0 X1 : G) : (w (e (v X0)) X1) = (w X1 (v X0)) := by first | exact superpose eq2429 eq2430 | exact mod_symm (superpose eq2429 eq2430) | exact superpose eq2430 eq2429 | exact mod_symm (superpose eq2430 eq2429)
  have eq2439 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (w (e (w X1 X0)) (e X2)) := by first | exact superpose eq1825 eq2431 | exact mod_symm (superpose eq1825 eq2431) | exact superpose eq2431 eq1825 | exact mod_symm (superpose eq2431 eq1825)
  have eq2441 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (w (w X1 X0) (e X2)) := by first | exact superpose eq103 eq2439 | exact mod_symm (superpose eq103 eq2439) | exact superpose eq2439 eq103 | exact mod_symm (superpose eq2439 eq103)
  have eq2443 (X0 X1 : G) : (w X1 (e X0)) = (w (e (e X0)) X1) := by first | exact superpose eq19 eq2438 | exact mod_symm (superpose eq19 eq2438) | exact superpose eq2438 eq19 | exact mod_symm (superpose eq2438 eq19)
  have eq2453 (X0 X1 X2 : G) : (w (w (e X0) X1) X2) = (w X2 (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq119 eq2438 | exact mod_symm (superpose eq119 eq2438) | exact superpose eq2438 eq119 | exact mod_symm (superpose eq2438 eq119)
  have eq2480 (X0 X1 X2 : G) : (w X2 (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w X1 X0) (e X2)) := by first | exact superpose eq2441 eq2453 | exact mod_symm (superpose eq2441 eq2453) | exact superpose eq2453 eq2441 | exact mod_symm (superpose eq2453 eq2441)
  have eq2485 (X0 X1 : G) : (w (e X0) X1) = (w X1 (e X0)) := by first | exact superpose eq16 eq2443 | exact mod_symm (superpose eq16 eq2443) | exact superpose eq2443 eq16 | exact mod_symm (superpose eq2443 eq16)
  have eq2515 (X0 X1 : G) : (w (v (e (X0 ◇ X0))) X1) = (e (v (v ((v (e (X0 ◇ X0))) ◇ (X1 ◇ ((v (e (X0 ◇ X0))) ◇ (e X0))))))) := by first | exact superpose eq36 eq118 | exact mod_symm (superpose eq36 eq118) | exact superpose eq118 eq36 | exact mod_symm (superpose eq118 eq36)
  have eq2554 (X0 X1 : G) : (w X1 (e X0)) = (w (v (e (X0 ◇ X0))) X1) := by first | exact superpose eq364 eq2515 | exact mod_symm (superpose eq364 eq2515) | exact superpose eq2515 eq364 | exact mod_symm (superpose eq2515 eq364)
  have eq2572 (X0 X1 : G) : (w X1 (e X0)) = (w (e (v (X0 ◇ X0))) X1) := by first | exact superpose eq17 eq2554 | exact mod_symm (superpose eq17 eq2554) | exact superpose eq2554 eq17 | exact mod_symm (superpose eq2554 eq17)
  have eq2586 (X0 X1 : G) : (w X1 (e X0)) = (w X1 (v (X0 ◇ X0))) := by first | exact superpose eq2438 eq2572 | exact mod_symm (superpose eq2438 eq2572) | exact superpose eq2572 eq2438 | exact mod_symm (superpose eq2572 eq2438)
  have eq2638 (X0 X1 : G) : (w X0 (e (v X1))) = (w X0 (v X1)) := by first | exact superpose eq2485 eq2438 | exact mod_symm (superpose eq2485 eq2438) | exact superpose eq2438 eq2485 | exact mod_symm (superpose eq2438 eq2485)
  have eq2644 : (w x y) ≠ (w y (w x (e x))) := by first | exact superpose eq2485 eq258 | exact mod_symm (superpose eq2485 eq258) | exact superpose eq258 eq2485 | exact mod_symm (superpose eq258 eq2485)
  have eq2865 (X0 X1 X2 : G) : (w X2 X1) = (((w X1 X2) ◇ X0) ◇ X0) := by first | exact superpose eq2162 eq233 | exact mod_symm (superpose eq2162 eq233) | exact superpose eq233 eq2162 | exact mod_symm (superpose eq233 eq2162)
  have eq2866 (X1 X2 : G) : (w X1 X2) = (w X2 X1) := by first | exact superpose eq78 eq2865 | exact mod_symm (superpose eq78 eq2865) | exact superpose eq2865 eq78 | exact mod_symm (superpose eq2865 eq78)
  have eq2949 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w (e X0) X1) (v X2)) := by first | exact superpose eq119 eq2416 | exact mod_symm (superpose eq119 eq2416) | exact superpose eq2416 eq119 | exact mod_symm (superpose eq2416 eq119)
  have eq2958 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w (e (v X1)) (e X0)) := by first | exact superpose eq19 eq2416 | exact mod_symm (superpose eq19 eq2416) | exact superpose eq2416 eq19 | exact mod_symm (superpose eq2416 eq19)
  have eq2993 (X0 X1 : G) : (v (w ((e X0) ◇ (e X0)) X1)) = (w X0 (v X1)) := by first | exact superpose eq1989 eq2958 | exact mod_symm (superpose eq1989 eq2958) | exact superpose eq2958 eq1989 | exact mod_symm (superpose eq2958 eq1989)
  have eq3000 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w X1 X0) (e (v X2))) := by first | exact superpose eq2441 eq2949 | exact mod_symm (superpose eq2441 eq2949) | exact superpose eq2949 eq2441 | exact mod_symm (superpose eq2949 eq2441)
  have eq3011 (X0 X1 : G) : (v (w (e (X0 ◇ X0)) X1)) = (w X0 (v X1)) := by first | exact superpose eq14 eq2993 | exact mod_symm (superpose eq14 eq2993) | exact superpose eq2993 eq14 | exact mod_symm (superpose eq2993 eq14)
  have eq3015 (X0 X1 X2 : G) : (v (w X2 ((e X0) ◇ (v (X1 ◇ (e X0)))))) = (w (w X1 X0) (v X2)) := by first | exact superpose eq2638 eq3000 | exact mod_symm (superpose eq2638 eq3000) | exact superpose eq3000 eq2638 | exact mod_symm (superpose eq3000 eq2638)
  have eq3022 (X0 X1 : G) : (w X0 (v X1)) = (v (w X1 (X0 ◇ X0))) := by first | exact superpose eq2007 eq3011 | exact mod_symm (superpose eq2007 eq3011) | exact superpose eq3011 eq2007 | exact mod_symm (superpose eq3011 eq2007)
  have eq3024 (X0 X1 X2 : G) : (w (w X1 X0) (v X2)) = (v (w X2 (X0 ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq2065 eq3015 | exact mod_symm (superpose eq2065 eq3015) | exact superpose eq3015 eq2065 | exact mod_symm (superpose eq3015 eq2065)
  have eq3029 (X0 X1 X2 : G) : (v (w (e (X0 ◇ X1)) X2)) = (v (w ((e X0) ◇ X1) X2)) := by first | exact superpose eq31 eq2224 | exact mod_symm (superpose eq31 eq2224) | exact superpose eq2224 eq31 | exact mod_symm (superpose eq2224 eq31)
  have eq3111 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ X1))) = (v (w ((e X0) ◇ X1) X2)) := by first | exact superpose eq2007 eq3029 | exact mod_symm (superpose eq2007 eq3029) | exact superpose eq3029 eq2007 | exact mod_symm (superpose eq3029 eq2007)
  have eq3176 (X0 X1 : G) : (w (v X0) (e X1)) = (v (w X0 (X1 ◇ X1))) := by first | exact superpose eq2586 eq127 | exact mod_symm (superpose eq2586 eq127) | exact superpose eq127 eq2586 | exact mod_symm (superpose eq127 eq2586)
  have eq3200 (X0 X1 : G) : (w (v X0) (e X1)) = (w X1 (v X0)) := by first | exact superpose eq3022 eq3176 | exact mod_symm (superpose eq3022 eq3176) | exact superpose eq3176 eq3022 | exact mod_symm (superpose eq3176 eq3022)
  have eq3463 (X0 X1 : G) : (w (e X0) (e X1)) = (w X1 (e X0)) := by first | exact superpose eq19 eq3200 | exact mod_symm (superpose eq19 eq3200) | exact superpose eq3200 eq19 | exact mod_symm (superpose eq3200 eq19)
  have eq3482 (X0 X1 X2 : G) : (w (v ((e X0) ◇ (v (X1 ◇ (e X0))))) (v X2)) = (w (v X2) (w (e X0) X1)) := by first | exact superpose eq119 eq3200 | exact mod_symm (superpose eq119 eq3200) | exact superpose eq3200 eq119 | exact mod_symm (superpose eq3200 eq119)
  have eq3513 (X0 X1 X2 : G) : (w (v X2) (w (e X0) X1)) = (v (w ((e X0) ◇ (v (X1 ◇ (e X0)))) X2)) := by first | exact superpose eq127 eq3482 | exact mod_symm (superpose eq127 eq3482) | exact superpose eq3482 eq127 | exact mod_symm (superpose eq3482 eq127)
  have eq3527 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ (v (X1 ◇ (e X0)))))) = (w (v X2) (w (e X0) X1)) := by first | exact superpose eq3111 eq3513 | exact mod_symm (superpose eq3111 eq3513) | exact superpose eq3513 eq3111 | exact mod_symm (superpose eq3513 eq3111)
  have eq3535 (X0 X1 X2 : G) : (w (w X1 X0) (v X2)) = (w (v X2) (w (e X0) X1)) := by first | exact superpose eq3024 eq3527 | exact mod_symm (superpose eq3024 eq3527) | exact superpose eq3527 eq3024 | exact mod_symm (superpose eq3527 eq3024)
  have eq3895 (X0 : G) : (e (e X0)) = (w X0 (e X0)) := by first | exact superpose eq3463 eq217 | exact mod_symm (superpose eq3463 eq217) | exact superpose eq217 eq3463 | exact mod_symm (superpose eq217 eq3463)
  have eq3914 (X0 : G) : (e X0) = (w X0 (e X0)) := by first | exact superpose eq16 eq3895 | exact mod_symm (superpose eq16 eq3895) | exact superpose eq3895 eq16 | exact mod_symm (superpose eq3895 eq16)
  have eq4145 (X0 X1 : G) : (w (e X0) X1) = (w (v ((e X0) ◇ (v (X1 ◇ (e X0))))) (w (e X0) X1)) := by first | exact superpose eq119 eq3914 | exact mod_symm (superpose eq119 eq3914) | exact superpose eq3914 eq119 | exact mod_symm (superpose eq3914 eq119)
  have eq4161 : (w x y) ≠ (w y (e x)) := by first | exact superpose eq3914 eq2644 | exact mod_symm (superpose eq3914 eq2644) | exact superpose eq2644 eq3914 | exact mod_symm (superpose eq2644 eq3914)
  have eq4188 (X0 X1 : G) : (w (e X0) X1) = (w (w X1 X0) (v ((e X0) ◇ (v (X1 ◇ (e X0)))))) := by first | exact superpose eq3535 eq4145 | exact mod_symm (superpose eq3535 eq4145) | exact superpose eq4145 eq3535 | exact mod_symm (superpose eq4145 eq3535)
  have eq4215 (X0 X1 : G) : (w (e X0) X1) = (w (w X1 X0) (e (w X1 X0))) := by first | exact superpose eq2480 eq4188 | exact mod_symm (superpose eq2480 eq4188) | exact superpose eq4188 eq2480 | exact mod_symm (superpose eq4188 eq2480)
  have eq4239 (X0 X1 : G) : (w (e X0) X1) = (e (w X1 X0)) := by first | exact superpose eq3914 eq4215 | exact mod_symm (superpose eq3914 eq4215) | exact superpose eq4215 eq3914 | exact mod_symm (superpose eq4215 eq3914)
  have eq4261 (X0 X1 : G) : (w (e X0) X1) = (w X1 X0) := by first | exact superpose eq103 eq4239 | exact mod_symm (superpose eq103 eq4239) | exact superpose eq4239 eq103 | exact mod_symm (superpose eq4239 eq103)
  have eq4668 (X0 X1 : G) : (w X0 X1) = (w X0 (e X1)) := by first | exact superpose eq4261 eq2866 | exact mod_symm (superpose eq4261 eq2866) | exact superpose eq2866 eq4261 | exact mod_symm (superpose eq2866 eq4261)
  have eq4934 : (w x y) ≠ (w y x) := by first | exact superpose eq4668 eq4161 | exact mod_symm (superpose eq4668 eq4161) | exact superpose eq4161 eq4668 | exact mod_symm (superpose eq4161 eq4668)
  subsumption eq4934 eq2866


/-- Equation 3675 `x ◇ x = (y ◇ x) ◇ (x ◇ y)` is term-definable from equation 546 over finite magmas, via the term
`x □ y := u^[3N+1] ((x ◇ x) ◇ (y ◇ y))` where `u a = a ◇ a`. -/
private theorem aux546_3675 [Magma G] (h : Equation546 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, v (e a) ◇ v (e a) = e a) (hvue : ∀ a : G, v (e a ◇ e a) = e a)
    (hw : ∀ a b : G, w a b = (e (v (v ((a ◇ a) ◇ (b ◇ b))))))
    (x y : G) :
    (w x x) =
      (w (w y x) (w x y)) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ (v (e X0))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ (e X0))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (v ((X0 ◇ X0) ◇ (X1 ◇ X1))))) := mod_symm (hw ..)
  have eq21 : (w x x) ≠ (w (w y x) (w x y)) := mod_symm nh
  have eq26 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq27 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq28 (X0 : G) : (e X0) = (v (e (X0 ◇ X0))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq29 (X0 : G) : (e X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq17 eq28 | exact mod_symm (superpose eq17 eq28) | exact superpose eq28 eq17 | exact mod_symm (superpose eq28 eq17)
  have eq30 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq27 | exact mod_symm (superpose eq14 eq27) | exact superpose eq27 eq14 | exact mod_symm (superpose eq27 eq14)
  have eq31 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq33 (X0 X1 : G) : (v (((e X0) ◇ (e X0)) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq35 (X0 X1 : G) : (v (X1 ◇ ((e X0) ◇ (e X0)))) = ((v X1) ◇ (e X0)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq36 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X1 ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35) | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14)
  have eq37 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v ((e (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq33 | exact mod_symm (superpose eq14 eq33) | exact superpose eq33 eq14 | exact mod_symm (superpose eq33 eq14)
  have eq39 (X0 : G) : (e (v X0)) = (e (v (v (X0 ◇ X0)))) := by first | exact superpose eq15 eq29 | exact mod_symm (superpose eq15 eq29) | exact superpose eq29 eq15 | exact mod_symm (superpose eq29 eq15)
  have eq40 (X0 X1 : G) : ((e X1) ◇ (e X0)) = (e (X1 ◇ (v (X0 ◇ X0)))) := by first | exact superpose eq29 eq14 | exact mod_symm (superpose eq29 eq14) | exact superpose eq14 eq29 | exact mod_symm (superpose eq14 eq29)
  have eq41 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((v (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq29 eq14 | exact mod_symm (superpose eq29 eq14) | exact superpose eq14 eq29 | exact mod_symm (superpose eq14 eq29)
  have eq46 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((v (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq41 | exact mod_symm (superpose eq14 eq41) | exact superpose eq41 eq14 | exact mod_symm (superpose eq41 eq14)
  have eq47 (X0 X1 : G) : (e (X1 ◇ X0)) = (e (X1 ◇ (v (X0 ◇ X0)))) := by first | exact superpose eq14 eq40 | exact mod_symm (superpose eq14 eq40) | exact superpose eq40 eq14 | exact mod_symm (superpose eq40 eq14)
  have eq61 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = ((e (X0 ◇ X1)) ◇ (e X2)) := by first | exact superpose eq30 eq14 | exact mod_symm (superpose eq30 eq14) | exact superpose eq14 eq30 | exact mod_symm (superpose eq14 eq30)
  have eq64 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq30 eq17 | exact mod_symm (superpose eq30 eq17) | exact superpose eq17 eq30 | exact mod_symm (superpose eq17 eq30)
  have eq67 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq17 eq64 | exact mod_symm (superpose eq17 eq64) | exact superpose eq64 eq17 | exact mod_symm (superpose eq64 eq17)
  have eq69 (X0 X1 X2 : G) : (e ((X0 ◇ (e X1)) ◇ X2)) = (e ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq14 eq61 | exact mod_symm (superpose eq14 eq61) | exact superpose eq61 eq14 | exact mod_symm (superpose eq61 eq14)
  have eq73 (X0 X1 X2 : G) : ((e X1) ◇ ((e X0) ◇ (X2 ◇ (e (X0 ◇ X1))))) = X2 := by first | exact superpose eq14 eq13 | exact mod_symm (superpose eq14 eq13) | exact superpose eq13 eq14 | exact mod_symm (superpose eq13 eq14)
  have eq76 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0))) = X3 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq77 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X2 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq78 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq83 (X0 : G) : (v (e X0)) = ((e X0) ◇ (v (e X0))) := by first | exact superpose eq18 eq78 | exact mod_symm (superpose eq18 eq78) | exact superpose eq78 eq18 | exact mod_symm (superpose eq78 eq18)
  have eq85 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X1 ◇ (X2 ◇ X0)) := by first | exact superpose eq78 eq13 | exact mod_symm (superpose eq78 eq13) | exact superpose eq13 eq78 | exact mod_symm (superpose eq13 eq78)
  have eq89 (X0 : G) : (e (v X0)) = ((e X0) ◇ (e (v X0))) := by first | exact superpose eq17 eq83 | exact mod_symm (superpose eq17 eq83) | exact superpose eq83 eq17 | exact mod_symm (superpose eq83 eq17)
  have eq92 (X0 : G) : (e (v X0)) = (e (X0 ◇ (v X0))) := by first | exact superpose eq14 eq89 | exact mod_symm (superpose eq14 eq89) | exact superpose eq89 eq14 | exact mod_symm (superpose eq89 eq14)
  have eq93 (X0 X1 : G) : (w (e X0) X1) = (e (v (v ((e (X0 ◇ X0)) ◇ (X1 ◇ X1))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq95 (X0 X1 : G) : (w (v (e X0)) X1) = (e (v (v ((e X0) ◇ (X1 ◇ X1))))) := by first | exact superpose eq18 eq20 | exact mod_symm (superpose eq18 eq20) | exact superpose eq20 eq18 | exact mod_symm (superpose eq20 eq18)
  have eq96 (X0 X1 : G) : (w X1 (e X0)) = (e (v (v ((X1 ◇ X1) ◇ (e (X0 ◇ X0)))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq98 (X0 X1 : G) : (w X1 (v (e X0))) = (e (v (v ((X1 ◇ X1) ◇ (e X0))))) := by first | exact superpose eq18 eq20 | exact mod_symm (superpose eq18 eq20) | exact superpose eq20 eq18 | exact mod_symm (superpose eq20 eq18)
  have eq101 (X0 X1 X2 : G) : (e (X2 ◇ (v (v ((X0 ◇ X0) ◇ (X1 ◇ X1)))))) = ((e X2) ◇ (w X0 X1)) := by first | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14) | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20)
  have eq102 (X0 X1 : G) : (w X0 X1) = (e (w X0 X1)) := by first | exact superpose eq20 eq16 | exact mod_symm (superpose eq20 eq16) | exact superpose eq16 eq20 | exact mod_symm (superpose eq16 eq20)
  have eq103 (X0 X1 : G) : (e (v (v (v ((X0 ◇ X0) ◇ (X1 ◇ X1)))))) = (v (w X0 X1)) := by first | exact superpose eq20 eq17 | exact mod_symm (superpose eq20 eq17) | exact superpose eq17 eq20 | exact mod_symm (superpose eq17 eq20)
  have eq106 (X0 X1 X2 : G) : (e (X2 ◇ (v (v ((X0 ◇ X0) ◇ (X1 ◇ X1)))))) = (e (X2 ◇ (w X0 X1))) := by first | exact superpose eq20 eq30 | exact mod_symm (superpose eq20 eq30) | exact superpose eq30 eq20 | exact mod_symm (superpose eq30 eq20)
  have eq108 (X0 X1 X2 : G) : ((e X2) ◇ (w X0 X1)) = (e (X2 ◇ (w X0 X1))) := by first | exact superpose eq106 eq101 | exact mod_symm (superpose eq106 eq101) | exact superpose eq101 eq106 | exact mod_symm (superpose eq101 eq106)
  have eq110 (X0 X1 : G) : (e (v (v ((X1 ◇ X1) ◇ (e X0))))) = (w X1 (e (v X0))) := by first | exact superpose eq17 eq98 | exact mod_symm (superpose eq17 eq98) | exact superpose eq98 eq17 | exact mod_symm (superpose eq98 eq17)
  have eq111 (X0 X1 : G) : (w X1 (e X0)) = (e (v ((v (X1 ◇ X1)) ◇ (e X0)))) := by first | exact superpose eq36 eq96 | exact mod_symm (superpose eq36 eq96) | exact superpose eq96 eq36 | exact mod_symm (superpose eq96 eq36)
  have eq112 (X0 X1 : G) : (e (v (v ((e X0) ◇ (X1 ◇ X1))))) = (w (e (v X0)) X1) := by first | exact superpose eq17 eq95 | exact mod_symm (superpose eq17 eq95) | exact superpose eq95 eq17 | exact mod_symm (superpose eq95 eq17)
  have eq113 (X0 X1 : G) : (w (e X0) X1) = (e (v ((e X0) ◇ (v (X1 ◇ X1))))) := by first | exact superpose eq37 eq93 | exact mod_symm (superpose eq37 eq93) | exact superpose eq93 eq37 | exact mod_symm (superpose eq93 eq37)
  have eq114 (X0 X1 : G) : (w X1 (e X0)) = (e (v ((v (X1 ◇ X1)) ◇ X0))) := by first | exact superpose eq67 eq111 | exact mod_symm (superpose eq67 eq111) | exact superpose eq111 eq67 | exact mod_symm (superpose eq111 eq67)
  have eq115 (X0 X1 X2 : G) : ((w X0 X1) ◇ (e X2)) = (e ((w X0 X1) ◇ X2)) := by first | exact superpose eq102 eq14 | exact mod_symm (superpose eq102 eq14) | exact superpose eq14 eq102 | exact mod_symm (superpose eq14 eq102)
  have eq118 (X0 X1 : G) : (v (w X0 X1)) = (e (v (w X0 X1))) := by first | exact superpose eq102 eq17 | exact mod_symm (superpose eq102 eq17) | exact superpose eq17 eq102 | exact mod_symm (superpose eq17 eq102)
  have eq130 (X0 X1 X2 : G) : ((e (X0 ◇ X1)) ◇ (e X2)) = (e (((e X0) ◇ X1) ◇ X2)) := by first | exact superpose eq31 eq14 | exact mod_symm (superpose eq31 eq14) | exact superpose eq14 eq31 | exact mod_symm (superpose eq14 eq31)
  have eq133 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq31 eq17 | exact mod_symm (superpose eq31 eq17) | exact superpose eq17 eq31 | exact mod_symm (superpose eq17 eq31)
  have eq138 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq17 eq133 | exact mod_symm (superpose eq17 eq133) | exact superpose eq133 eq17 | exact mod_symm (superpose eq133 eq17)
  have eq140 (X0 X1 X2 : G) : (e ((X0 ◇ X1) ◇ X2)) = (e (((e X0) ◇ X1) ◇ X2)) := by first | exact superpose eq14 eq130 | exact mod_symm (superpose eq14 eq130) | exact superpose eq130 eq14 | exact mod_symm (superpose eq130 eq14)
  have eq159 (X0 X1 : G) : (e ((X0 ◇ (v X0)) ◇ X1)) = (e ((e (v X0)) ◇ X1)) := by first | exact superpose eq92 eq31 | exact mod_symm (superpose eq92 eq31) | exact superpose eq31 eq92 | exact mod_symm (superpose eq31 eq92)
  have eq160 (X0 X1 : G) : (e ((X0 ◇ (v X0)) ◇ X1)) = (e ((v X0) ◇ X1)) := by first | exact superpose eq31 eq159 | exact mod_symm (superpose eq31 eq159) | exact superpose eq159 eq31 | exact mod_symm (superpose eq159 eq31)
  have eq181 (X0 X1 X2 : G) : (e X1) = ((X2 ◇ (e (X0 ◇ X1))) ◇ ((e X0) ◇ X2)) := by first | exact superpose eq14 eq77 | exact mod_symm (superpose eq14 eq77) | exact superpose eq77 eq14 | exact mod_symm (superpose eq77 eq14)
  have eq187 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X2 := by first | exact superpose eq78 eq77 | exact mod_symm (superpose eq78 eq77) | exact superpose eq77 eq78 | exact mod_symm (superpose eq77 eq78)
  have eq191 (X0 X1 : G) : (((v (e X0)) ◇ ((v (e X0)) ◇ X1)) ◇ (e X0)) = X1 := by first | exact superpose eq18 eq77 | exact mod_symm (superpose eq18 eq77) | exact superpose eq77 eq18 | exact mod_symm (superpose eq77 eq18)
  have eq193 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X0))) = X3 := by first | exact superpose eq77 eq13 | exact mod_symm (superpose eq77 eq13) | exact superpose eq13 eq77 | exact mod_symm (superpose eq13 eq77)
  have eq194 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X0))))) = X3 := by first | exact superpose eq85 eq193 | exact mod_symm (superpose eq85 eq193) | exact superpose eq193 eq85 | exact mod_symm (superpose eq193 eq85)
  have eq195 (X0 X1 : G) : (((e (v X0)) ◇ ((e (v X0)) ◇ X1)) ◇ (e X0)) = X1 := by first | exact superpose eq17 eq191 | exact mod_symm (superpose eq17 eq191) | exact superpose eq191 eq17 | exact mod_symm (superpose eq191 eq17)
  have eq198 (X0 X1 X2 : G) : (e X1) = (X2 ◇ ((e X0) ◇ (X2 ◇ (e (X0 ◇ X1))))) := by first | exact superpose eq85 eq181 | exact mod_symm (superpose eq85 eq181) | exact superpose eq181 eq85 | exact mod_symm (superpose eq181 eq85)
  have eq247 (X0 : G) : (w X0 X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq39 eq20 | exact mod_symm (superpose eq39 eq20) | exact superpose eq20 eq39 | exact mod_symm (superpose eq20 eq39)
  have eq255 (X0 X1 : G) : (e (X1 ◇ (e (v X0)))) = (e (X1 ◇ (v (v (X0 ◇ X0))))) := by first | exact superpose eq39 eq30 | exact mod_symm (superpose eq39 eq30) | exact superpose eq30 eq39 | exact mod_symm (superpose eq30 eq39)
  have eq258 (X0 X1 : G) : (e (X1 ◇ (v X0))) = (e (X1 ◇ (v (v (X0 ◇ X0))))) := by first | exact superpose eq30 eq255 | exact mod_symm (superpose eq30 eq255) | exact superpose eq255 eq30 | exact mod_symm (superpose eq255 eq30)
  have eq263 (X0 : G) : (e X0) = (w X0 X0) := by first | exact superpose eq29 eq247 | exact mod_symm (superpose eq29 eq247) | exact superpose eq247 eq29 | exact mod_symm (superpose eq247 eq29)
  have eq575 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((v (e (X0 ◇ X0))) ◇ X1))) := by first | exact superpose eq14 eq114 | exact mod_symm (superpose eq14 eq114) | exact superpose eq114 eq14 | exact mod_symm (superpose eq114 eq14)
  have eq578 (X0 X1 : G) : (e (v ((e X0) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq19 eq114 | exact mod_symm (superpose eq19 eq114) | exact superpose eq114 eq19 | exact mod_symm (superpose eq114 eq19)
  have eq582 (X0 X1 : G) : (w X0 (e (v X1))) = (e (v (v ((X0 ◇ X0) ◇ X1)))) := by first | exact superpose eq15 eq114 | exact mod_symm (superpose eq15 eq114) | exact superpose eq114 eq15 | exact mod_symm (superpose eq114 eq15)
  have eq614 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq138 eq578 | exact mod_symm (superpose eq138 eq578) | exact superpose eq578 eq138 | exact mod_symm (superpose eq578 eq138)
  have eq616 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((e (v (X0 ◇ X0))) ◇ X1))) := by first | exact superpose eq17 eq575 | exact mod_symm (superpose eq17 eq575) | exact superpose eq575 eq17 | exact mod_symm (superpose eq575 eq17)
  have eq622 (X0 X1 : G) : (e (v ((v (X0 ◇ X0)) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq138 eq616 | exact mod_symm (superpose eq138 eq616) | exact superpose eq616 eq138 | exact mod_symm (superpose eq616 eq138)
  have eq626 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((v (X0 ◇ X0)) ◇ X1))) := by first | exact superpose eq614 eq622 | exact mod_symm (superpose eq614 eq622) | exact superpose eq622 eq614 | exact mod_symm (superpose eq622 eq614)
  have eq629 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (w X0 (e X1)) := by first | exact superpose eq114 eq626 | exact mod_symm (superpose eq114 eq626) | exact superpose eq626 eq114 | exact mod_symm (superpose eq626 eq114)
  have eq636 (X0 X1 : G) : (e (v X0)) = (w (X0 ◇ X1) (e X1)) := by first | exact superpose eq78 eq629 | exact mod_symm (superpose eq78 eq629) | exact superpose eq629 eq78 | exact mod_symm (superpose eq629 eq78)
  have eq657 (X0 X1 : G) : (v (w X0 (e X1))) = (e (v (v (X0 ◇ X1)))) := by first | exact superpose eq629 eq17 | exact mod_symm (superpose eq629 eq17) | exact superpose eq17 eq629 | exact mod_symm (superpose eq17 eq629)
  have eq735 (X0 X1 X2 X3 : G) : (((e X1) ◇ (X0 ◇ (e (X1 ◇ X2)))) ◇ ((e X2) ◇ (X3 ◇ X0))) = X3 := by first | exact superpose eq73 eq13 | exact mod_symm (superpose eq73 eq13) | exact superpose eq13 eq73 | exact mod_symm (superpose eq13 eq73)
  have eq1207 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq78 eq85 | exact mod_symm (superpose eq78 eq85) | exact superpose eq85 eq78 | exact mod_symm (superpose eq85 eq78)
  have eq1255 (X0 X1 X2 : G) : (w X2 (X1 ◇ X0)) = (e (v (v ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))))) := by first | exact superpose eq85 eq20 | exact mod_symm (superpose eq85 eq20) | exact superpose eq20 eq85 | exact mod_symm (superpose eq20 eq85)
  have eq1256 (X0 X1 : G) : (e (X1 ◇ X0)) = (e (v (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by first | exact superpose eq85 eq29 | exact mod_symm (superpose eq85 eq29) | exact superpose eq29 eq85 | exact mod_symm (superpose eq29 eq85)
  have eq1288 (X0 X1 : G) : (e (X1 ◇ X0)) = (w X0 (e (X1 ◇ (X1 ◇ X0)))) := by first | exact superpose eq629 eq1256 | exact mod_symm (superpose eq629 eq1256) | exact superpose eq1256 eq629 | exact mod_symm (superpose eq1256 eq629)
  have eq1289 (X0 X1 X2 : G) : (w X2 (X1 ◇ X0)) = (w X2 (e (v (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := by first | exact superpose eq582 eq1255 | exact mod_symm (superpose eq582 eq1255) | exact superpose eq1255 eq582 | exact mod_symm (superpose eq1255 eq582)
  have eq1317 (X0 X1 X2 : G) : (w X2 (X1 ◇ X0)) = (w X2 (w X0 (e (X1 ◇ (X1 ◇ X0))))) := by first | exact superpose eq629 eq1289 | exact mod_symm (superpose eq629 eq1289) | exact superpose eq1289 eq629 | exact mod_symm (superpose eq1289 eq629)
  have eq1328 (X0 X1 X2 : G) : (w X2 (e (X1 ◇ X0))) = (w X2 (X1 ◇ X0)) := by first | exact superpose eq1288 eq1317 | exact mod_symm (superpose eq1288 eq1317) | exact superpose eq1317 eq1288 | exact mod_symm (superpose eq1317 eq1288)
  have eq1360 (X0 X1 : G) : (w (e (X0 ◇ X0)) X1) = (e ((e X0) ◇ (v (v (X1 ◇ X1))))) := by first | exact superpose eq37 eq113 | exact mod_symm (superpose eq37 eq113) | exact superpose eq113 eq37 | exact mod_symm (superpose eq113 eq37)
  have eq1362 (X0 X1 : G) : (w (e X0) X1) = (w (e X0) (e (v (X1 ◇ X1)))) := by first | exact superpose eq113 eq629 | exact mod_symm (superpose eq113 eq629) | exact superpose eq629 eq113 | exact mod_symm (superpose eq629 eq113)
  have eq1393 (X0 X1 : G) : (w (e X0) X1) = (e (v (X0 ◇ (v (X1 ◇ X1))))) := by first | exact superpose eq614 eq1362 | exact mod_symm (superpose eq614 eq1362) | exact superpose eq1362 eq614 | exact mod_symm (superpose eq1362 eq614)
  have eq1395 (X0 X1 : G) : (e ((e X0) ◇ (v X1))) = (w (e (X0 ◇ X0)) X1) := by first | exact superpose eq258 eq1360 | exact mod_symm (superpose eq258 eq1360) | exact superpose eq1360 eq258 | exact mod_symm (superpose eq1360 eq258)
  have eq1418 (X0 X1 : G) : (w (e X0) X1) = (w X0 (e (v (X1 ◇ X1)))) := by first | exact superpose eq629 eq1393 | exact mod_symm (superpose eq629 eq1393) | exact superpose eq1393 eq629 | exact mod_symm (superpose eq1393 eq629)
  have eq1420 (X0 X1 : G) : (e (X0 ◇ (v X1))) = (w (e (X0 ◇ X0)) X1) := by first | exact superpose eq31 eq1395 | exact mod_symm (superpose eq31 eq1395) | exact superpose eq1395 eq31 | exact mod_symm (superpose eq1395 eq31)
  have eq1442 (X0 X1 : G) : (w (e X0) X1) = (w X0 (e X1)) := by first | exact superpose eq29 eq1418 | exact mod_symm (superpose eq29 eq1418) | exact superpose eq1418 eq29 | exact mod_symm (superpose eq1418 eq29)
  have eq1625 (X0 X1 : G) : (w (e X1) (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (e (v ((e X1) ◇ (v (X0 ◇ X0))))) := by first | exact superpose eq76 eq113 | exact mod_symm (superpose eq76 eq113) | exact superpose eq113 eq76 | exact mod_symm (superpose eq113 eq76)
  have eq1648 (X0 X1 : G) : (w (e X1) (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (w (e X1) (e (v (X0 ◇ X0)))) := by first | exact superpose eq629 eq1625 | exact mod_symm (superpose eq629 eq1625) | exact superpose eq1625 eq629 | exact mod_symm (superpose eq1625 eq629)
  have eq1705 (X0 X1 : G) : (w (e X1) (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (e (v (X1 ◇ (v (X0 ◇ X0))))) := by first | exact superpose eq614 eq1648 | exact mod_symm (superpose eq614 eq1648) | exact superpose eq1648 eq614 | exact mod_symm (superpose eq1648 eq614)
  have eq1733 (X0 X1 : G) : (w X1 (e (v (X0 ◇ X0)))) = (w (e X1) (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by first | exact superpose eq629 eq1705 | exact mod_symm (superpose eq629 eq1705) | exact superpose eq1705 eq629 | exact mod_symm (superpose eq1705 eq629)
  have eq1739 (X0 X1 : G) : (w X1 (e (v (X0 ◇ X0)))) = (w X1 (e (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := by first | exact superpose eq1442 eq1733 | exact mod_symm (superpose eq1442 eq1733) | exact superpose eq1733 eq1442 | exact mod_symm (superpose eq1733 eq1442)
  have eq1742 (X0 X1 : G) : (w X1 (e (v (X0 ◇ X0)))) = (w X1 (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by first | exact superpose eq1328 eq1739 | exact mod_symm (superpose eq1328 eq1739) | exact superpose eq1739 eq1328 | exact mod_symm (superpose eq1739 eq1328)
  have eq1743 (X0 X1 : G) : (w X1 (e (v (X0 ◇ X0)))) = (w X1 ((X0 ◇ X0) ◇ X0)) := by first | exact superpose eq1207 eq1742 | exact mod_symm (superpose eq1207 eq1742) | exact superpose eq1742 eq1207 | exact mod_symm (superpose eq1742 eq1207)
  have eq1744 (X0 X1 : G) : (w X1 X0) = (w X1 (e (v (X0 ◇ X0)))) := by first | exact superpose eq78 eq1743 | exact mod_symm (superpose eq78 eq1743) | exact superpose eq1743 eq78 | exact mod_symm (superpose eq1743 eq78)
  have eq1745 (X0 X1 : G) : (w X1 X0) = (w X1 (e X0)) := by first | exact superpose eq29 eq1744 | exact mod_symm (superpose eq29 eq1744) | exact superpose eq1744 eq29 | exact mod_symm (superpose eq1744 eq29)
  have eq1746 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w X2 (e (X0 ◇ X1))) := by first | exact superpose eq30 eq1745 | exact mod_symm (superpose eq30 eq1745) | exact superpose eq1745 eq30 | exact mod_symm (superpose eq1745 eq30)
  have eq1750 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ X1))) = (w X2 (w X0 (e X1))) := by first | exact superpose eq629 eq1745 | exact mod_symm (superpose eq629 eq1745) | exact superpose eq1745 eq629 | exact mod_symm (superpose eq1745 eq629)
  have eq1769 (X0 X1 : G) : (e (v X0)) = (w (X0 ◇ X1) X1) := by first | exact superpose eq1745 eq636 | exact mod_symm (superpose eq1745 eq636) | exact superpose eq636 eq1745 | exact mod_symm (superpose eq636 eq1745)
  have eq1782 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ X1))) = (w X2 (w X0 X1)) := by first | exact superpose eq1745 eq1750 | exact mod_symm (superpose eq1745 eq1750) | exact superpose eq1750 eq1745 | exact mod_symm (superpose eq1750 eq1745)
  have eq1786 (X0 X1 X2 : G) : (w X2 (X0 ◇ (e X1))) = (w X2 (X0 ◇ X1)) := by first | exact superpose eq1328 eq1746 | exact mod_symm (superpose eq1328 eq1746) | exact superpose eq1746 eq1328 | exact mod_symm (superpose eq1746 eq1328)
  have eq1831 (X0 X1 : G) : (e (v (v (v ((X0 ◇ X0) ◇ (e X1)))))) = (v (w X0 (e (v X1)))) := by first | exact superpose eq110 eq17 | exact mod_symm (superpose eq110 eq17) | exact superpose eq17 eq110 | exact mod_symm (superpose eq17 eq110)
  have eq1859 (X0 X1 : G) : (e (v (v (v ((X0 ◇ X0) ◇ (e X1)))))) = (v (w X0 (v X1))) := by first | exact superpose eq1745 eq1831 | exact mod_symm (superpose eq1745 eq1831) | exact superpose eq1831 eq1745 | exact mod_symm (superpose eq1831 eq1745)
  have eq1985 (X0 X1 X2 : G) : (e (v (X1 ◇ (X2 ◇ X0)))) = (w X0 (X2 ◇ X1)) := by first | exact superpose eq77 eq1769 | exact mod_symm (superpose eq77 eq1769) | exact superpose eq1769 eq77 | exact mod_symm (superpose eq1769 eq77)
  have eq2011 (X0 X1 X2 : G) : (w X1 (e (X2 ◇ X0))) = (w X0 (X2 ◇ X1)) := by first | exact superpose eq629 eq1985 | exact mod_symm (superpose eq629 eq1985) | exact superpose eq1985 eq629 | exact mod_symm (superpose eq1985 eq629)
  have eq2019 (X0 X1 X2 : G) : (w X0 (X2 ◇ X1)) = (w X1 (X2 ◇ X0)) := by first | exact superpose eq1745 eq2011 | exact mod_symm (superpose eq1745 eq2011) | exact superpose eq2011 eq1745 | exact mod_symm (superpose eq2011 eq1745)
  have eq2049 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v (v ((e X1) ◇ (v (X0 ◇ X0)))))) := by first | exact superpose eq15 eq112 | exact mod_symm (superpose eq15 eq112) | exact superpose eq112 eq15 | exact mod_symm (superpose eq112 eq15)
  have eq2102 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (v (w (e X1) (e (v (X0 ◇ X0))))) := by first | exact superpose eq657 eq2049 | exact mod_symm (superpose eq657 eq2049) | exact superpose eq2049 eq657 | exact mod_symm (superpose eq2049 eq657)
  have eq2145 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (v (e (v (X1 ◇ (v (X0 ◇ X0)))))) := by first | exact superpose eq614 eq2102 | exact mod_symm (superpose eq614 eq2102) | exact superpose eq2102 eq614 | exact mod_symm (superpose eq2102 eq614)
  have eq2179 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (e (v (v (X1 ◇ (v (X0 ◇ X0)))))) := by first | exact superpose eq17 eq2145 | exact mod_symm (superpose eq17 eq2145) | exact superpose eq2145 eq17 | exact mod_symm (superpose eq2145 eq17)
  have eq2209 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (v (w X1 (e (v (X0 ◇ X0))))) := by first | exact superpose eq657 eq2179 | exact mod_symm (superpose eq657 eq2179) | exact superpose eq2179 eq657 | exact mod_symm (superpose eq2179 eq657)
  have eq2237 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (v (w X1 (v (X0 ◇ X0)))) := by first | exact superpose eq1745 eq2209 | exact mod_symm (superpose eq1745 eq2209) | exact superpose eq2209 eq1745 | exact mod_symm (superpose eq2209 eq1745)
  have eq2259 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (v (w X1 (w X0 X0))) := by first | exact superpose eq1782 eq2237 | exact mod_symm (superpose eq1782 eq2237) | exact superpose eq2237 eq1782 | exact mod_symm (superpose eq2237 eq1782)
  have eq2281 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (v (w X1 (e X0))) := by first | exact superpose eq263 eq2259 | exact mod_symm (superpose eq263 eq2259) | exact superpose eq2259 eq263 | exact mod_symm (superpose eq2259 eq263)
  have eq2300 (X0 X1 : G) : (w (e (v X1)) (v X0)) = (v (w X1 X0)) := by first | exact superpose eq1745 eq2281 | exact mod_symm (superpose eq1745 eq2281) | exact superpose eq2281 eq1745 | exact mod_symm (superpose eq2281 eq1745)
  have eq2315 (X0 X1 : G) : (v (w X1 X0)) = (w (v X1) (e (v X0))) := by first | exact superpose eq1442 eq2300 | exact mod_symm (superpose eq1442 eq2300) | exact superpose eq2300 eq1442 | exact mod_symm (superpose eq2300 eq1442)
  have eq2325 (X0 X1 : G) : (v (w X1 X0)) = (w (v X1) (v X0)) := by first | exact superpose eq1745 eq2315 | exact mod_symm (superpose eq1745 eq2315) | exact superpose eq2315 eq1745 | exact mod_symm (superpose eq2315 eq1745)
  have eq3370 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ (e (X1 ◇ X1))))) = (w (v X2) ((v X0) ◇ (e X1))) := by first | exact superpose eq36 eq2325 | exact mod_symm (superpose eq36 eq2325) | exact superpose eq2325 eq36 | exact mod_symm (superpose eq2325 eq36)
  have eq3388 (X0 X1 X2 : G) : (v (w X2 (X0 ◇ (e (X1 ◇ X1))))) = (w (v X2) ((v X0) ◇ X1)) := by first | exact superpose eq1786 eq3370 | exact mod_symm (superpose eq1786 eq3370) | exact superpose eq3370 eq1786 | exact mod_symm (superpose eq3370 eq1786)
  have eq3397 (X0 X1 X2 : G) : (w (v X2) ((v X0) ◇ X1)) = (v (w X2 (X0 ◇ (X1 ◇ X1)))) := by first | exact superpose eq1786 eq3388 | exact mod_symm (superpose eq1786 eq3388) | exact superpose eq3388 eq1786 | exact mod_symm (superpose eq3388 eq1786)
  have eq3451 (X0 X1 X2 : G) : (e (v (X1 ◇ ((X2 ◇ X1) ◇ X0)))) = (w X0 X2) := by first | exact superpose eq187 eq1769 | exact mod_symm (superpose eq187 eq1769) | exact superpose eq1769 eq187 | exact mod_symm (superpose eq1769 eq187)
  have eq3478 (X0 X1 X2 : G) : (w X0 X2) = (w X1 (e ((X2 ◇ X1) ◇ X0))) := by first | exact superpose eq629 eq3451 | exact mod_symm (superpose eq629 eq3451) | exact superpose eq3451 eq629 | exact mod_symm (superpose eq3451 eq629)
  have eq3509 (X0 X1 X2 : G) : (w X0 X2) = (w X1 ((X2 ◇ X1) ◇ X0)) := by first | exact superpose eq1328 eq3478 | exact mod_symm (superpose eq1328 eq3478) | exact superpose eq3478 eq1328 | exact mod_symm (superpose eq3478 eq1328)
  have eq4018 (X0 X1 X2 : G) : (e (X2 ◇ (X1 ◇ X0))) = (e (X0 ◇ (X1 ◇ (v (X2 ◇ X2))))) := by first | exact superpose eq85 eq46 | exact mod_symm (superpose eq85 eq46) | exact superpose eq46 eq85 | exact mod_symm (superpose eq46 eq85)
  have eq4397 (X0 X1 X2 : G) : (e (X2 ◇ (e (X0 ◇ X1)))) = (e (X2 ◇ (X0 ◇ (v (X1 ◇ X1))))) := by first | exact superpose eq47 eq30 | exact mod_symm (superpose eq47 eq30) | exact superpose eq30 eq47 | exact mod_symm (superpose eq30 eq47)
  have eq4433 (X0 X1 X2 : G) : (e (X2 ◇ (e (X0 ◇ X1)))) = (e (X1 ◇ (X0 ◇ X2))) := by first | exact superpose eq4018 eq4397 | exact mod_symm (superpose eq4018 eq4397) | exact superpose eq4397 eq4018 | exact mod_symm (superpose eq4397 eq4018)
  have eq4468 (X0 X1 X2 : G) : (e (X2 ◇ (X0 ◇ X1))) = (e (X1 ◇ (X0 ◇ X2))) := by first | exact superpose eq30 eq4433 | exact mod_symm (superpose eq30 eq4433) | exact superpose eq4433 eq30 | exact mod_symm (superpose eq4433 eq30)
  have eq5899 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by first | exact superpose eq85 eq1207 | exact mod_symm (superpose eq85 eq1207) | exact superpose eq1207 eq85 | exact mod_symm (superpose eq1207 eq85)
  have eq9903 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ X1))) = (w (v X1) ((v X0) ◇ X2)) := by first | exact superpose eq15 eq2019 | exact mod_symm (superpose eq15 eq2019) | exact superpose eq2019 eq15 | exact mod_symm (superpose eq2019 eq15)
  have eq9985 (X0 X1 X2 : G) : (w X2 (w X0 X1)) = (w (v X1) ((v X0) ◇ X2)) := by first | exact superpose eq1782 eq9903 | exact mod_symm (superpose eq1782 eq9903) | exact superpose eq9903 eq1782 | exact mod_symm (superpose eq9903 eq1782)
  have eq11088 (X0 X1 X2 X3 : G) : (w (X1 ◇ X0) X2) = (w X3 (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by first | exact superpose eq85 eq3509 | exact mod_symm (superpose eq85 eq3509) | exact superpose eq3509 eq85 | exact mod_symm (superpose eq3509 eq85)
  have eq12562 (X0 X1 X2 : G) : (e X1) = (((e (v (X2 ◇ X1))) ◇ ((e (v (X2 ◇ X1))) ◇ X0)) ◇ ((e X2) ◇ X0)) := by first | exact superpose eq195 eq198 | exact mod_symm (superpose eq195 eq198) | exact superpose eq198 eq195 | exact mod_symm (superpose eq198 eq195)
  have eq12672 (X0 X1 X2 : G) : (e X1) = (X0 ◇ ((e X2) ◇ ((e (v (X2 ◇ X1))) ◇ ((e (v (X2 ◇ X1))) ◇ X0)))) := by first | exact superpose eq85 eq12562 | exact mod_symm (superpose eq85 eq12562) | exact superpose eq12562 eq85 | exact mod_symm (superpose eq12562 eq85)
  have eq12778 (X1 X2 : G) : (e X1) = (((e (v (X2 ◇ X1))) ◇ (e X2)) ◇ (e (v (X2 ◇ X1)))) := by first | exact superpose eq5899 eq12672 | exact mod_symm (superpose eq5899 eq12672) | exact superpose eq12672 eq5899 | exact mod_symm (superpose eq12672 eq5899)
  have eq12853 (X1 X2 : G) : (e X1) = (((w X2 (e X1)) ◇ (e X2)) ◇ (w X2 (e X1))) := by first | exact superpose eq629 eq12778 | exact mod_symm (superpose eq629 eq12778) | exact superpose eq12778 eq629 | exact mod_symm (superpose eq12778 eq629)
  have eq12912 (X1 X2 : G) : (e X1) = (((w X2 X1) ◇ (e X2)) ◇ (w X2 X1)) := by first | exact superpose eq1745 eq12853 | exact mod_symm (superpose eq1745 eq12853) | exact superpose eq12853 eq1745 | exact mod_symm (superpose eq12853 eq1745)
  have eq12945 (X1 X2 : G) : (e X1) = ((e ((w X2 X1) ◇ X2)) ◇ (w X2 X1)) := by first | exact superpose eq115 eq12912 | exact mod_symm (superpose eq115 eq12912) | exact superpose eq12912 eq115 | exact mod_symm (superpose eq12912 eq115)
  have eq12963 (X1 X2 : G) : (e X1) = (e (((w X2 X1) ◇ X2) ◇ (w X2 X1))) := by first | exact superpose eq108 eq12945 | exact mod_symm (superpose eq108 eq12945) | exact superpose eq12945 eq108 | exact mod_symm (superpose eq12945 eq108)
  have eq18016 (X0 X1 X2 : G) : (e (v (v X0))) = (w X1 (e (v (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))))) := by first | exact superpose eq194 eq582 | exact mod_symm (superpose eq194 eq582) | exact superpose eq582 eq194 | exact mod_symm (superpose eq582 eq194)
  have eq18095 (X0 X1 X2 : G) : (e (v (v X0))) = (w X1 (v (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := by first | exact superpose eq1745 eq18016 | exact mod_symm (superpose eq1745 eq18016) | exact superpose eq18016 eq1745 | exact mod_symm (superpose eq18016 eq1745)
  have eq18198 (X0 X1 X2 : G) : (e (v (v X0))) = (w X1 (w X2 (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by first | exact superpose eq1782 eq18095 | exact mod_symm (superpose eq1782 eq18095) | exact superpose eq18095 eq1782 | exact mod_symm (superpose eq18095 eq1782)
  have eq18257 (X0 X1 : G) : (e (v (v X0))) = (w X1 (w (X1 ◇ X0) X1)) := by first | exact superpose eq11088 eq18198 | exact mod_symm (superpose eq11088 eq18198) | exact superpose eq18198 eq11088 | exact mod_symm (superpose eq18198 eq11088)
  have eq52519 (X0 X1 X2 X3 : G) : (e ((e (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (e ((X2 ◇ (X1 ◇ X0)) ◇ X3)) := by first | exact superpose eq4468 eq31 | exact mod_symm (superpose eq4468 eq31) | exact superpose eq31 eq4468 | exact mod_symm (superpose eq31 eq4468)
  have eq52626 (X0 X1 X2 X3 : G) : (e ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (e ((X2 ◇ (X1 ◇ X0)) ◇ X3)) := by first | exact superpose eq31 eq52519 | exact mod_symm (superpose eq31 eq52519) | exact superpose eq52519 eq31 | exact mod_symm (superpose eq52519 eq31)
  have eq60113 (X0 X1 : G) : (e (w (X1 ◇ X0) X1)) = (e (((e (v (v X0))) ◇ X1) ◇ (e (v (v X0))))) := by first | exact superpose eq18257 eq12963 | exact mod_symm (superpose eq18257 eq12963) | exact superpose eq12963 eq18257 | exact mod_symm (superpose eq12963 eq18257)
  have eq60263 (X0 X1 : G) : (e (w (X1 ◇ X0) X1)) = (e (((e (v (v X0))) ◇ X1) ◇ (v (v X0)))) := by first | exact superpose eq30 eq60113 | exact mod_symm (superpose eq30 eq60113) | exact superpose eq60113 eq30 | exact mod_symm (superpose eq60113 eq30)
  have eq60371 (X0 X1 : G) : (e (w (X1 ◇ X0) X1)) = (e (((v (v X0)) ◇ X1) ◇ (v (v X0)))) := by first | exact superpose eq140 eq60263 | exact mod_symm (superpose eq140 eq60263) | exact superpose eq60263 eq140 | exact mod_symm (superpose eq60263 eq140)
  have eq60457 (X0 X1 : G) : (w (X1 ◇ X0) X1) = (e (((v (v X0)) ◇ X1) ◇ (v (v X0)))) := by first | exact superpose eq102 eq60371 | exact mod_symm (superpose eq102 eq60371) | exact superpose eq60371 eq102 | exact mod_symm (superpose eq60371 eq102)
  have eq72897 (X0 X1 : G) : (e (v (v (v ((X1 ◇ X1) ◇ (e (X0 ◇ X0))))))) = (v (w X1 ((e X0) ◇ ((e (X0 ◇ X0)) ◇ (e (X0 ◇ X0)))))) := by first | exact superpose eq735 eq103 | exact mod_symm (superpose eq735 eq103) | exact superpose eq103 eq735 | exact mod_symm (superpose eq103 eq735)
  have eq73113 (X0 X1 : G) : (e (v (v (v ((X1 ◇ X1) ◇ (e (X0 ◇ X0))))))) = (w (v X1) ((v (e X0)) ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq3397 eq72897 | exact mod_symm (superpose eq3397 eq72897) | exact superpose eq72897 eq3397 | exact mod_symm (superpose eq72897 eq3397)
  have eq73510 (X0 X1 : G) : (e (v (v (v ((X1 ◇ X1) ◇ (e (X0 ◇ X0))))))) = (w (e (X0 ◇ X0)) (w (e X0) X1)) := by first | exact superpose eq9985 eq73113 | exact mod_symm (superpose eq9985 eq73113) | exact superpose eq73113 eq9985 | exact mod_symm (superpose eq73113 eq9985)
  have eq73879 (X0 X1 : G) : (e (v (v (v ((X1 ◇ X1) ◇ (e (X0 ◇ X0))))))) = (e (X0 ◇ (v (w (e X0) X1)))) := by first | exact superpose eq1420 eq73510 | exact mod_symm (superpose eq1420 eq73510) | exact superpose eq73510 eq1420 | exact mod_symm (superpose eq73510 eq1420)
  have eq74212 (X0 X1 : G) : (e (v (v (v ((X1 ◇ X1) ◇ (e (X0 ◇ X0))))))) = (e (X0 ◇ (v (w X0 (e X1))))) := by first | exact superpose eq1442 eq73879 | exact mod_symm (superpose eq1442 eq73879) | exact superpose eq73879 eq1442 | exact mod_symm (superpose eq73879 eq1442)
  have eq74501 (X0 X1 : G) : (e (v (v (v ((X1 ◇ X1) ◇ (e (X0 ◇ X0))))))) = (e (X0 ◇ (v (w X0 X1)))) := by first | exact superpose eq1745 eq74212 | exact mod_symm (superpose eq1745 eq74212) | exact superpose eq74212 eq1745 | exact mod_symm (superpose eq74212 eq1745)
  have eq74696 (X0 X1 : G) : (v (w X1 (v (X0 ◇ X0)))) = (e (X0 ◇ (v (w X0 X1)))) := by first | exact superpose eq1859 eq74501 | exact mod_symm (superpose eq1859 eq74501) | exact superpose eq74501 eq1859 | exact mod_symm (superpose eq74501 eq1859)
  have eq74865 (X0 X1 : G) : (v (w X1 (w X0 X0))) = (e (X0 ◇ (v (w X0 X1)))) := by first | exact superpose eq1782 eq74696 | exact mod_symm (superpose eq1782 eq74696) | exact superpose eq74696 eq1782 | exact mod_symm (superpose eq74696 eq1782)
  have eq74998 (X0 X1 : G) : (v (w X1 (e X0))) = (e (X0 ◇ (v (w X0 X1)))) := by first | exact superpose eq263 eq74865 | exact mod_symm (superpose eq263 eq74865) | exact superpose eq74865 eq263 | exact mod_symm (superpose eq74865 eq263)
  have eq75105 (X0 X1 : G) : (v (w X1 X0)) = (e (X0 ◇ (v (w X0 X1)))) := by first | exact superpose eq1745 eq74998 | exact mod_symm (superpose eq1745 eq74998) | exact superpose eq74998 eq1745 | exact mod_symm (superpose eq74998 eq1745)
  have eq75591 (X0 X1 : G) : (v (v (w X0 X1))) = (e (v (X1 ◇ (v (w X1 X0))))) := by first | exact superpose eq75105 eq17 | exact mod_symm (superpose eq75105 eq17) | exact superpose eq17 eq75105 | exact mod_symm (superpose eq17 eq75105)
  have eq75598 (X0 X1 X2 X3 : G) : (e ((X2 ◇ (v (w X0 X1))) ◇ X3)) = (e ((X2 ◇ (X1 ◇ (v (w X1 X0)))) ◇ X3)) := by first | exact superpose eq75105 eq69 | exact mod_symm (superpose eq75105 eq69) | exact superpose eq69 eq75105 | exact mod_symm (superpose eq69 eq75105)
  have eq75698 (X0 X1 : G) : (v (v (w X0 X1))) = (w X1 (e (v (w X1 X0)))) := by first | exact superpose eq629 eq75591 | exact mod_symm (superpose eq629 eq75591) | exact superpose eq75591 eq629 | exact mod_symm (superpose eq75591 eq629)
  have eq75830 (X0 X1 : G) : (v (v (w X0 X1))) = (w X1 (v (w X1 X0))) := by first | exact superpose eq1745 eq75698 | exact mod_symm (superpose eq1745 eq75698) | exact superpose eq75698 eq1745 | exact mod_symm (superpose eq75698 eq1745)
  have eq81117 (X0 X1 : G) : (e (v (w X1 X0))) = (e (((v (v (w X0 X1))) ◇ X1) ◇ (v (v (w X0 X1))))) := by first | exact superpose eq75830 eq12963 | exact mod_symm (superpose eq75830 eq12963) | exact superpose eq12963 eq75830 | exact mod_symm (superpose eq12963 eq75830)
  have eq81158 (X0 X1 : G) : (w (X1 ◇ (w X0 X1)) X1) = (e (v (w X1 X0))) := by first | exact superpose eq60457 eq81117 | exact mod_symm (superpose eq60457 eq81117) | exact superpose eq81117 eq60457 | exact mod_symm (superpose eq81117 eq60457)
  have eq81263 (X0 X1 : G) : (v (w X1 X0)) = (w (X1 ◇ (w X0 X1)) X1) := by first | exact superpose eq118 eq81158 | exact mod_symm (superpose eq118 eq81158) | exact superpose eq81158 eq118 | exact mod_symm (superpose eq81158 eq118)
  have eq92068 (X0 X1 : G) : (e X0) = (e (((v (w X0 X1)) ◇ (X0 ◇ (w X1 X0))) ◇ (v (w X0 X1)))) := by first | exact superpose eq81263 eq12963 | exact mod_symm (superpose eq81263 eq12963) | exact superpose eq12963 eq81263 | exact mod_symm (superpose eq12963 eq81263)
  have eq92119 (X0 X1 : G) : (e X0) = (e (((w X1 X0) ◇ (X0 ◇ (v (w X0 X1)))) ◇ (v (w X0 X1)))) := by first | exact superpose eq52626 eq92068 | exact mod_symm (superpose eq52626 eq92068) | exact superpose eq92068 eq52626 | exact mod_symm (superpose eq92068 eq52626)
  have eq92242 (X0 X1 : G) : (e X0) = (e (((w X1 X0) ◇ (v (w X1 X0))) ◇ (v (w X0 X1)))) := by first | exact superpose eq75598 eq92119 | exact mod_symm (superpose eq75598 eq92119) | exact superpose eq92119 eq75598 | exact mod_symm (superpose eq92119 eq75598)
  have eq92346 (X0 X1 : G) : (e X0) = (e ((v (w X1 X0)) ◇ (v (w X0 X1)))) := by first | exact superpose eq160 eq92242 | exact mod_symm (superpose eq160 eq92242) | exact superpose eq92242 eq160 | exact mod_symm (superpose eq92242 eq160)
  have eq92433 (X0 X1 : G) : (e X0) = (e (v ((w X1 X0) ◇ (w X0 X1)))) := by first | exact superpose eq15 eq92346 | exact mod_symm (superpose eq15 eq92346) | exact superpose eq92346 eq15 | exact mod_symm (superpose eq92346 eq15)
  have eq92507 (X0 X1 : G) : (e X0) = (w (w X1 X0) (e (w X0 X1))) := by first | exact superpose eq629 eq92433 | exact mod_symm (superpose eq629 eq92433) | exact superpose eq92433 eq629 | exact mod_symm (superpose eq92433 eq629)
  have eq92562 (X0 X1 : G) : (e X0) = (w (w X1 X0) (w X0 X1)) := by first | exact superpose eq1745 eq92507 | exact mod_symm (superpose eq1745 eq92507) | exact superpose eq92507 eq1745 | exact mod_symm (superpose eq92507 eq1745)
  have eq94813 : (w x x) ≠ (e x) := by first | exact superpose eq92562 eq21 | exact mod_symm (superpose eq92562 eq21) | exact superpose eq21 eq92562 | exact mod_symm (superpose eq21 eq92562)
  subsumption eq94813 eq263


/-- Equation 4443 `x ◇ (y ◇ x) = (y ◇ x) ◇ y` is term-definable from equation 546 over finite magmas, via the term
`x □ y := u^[3N+1] ((x ◇ x) ◇ (y ◇ y))` where `u a = a ◇ a`. -/
private theorem aux546_4443 [Magma G] (h : Equation546 G) (e v : G → G) (w : G → G → G)
    (heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b) (hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b)
    (hee : ∀ a : G, e (e a) = e a) (hve : ∀ a : G, v (e a) = e (v a))
    (huve : ∀ a : G, v (e a) ◇ v (e a) = e a) (hvue : ∀ a : G, v (e a ◇ e a) = e a)
    (hw : ∀ a b : G, w a b = (e (v (v ((a ◇ a) ◇ (b ◇ b))))))
    (x y : G) :
    (w x (w y x)) =
      (w (w y x) y) := by
  by_contra nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq14 (X0 X1 : G) : (e (X0 ◇ X1)) = ((e X0) ◇ (e X1)) := mod_symm (heh ..)
  have eq15 (X0 X1 : G) : (v (X0 ◇ X1)) = ((v X0) ◇ (v X1)) := mod_symm (hvh ..)
  have eq16 (X0 : G) : (e X0) = (e (e X0)) := mod_symm (hee ..)
  have eq17 (X0 : G) : (v (e X0)) = (e (v X0)) := mod_symm (hve ..)
  have eq18 (X0 : G) : (e X0) = ((v (e X0)) ◇ (v (e X0))) := mod_symm (huve ..)
  have eq19 (X0 : G) : (e X0) = (v ((e X0) ◇ (e X0))) := mod_symm (hvue ..)
  have eq20 (X0 X1 : G) : (w X0 X1) = (e (v (v ((X0 ◇ X0) ◇ (X1 ◇ X1))))) := mod_symm (hw ..)
  have eq21 : (w x (w y x)) ≠ (w (w y x) y) := mod_symm nh
  have eq26 (X0 X1 : G) : ((e X0) ◇ (e X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq27 (X0 X1 : G) : (e (X1 ◇ (e X0))) = ((e X1) ◇ (e X0)) := by first | exact superpose eq16 eq14 | exact mod_symm (superpose eq16 eq14) | exact superpose eq14 eq16 | exact mod_symm (superpose eq14 eq16)
  have eq28 (X0 : G) : (e X0) = (v (e (X0 ◇ X0))) := by first | exact superpose eq14 eq19 | exact mod_symm (superpose eq14 eq19) | exact superpose eq19 eq14 | exact mod_symm (superpose eq19 eq14)
  have eq29 (X0 : G) : (e X0) = (e (v (X0 ◇ X0))) := by first | exact superpose eq17 eq28 | exact mod_symm (superpose eq17 eq28) | exact superpose eq28 eq17 | exact mod_symm (superpose eq28 eq17)
  have eq30 (X0 X1 : G) : (e (X1 ◇ (e X0))) = (e (X1 ◇ X0)) := by first | exact superpose eq14 eq27 | exact mod_symm (superpose eq14 eq27) | exact superpose eq27 eq14 | exact mod_symm (superpose eq27 eq14)
  have eq31 (X0 X1 : G) : (e (X0 ◇ X1)) = (e ((e X0) ◇ X1)) := by first | exact superpose eq14 eq26 | exact mod_symm (superpose eq14 eq26) | exact superpose eq26 eq14 | exact mod_symm (superpose eq26 eq14)
  have eq33 (X0 X1 : G) : (v (((e X0) ◇ (e X0)) ◇ X1)) = ((e X0) ◇ (v X1)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq35 (X0 X1 : G) : (v (X1 ◇ ((e X0) ◇ (e X0)))) = ((v X1) ◇ (e X0)) := by first | exact superpose eq19 eq15 | exact mod_symm (superpose eq19 eq15) | exact superpose eq15 eq19 | exact mod_symm (superpose eq15 eq19)
  have eq36 (X0 X1 : G) : ((v X1) ◇ (e X0)) = (v (X1 ◇ (e (X0 ◇ X0)))) := by first | exact superpose eq14 eq35 | exact mod_symm (superpose eq14 eq35) | exact superpose eq35 eq14 | exact mod_symm (superpose eq35 eq14)
  have eq37 (X0 X1 : G) : ((e X0) ◇ (v X1)) = (v ((e (X0 ◇ X0)) ◇ X1)) := by first | exact superpose eq14 eq33 | exact mod_symm (superpose eq14 eq33) | exact superpose eq33 eq14 | exact mod_symm (superpose eq33 eq14)
  have eq64 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (v (e (X0 ◇ X1))) := by first | exact superpose eq30 eq17 | exact mod_symm (superpose eq30 eq17) | exact superpose eq17 eq30 | exact mod_symm (superpose eq17 eq30)
  have eq67 (X0 X1 : G) : (e (v (X0 ◇ (e X1)))) = (e (v (X0 ◇ X1))) := by first | exact superpose eq17 eq64 | exact mod_symm (superpose eq17 eq64) | exact superpose eq64 eq17 | exact mod_symm (superpose eq64 eq17)
  have eq76 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0))) = X3 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq77 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X2 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq78 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := by first | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13) | exact superpose eq13 eq13 | exact mod_symm (superpose eq13 eq13)
  have eq83 (X0 : G) : (v (e X0)) = ((e X0) ◇ (v (e X0))) := by first | exact superpose eq18 eq78 | exact mod_symm (superpose eq18 eq78) | exact superpose eq78 eq18 | exact mod_symm (superpose eq78 eq18)
  have eq85 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X1 ◇ (X2 ◇ X0)) := by first | exact superpose eq78 eq13 | exact mod_symm (superpose eq78 eq13) | exact superpose eq13 eq78 | exact mod_symm (superpose eq13 eq78)
  have eq89 (X0 : G) : (e (v X0)) = ((e X0) ◇ (e (v X0))) := by first | exact superpose eq17 eq83 | exact mod_symm (superpose eq17 eq83) | exact superpose eq83 eq17 | exact mod_symm (superpose eq83 eq17)
  have eq92 (X0 : G) : (e (v X0)) = (e (X0 ◇ (v X0))) := by first | exact superpose eq14 eq89 | exact mod_symm (superpose eq14 eq89) | exact superpose eq89 eq14 | exact mod_symm (superpose eq89 eq14)
  have eq93 (X0 X1 : G) : (w (e X0) X1) = (e (v (v ((e (X0 ◇ X0)) ◇ (X1 ◇ X1))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq96 (X0 X1 : G) : (w X1 (e X0)) = (e (v (v ((X1 ◇ X1) ◇ (e (X0 ◇ X0)))))) := by first | exact superpose eq14 eq20 | exact mod_symm (superpose eq14 eq20) | exact superpose eq20 eq14 | exact mod_symm (superpose eq20 eq14)
  have eq111 (X0 X1 : G) : (w X1 (e X0)) = (e (v ((v (X1 ◇ X1)) ◇ (e X0)))) := by first | exact superpose eq36 eq96 | exact mod_symm (superpose eq36 eq96) | exact superpose eq96 eq36 | exact mod_symm (superpose eq96 eq36)
  have eq113 (X0 X1 : G) : (w (e X0) X1) = (e (v ((e X0) ◇ (v (X1 ◇ X1))))) := by first | exact superpose eq37 eq93 | exact mod_symm (superpose eq37 eq93) | exact superpose eq93 eq37 | exact mod_symm (superpose eq93 eq37)
  have eq114 (X0 X1 : G) : (w X1 (e X0)) = (e (v ((v (X1 ◇ X1)) ◇ X0))) := by first | exact superpose eq67 eq111 | exact mod_symm (superpose eq67 eq111) | exact superpose eq111 eq67 | exact mod_symm (superpose eq111 eq67)
  have eq133 (X0 X1 : G) : (v (e (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq31 eq17 | exact mod_symm (superpose eq31 eq17) | exact superpose eq17 eq31 | exact mod_symm (superpose eq17 eq31)
  have eq138 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((e X0) ◇ X1))) := by first | exact superpose eq17 eq133 | exact mod_symm (superpose eq17 eq133) | exact superpose eq133 eq17 | exact mod_symm (superpose eq133 eq17)
  have eq149 (X0 : G) : (e (v (v X0))) = (e (v (X0 ◇ (v X0)))) := by first | exact superpose eq15 eq92 | exact mod_symm (superpose eq15 eq92) | exact superpose eq92 eq15 | exact mod_symm (superpose eq92 eq15)
  have eq575 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((v (e (X0 ◇ X0))) ◇ X1))) := by first | exact superpose eq14 eq114 | exact mod_symm (superpose eq14 eq114) | exact superpose eq114 eq14 | exact mod_symm (superpose eq114 eq14)
  have eq578 (X0 X1 : G) : (e (v ((e X0) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq19 eq114 | exact mod_symm (superpose eq19 eq114) | exact superpose eq114 eq19 | exact mod_symm (superpose eq114 eq19)
  have eq582 (X0 X1 : G) : (w X0 (e (v X1))) = (e (v (v ((X0 ◇ X0) ◇ X1)))) := by first | exact superpose eq15 eq114 | exact mod_symm (superpose eq15 eq114) | exact superpose eq114 eq15 | exact mod_symm (superpose eq114 eq15)
  have eq614 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq138 eq578 | exact mod_symm (superpose eq138 eq578) | exact superpose eq578 eq138 | exact mod_symm (superpose eq578 eq138)
  have eq616 (X0 X1 : G) : (w (e X0) (e X1)) = (e (v ((e (v (X0 ◇ X0))) ◇ X1))) := by first | exact superpose eq17 eq575 | exact mod_symm (superpose eq17 eq575) | exact superpose eq575 eq17 | exact mod_symm (superpose eq575 eq17)
  have eq622 (X0 X1 : G) : (e (v ((v (X0 ◇ X0)) ◇ X1))) = (w (e X0) (e X1)) := by first | exact superpose eq138 eq616 | exact mod_symm (superpose eq138 eq616) | exact superpose eq616 eq138 | exact mod_symm (superpose eq616 eq138)
  have eq626 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (e (v ((v (X0 ◇ X0)) ◇ X1))) := by first | exact superpose eq614 eq622 | exact mod_symm (superpose eq614 eq622) | exact superpose eq622 eq614 | exact mod_symm (superpose eq622 eq614)
  have eq629 (X0 X1 : G) : (e (v (X0 ◇ X1))) = (w X0 (e X1)) := by first | exact superpose eq114 eq626 | exact mod_symm (superpose eq114 eq626) | exact superpose eq626 eq114 | exact mod_symm (superpose eq626 eq114)
  have eq636 (X0 X1 : G) : (e (v X0)) = (w (X0 ◇ X1) (e X1)) := by first | exact superpose eq78 eq629 | exact mod_symm (superpose eq78 eq629) | exact superpose eq629 eq78 | exact mod_symm (superpose eq629 eq78)
  have eq824 (X0 X1 X2 : G) : (e (v (X1 ◇ (X2 ◇ X0)))) = (w X0 (e (X2 ◇ X1))) := by first | exact superpose eq77 eq636 | exact mod_symm (superpose eq77 eq636) | exact superpose eq636 eq77 | exact mod_symm (superpose eq636 eq77)
  have eq856 (X0 X1 X2 : G) : (w X0 (e (X2 ◇ X1))) = (w X1 (e (X2 ◇ X0))) := by first | exact superpose eq629 eq824 | exact mod_symm (superpose eq629 eq824) | exact superpose eq824 eq629 | exact mod_symm (superpose eq824 eq629)
  have eq1207 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := by first | exact superpose eq78 eq85 | exact mod_symm (superpose eq78 eq85) | exact superpose eq85 eq78 | exact mod_symm (superpose eq85 eq78)
  have eq1255 (X0 X1 X2 : G) : (w X2 (X1 ◇ X0)) = (e (v (v ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))))) := by first | exact superpose eq85 eq20 | exact mod_symm (superpose eq85 eq20) | exact superpose eq20 eq85 | exact mod_symm (superpose eq20 eq85)
  have eq1256 (X0 X1 : G) : (e (X1 ◇ X0)) = (e (v (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by first | exact superpose eq85 eq29 | exact mod_symm (superpose eq85 eq29) | exact superpose eq29 eq85 | exact mod_symm (superpose eq29 eq85)
  have eq1288 (X0 X1 : G) : (e (X1 ◇ X0)) = (w X0 (e (X1 ◇ (X1 ◇ X0)))) := by first | exact superpose eq629 eq1256 | exact mod_symm (superpose eq629 eq1256) | exact superpose eq1256 eq629 | exact mod_symm (superpose eq1256 eq629)
  have eq1289 (X0 X1 X2 : G) : (w X2 (X1 ◇ X0)) = (w X2 (e (v (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := by first | exact superpose eq582 eq1255 | exact mod_symm (superpose eq582 eq1255) | exact superpose eq1255 eq582 | exact mod_symm (superpose eq1255 eq582)
  have eq1317 (X0 X1 X2 : G) : (w X2 (X1 ◇ X0)) = (w X2 (w X0 (e (X1 ◇ (X1 ◇ X0))))) := by first | exact superpose eq629 eq1289 | exact mod_symm (superpose eq629 eq1289) | exact superpose eq1289 eq629 | exact mod_symm (superpose eq1289 eq629)
  have eq1328 (X0 X1 X2 : G) : (w X2 (e (X1 ◇ X0))) = (w X2 (X1 ◇ X0)) := by first | exact superpose eq1288 eq1317 | exact mod_symm (superpose eq1288 eq1317) | exact superpose eq1317 eq1288 | exact mod_symm (superpose eq1317 eq1288)
  have eq1362 (X0 X1 : G) : (w (e X0) X1) = (w (e X0) (e (v (X1 ◇ X1)))) := by first | exact superpose eq113 eq629 | exact mod_symm (superpose eq113 eq629) | exact superpose eq629 eq113 | exact mod_symm (superpose eq629 eq113)
  have eq1393 (X0 X1 : G) : (w (e X0) X1) = (e (v (X0 ◇ (v (X1 ◇ X1))))) := by first | exact superpose eq614 eq1362 | exact mod_symm (superpose eq614 eq1362) | exact superpose eq1362 eq614 | exact mod_symm (superpose eq1362 eq614)
  have eq1418 (X0 X1 : G) : (w (e X0) X1) = (w X0 (e (v (X1 ◇ X1)))) := by first | exact superpose eq629 eq1393 | exact mod_symm (superpose eq629 eq1393) | exact superpose eq1393 eq629 | exact mod_symm (superpose eq1393 eq629)
  have eq1442 (X0 X1 : G) : (w (e X0) X1) = (w X0 (e X1)) := by first | exact superpose eq29 eq1418 | exact mod_symm (superpose eq29 eq1418) | exact superpose eq1418 eq29 | exact mod_symm (superpose eq1418 eq29)
  have eq1499 (X0 X1 X2 : G) : (w (e (X0 ◇ X1)) X2) = (w ((e X0) ◇ X1) (e X2)) := by first | exact superpose eq31 eq1442 | exact mod_symm (superpose eq31 eq1442) | exact superpose eq1442 eq31 | exact mod_symm (superpose eq1442 eq31)
  have eq1529 (X0 X1 X2 : G) : (w ((e X0) ◇ X1) (e X2)) = (w (X0 ◇ X1) (e X2)) := by first | exact superpose eq1442 eq1499 | exact mod_symm (superpose eq1442 eq1499) | exact superpose eq1499 eq1442 | exact mod_symm (superpose eq1499 eq1442)
  have eq1625 (X0 X1 : G) : (w (e X1) (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (e (v ((e X1) ◇ (v (X0 ◇ X0))))) := by first | exact superpose eq76 eq113 | exact mod_symm (superpose eq76 eq113) | exact superpose eq113 eq76 | exact mod_symm (superpose eq113 eq76)
  have eq1648 (X0 X1 : G) : (w (e X1) (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (w (e X1) (e (v (X0 ◇ X0)))) := by first | exact superpose eq629 eq1625 | exact mod_symm (superpose eq629 eq1625) | exact superpose eq1625 eq629 | exact mod_symm (superpose eq1625 eq629)
  have eq1705 (X0 X1 : G) : (w (e X1) (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (e (v (X1 ◇ (v (X0 ◇ X0))))) := by first | exact superpose eq614 eq1648 | exact mod_symm (superpose eq614 eq1648) | exact superpose eq1648 eq614 | exact mod_symm (superpose eq1648 eq614)
  have eq1733 (X0 X1 : G) : (w X1 (e (v (X0 ◇ X0)))) = (w (e X1) (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by first | exact superpose eq629 eq1705 | exact mod_symm (superpose eq629 eq1705) | exact superpose eq1705 eq629 | exact mod_symm (superpose eq1705 eq629)
  have eq1739 (X0 X1 : G) : (w X1 (e (v (X0 ◇ X0)))) = (w X1 (e (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := by first | exact superpose eq1442 eq1733 | exact mod_symm (superpose eq1442 eq1733) | exact superpose eq1733 eq1442 | exact mod_symm (superpose eq1733 eq1442)
  have eq1742 (X0 X1 : G) : (w X1 (e (v (X0 ◇ X0)))) = (w X1 (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by first | exact superpose eq1328 eq1739 | exact mod_symm (superpose eq1328 eq1739) | exact superpose eq1739 eq1328 | exact mod_symm (superpose eq1739 eq1328)
  have eq1743 (X0 X1 : G) : (w X1 (e (v (X0 ◇ X0)))) = (w X1 ((X0 ◇ X0) ◇ X0)) := by first | exact superpose eq1207 eq1742 | exact mod_symm (superpose eq1207 eq1742) | exact superpose eq1742 eq1207 | exact mod_symm (superpose eq1742 eq1207)
  have eq1744 (X0 X1 : G) : (w X1 X0) = (w X1 (e (v (X0 ◇ X0)))) := by first | exact superpose eq78 eq1743 | exact mod_symm (superpose eq78 eq1743) | exact superpose eq1743 eq78 | exact mod_symm (superpose eq1743 eq78)
  have eq1745 (X0 X1 : G) : (w X1 X0) = (w X1 (e X0)) := by first | exact superpose eq29 eq1744 | exact mod_symm (superpose eq29 eq1744) | exact superpose eq1744 eq29 | exact mod_symm (superpose eq1744 eq29)
  have eq1748 (X0 X1 X2 : G) : (w X2 (e (X0 ◇ X1))) = (w X2 ((e X0) ◇ X1)) := by first | exact superpose eq31 eq1745 | exact mod_symm (superpose eq31 eq1745) | exact superpose eq1745 eq31 | exact mod_symm (superpose eq1745 eq31)
  have eq1750 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ X1))) = (w X2 (w X0 (e X1))) := by first | exact superpose eq629 eq1745 | exact mod_symm (superpose eq629 eq1745) | exact superpose eq1745 eq629 | exact mod_symm (superpose eq1745 eq629)
  have eq1769 (X0 X1 : G) : (e (v X0)) = (w (X0 ◇ X1) X1) := by first | exact superpose eq1745 eq636 | exact mod_symm (superpose eq1745 eq636) | exact superpose eq636 eq1745 | exact mod_symm (superpose eq636 eq1745)
  have eq1782 (X0 X1 X2 : G) : (w X2 (v (X0 ◇ X1))) = (w X2 (w X0 X1)) := by first | exact superpose eq1745 eq1750 | exact mod_symm (superpose eq1745 eq1750) | exact superpose eq1750 eq1745 | exact mod_symm (superpose eq1750 eq1745)
  have eq1784 (X0 X1 X2 : G) : (w X2 ((e X0) ◇ X1)) = (w X2 (X0 ◇ X1)) := by first | exact superpose eq1328 eq1748 | exact mod_symm (superpose eq1328 eq1748) | exact superpose eq1748 eq1328 | exact mod_symm (superpose eq1748 eq1328)
  have eq1984 (X0 X1 : G) : (w X0 X1) = (e (v (X0 ◇ X1))) := by first | exact superpose eq78 eq1769 | exact mod_symm (superpose eq78 eq1769) | exact superpose eq1769 eq78 | exact mod_symm (superpose eq1769 eq78)
  have eq2874 (X0 X1 X2 : G) : (w (w X0 X1) X2) = (w (v (X0 ◇ X1)) (e X2)) := by first | exact superpose eq1984 eq1442 | exact mod_symm (superpose eq1984 eq1442) | exact superpose eq1442 eq1984 | exact mod_symm (superpose eq1442 eq1984)
  have eq2876 (X0 X1 X2 : G) : (w (w X0 X1) X2) = (w (v (X0 ◇ X1)) X2) := by first | exact superpose eq1745 eq2874 | exact mod_symm (superpose eq1745 eq2874) | exact superpose eq2874 eq1745 | exact mod_symm (superpose eq2874 eq1745)
  have eq3828 (X0 X1 : G) : (e (v ((e X0) ◇ (v X1)))) = (e (v (((e (X0 ◇ X0)) ◇ X1) ◇ ((e X0) ◇ (v X1))))) := by first | exact superpose eq37 eq149 | exact mod_symm (superpose eq37 eq149) | exact superpose eq149 eq37 | exact mod_symm (superpose eq149 eq37)
  have eq3899 (X0 X1 : G) : (e (v ((e X0) ◇ (v X1)))) = (w ((e (X0 ◇ X0)) ◇ X1) (e ((e X0) ◇ (v X1)))) := by first | exact superpose eq629 eq3828 | exact mod_symm (superpose eq629 eq3828) | exact superpose eq3828 eq629 | exact mod_symm (superpose eq3828 eq629)
  have eq3928 (X0 X1 : G) : (e (v ((e X0) ◇ (v X1)))) = (w ((X0 ◇ X0) ◇ X1) (e ((e X0) ◇ (v X1)))) := by first | exact superpose eq1529 eq3899 | exact mod_symm (superpose eq1529 eq3899) | exact superpose eq3899 eq1529 | exact mod_symm (superpose eq3899 eq1529)
  have eq3955 (X0 X1 : G) : (e (v ((e X0) ◇ (v X1)))) = (w (v X1) (e ((e X0) ◇ ((X0 ◇ X0) ◇ X1)))) := by first | exact superpose eq856 eq3928 | exact mod_symm (superpose eq856 eq3928) | exact superpose eq3928 eq856 | exact mod_symm (superpose eq3928 eq856)
  have eq3969 (X0 X1 : G) : (e (v ((e X0) ◇ (v X1)))) = (w (v X1) ((e X0) ◇ ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq1328 eq3955 | exact mod_symm (superpose eq1328 eq3955) | exact superpose eq3955 eq1328 | exact mod_symm (superpose eq3955 eq1328)
  have eq3978 (X0 X1 : G) : (e (v ((e X0) ◇ (v X1)))) = (w (v X1) (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by first | exact superpose eq1784 eq3969 | exact mod_symm (superpose eq1784 eq3969) | exact superpose eq3969 eq1784 | exact mod_symm (superpose eq3969 eq1784)
  have eq3985 (X0 X1 : G) : (e (v ((e X0) ◇ (v X1)))) = (w (v X1) (X1 ◇ X0)) := by first | exact superpose eq1207 eq3978 | exact mod_symm (superpose eq1207 eq3978) | exact superpose eq3978 eq1207 | exact mod_symm (superpose eq3978 eq1207)
  have eq3991 (X0 X1 : G) : (w (e X0) (e (v X1))) = (w (v X1) (X1 ◇ X0)) := by first | exact superpose eq629 eq3985 | exact mod_symm (superpose eq629 eq3985) | exact superpose eq3985 eq629 | exact mod_symm (superpose eq3985 eq629)
  have eq3995 (X0 X1 : G) : (e (v (X0 ◇ (v X1)))) = (w (v X1) (X1 ◇ X0)) := by first | exact superpose eq614 eq3991 | exact mod_symm (superpose eq614 eq3991) | exact superpose eq3991 eq614 | exact mod_symm (superpose eq3991 eq614)
  have eq3999 (X0 X1 : G) : (w X0 (e (v X1))) = (w (v X1) (X1 ◇ X0)) := by first | exact superpose eq629 eq3995 | exact mod_symm (superpose eq629 eq3995) | exact superpose eq3995 eq629 | exact mod_symm (superpose eq3995 eq629)
  have eq4001 (X0 X1 : G) : (w X0 (v X1)) = (w (v X1) (X1 ◇ X0)) := by first | exact superpose eq1745 eq3999 | exact mod_symm (superpose eq1745 eq3999) | exact superpose eq3999 eq1745 | exact mod_symm (superpose eq3999 eq1745)
  have eq8435 (X0 X1 : G) : (w X1 (v (X0 ◇ X1))) = (w (v (X0 ◇ X1)) X0) := by first | exact superpose eq78 eq4001 | exact mod_symm (superpose eq78 eq4001) | exact superpose eq4001 eq78 | exact mod_symm (superpose eq4001 eq78)
  have eq8473 (X0 X1 : G) : (w X1 (v (X0 ◇ X1))) = (w (w X0 X1) X0) := by first | exact superpose eq2876 eq8435 | exact mod_symm (superpose eq2876 eq8435) | exact superpose eq8435 eq2876 | exact mod_symm (superpose eq8435 eq2876)
  have eq8492 (X0 X1 : G) : (w X1 (w X0 X1)) = (w (w X0 X1) X0) := by first | exact superpose eq1782 eq8473 | exact mod_symm (superpose eq1782 eq8473) | exact superpose eq8473 eq1782 | exact mod_symm (superpose eq8473 eq1782)
  have eq11823 : (w x (w y x)) ≠ (w x (w y x)) := by first | exact superpose eq8492 eq21 | exact mod_symm (superpose eq8492 eq21) | exact superpose eq21 eq8492 | exact mod_symm (superpose eq21 eq8492)
  first | exact eq11823 rfl | exact eq11823 _ rfl | exact eq11823 _ _ rfl | exact eq11823 _ _ _ rfl


theorem Equation332_termDefinableFromFin_Equation546 :
    Law332.TermDefinableFromFin Law546 := by
  refine termDefinableFromFin_of_iterate_evv (fun G ↦ tm1 (Term.var 0) (Term.var 0))
    (fun G ↦ (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0)))) ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation546 G := Law546.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (Term.var 0)) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (Term.var 0)) a ◇ ufunM M (tm1 (Term.var 0) (Term.var 0)) b :=
    fun a b ↦ sq_endo h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, v (e a) ◇ v (e a) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v (e a ◇ e a) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law332.models_iff]
  intro x y
  exact aux546_332 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

theorem Equation3342_termDefinableFromFin_Equation546 :
    Law3342.TermDefinableFromFin Law546 := by
  refine termDefinableFromFin_of_iterate_evv (fun G ↦ tm1 (Term.var 0) (Term.var 0))
    (fun G ↦ (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0)))) ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation546 G := Law546.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (Term.var 0)) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (Term.var 0)) a ◇ ufunM M (tm1 (Term.var 0) (Term.var 0)) b :=
    fun a b ↦ sq_endo h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, v (e a) ◇ v (e a) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v (e a ◇ e a) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law3342.models_iff]
  intro x y
  exact aux546_3342 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

theorem Equation3345_termDefinableFromFin_Equation546 :
    Law3345.TermDefinableFromFin Law546 := by
  refine termDefinableFromFin_of_iterate_evv (fun G ↦ tm1 (Term.var 0) (Term.var 0))
    (fun G ↦ (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))) (Term.var 1))) ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation546 G := Law546.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (Term.var 0)) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (Term.var 0)) a ◇ ufunM M (tm1 (Term.var 0) (Term.var 0)) b :=
    fun a b ↦ sq_endo h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, v (e a) ◇ v (e a) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v (e a ◇ e a) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law3345.models_iff]
  intro x y
  exact aux546_3345 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

theorem Equation3545_termDefinableFromFin_Equation546 :
    Law3545.TermDefinableFromFin Law546 := by
  refine termDefinableFromFin_of_iterate_evv (fun G ↦ tm1 (Term.var 0) (Term.var 0))
    (fun G ↦ (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0)))) ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation546 G := Law546.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (Term.var 0)) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (Term.var 0)) a ◇ ufunM M (tm1 (Term.var 0) (Term.var 0)) b :=
    fun a b ↦ sq_endo h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, v (e a) ◇ v (e a) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v (e a ◇ e a) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law3545.models_iff]
  intro x y
  exact aux546_3545 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

theorem Equation3675_termDefinableFromFin_Equation546 :
    Law3675.TermDefinableFromFin Law546 := by
  refine termDefinableFromFin_of_iterate_evv (fun G ↦ tm1 (Term.var 0) (Term.var 0))
    (fun G ↦ (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1)))) ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation546 G := Law546.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (Term.var 0)) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (Term.var 0)) a ◇ ufunM M (tm1 (Term.var 0) (Term.var 0)) b :=
    fun a b ↦ sq_endo h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, v (e a) ◇ v (e a) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v (e a ◇ e a) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law3675.models_iff]
  intro x y
  exact aux546_3675 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

theorem Equation4443_termDefinableFromFin_Equation546 :
    Law4443.TermDefinableFromFin Law546 := by
  refine termDefinableFromFin_of_iterate_evv (fun G ↦ tm1 (Term.var 0) (Term.var 0))
    (fun G ↦ (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1)))) ?_
  intro G _ M hGL N e v he
  letI : Magma G := M
  have h : Equation546 G := Law546.models_iff.mp hGL
  have hu : ∀ a b : G, ufunM M (tm1 (Term.var 0) (Term.var 0)) (a ◇ b)
      = ufunM M (tm1 (Term.var 0) (Term.var 0)) a ◇ ufunM M (tm1 (Term.var 0) (Term.var 0)) b :=
    fun a b ↦ sq_endo h a b
  have heh : ∀ a b : G, e (a ◇ b) = e a ◇ e b := by
    rw [he.e_eq]; exact iterate_endo hu _
  have hvh : ∀ a b : G, v (a ◇ b) = v a ◇ v b := by
    rw [he.v_eq]; exact iterate_endo hu _
  have huve : ∀ a : G, v (e a) ◇ v (e a) = e a := fun a ↦ by
    have := he.u_comp_v (e a); rw [he.idem] at this; exact this
  have hvue : ∀ a : G, v (e a ◇ e a) = e a := fun a ↦ by
    have := he.v_comp_u (e a); rw [he.idem] at this; exact this
  rw [@Law4443.models_iff]
  intro x y
  exact aux546_4443 h e v _ heh hvh he.idem he.comm_v huve hvue (fun a b ↦ rfl) x y

end Law.MagmaLaw

import equational_theories.Definability.IdempotentPower

/-!
# Witnesses named by an equation instead of by a term

`Definability/PositiveTermsFin.lean` proves a cell by exhibiting one term that defines the target in
every finite model of the source at once. Most of the cells still open cannot be proved that way,
and not because the search was too shallow: on source `546` the definition of `332` is the midpoint
`(x + y) / 2`, which is `x ◇ (y ◇ x)` in one five-element model of the law and `(y ◇ y) ◇ x` in
another. No single term is the witness, so no amount of prover time spent on single terms will do.

What is uniform across the models is not the term but an *equation* it solves. Fix a term `g` with a
hole -- one built from `x`, `y` and a placeholder -- and a binary term `t`. Substituting into the
hole makes `g` act on binary term functions, and on a finite carrier that action has finite orbits,
so the sequence `t`, `g(t)`, `g(g(t)), …` runs into a cycle. When the action is injective the cycle
is the whole orbit and `g` is a permutation of it, so

    g^{j+1}(w) = t

has a solution `w` in the orbit for every `j` -- again a term, since everything in the orbit is one.
The witness is that `w`. Its depth is whatever the orbit length in this particular magma makes it,
which is exactly the freedom `TermDefinableFromFin` grants and `TermDefinableFrom` does not, and its
defining property is an equation that does not mention the magma at all. So a cell splits into two
prover questions, both unit equational and both settled by twee:

* is `a ↦ g(x, y, a)` injective, so that a solution exists; and
* does *every* solution of `g^{j+1}(w) = t` satisfy the target?

`Function.exists_pos_period_iterate` of `Definability/IdempotentPower.lean` supplies the orbit, and
injectivity turns its eventual period into a genuine one: `g^p` is the identity on the nose, so
`w = g^{n}(t)` for `n = mp - (j+1)` is the solution, and `hiter` names it syntactically.

This is a different device from the idempotent power of that file, and a strictly more useful one.
There the witness is the limit of the orbit, `e = u^[N]`, whose defining axioms (`e ∘ e = e` and the
rest) are too weak to prove anything -- the file proves no cell. Here the witness is a point of the
orbit a fixed distance *before* it closes up, and its defining property is an equation between
magma terms, which is precisely what an equational prover can use.
-/

open FirstOrder FirstOrder.Language
open Law
open Law.MagmaLaw

namespace Law.MagmaLaw

variable {G : Type}

/-- A term in `x`, `y` and a hole: the shape of an orbit step. Variable `2` is the hole. -/
abbrev HTerm (G : Type) := (MagmaLanguage.withConstants (∅ : Set G)).Term (Fin 3)

/-- Fill the hole of `g` with the binary term `t`. -/
def happ (g : HTerm G) (t : BTerm G) : BTerm G :=
  g.subst ![Term.var 0, Term.var 1, t]

/-- `g` applied `n` times to `t`, filling the hole each time. For each fixed `n` this is an honest
term; `n` is chosen after the magma, which is what the finite flavour allows. -/
def hiter (g : HTerm G) (n : ℕ) (t : BTerm G) : BTerm G := (happ g)^[n] t

section Realize

variable [MagmaLanguage[[(∅ : Set G)]].Structure G]

/-- The binary function a two-variable term denotes. -/
def bfun (t : BTerm G) : G → G → G := fun x y ↦ t.realize ![x, y]

/-- The map on binary functions that filling the hole of `g` induces. -/
def hfun (g : HTerm G) : (G → G → G) → (G → G → G) :=
  fun F x y ↦ g.realize ![x, y, F x y]

theorem bfun_happ (g : HTerm G) (t : BTerm G) : bfun (happ g t) = hfun g (bfun t) := by
  funext x y
  show (g.subst ![Term.var 0, Term.var 1, t]).realize ![x, y] = _
  rw [Term.realize_subst]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

theorem bfun_hiter (g : HTerm G) (n : ℕ) (t : BTerm G) :
    bfun (hiter g n t) = (hfun g)^[n] (bfun t) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [show hiter g (k + 1) t = happ g (hiter g k t) from Function.iterate_succ_apply' _ _ _,
      bfun_happ, ih, Function.iterate_succ_apply']

/-- A step that is injective at every pair is injective on binary functions. -/
theorem injective_hfun (g : HTerm G) (h : ∀ x y : G, Function.Injective fun a ↦
    g.realize ![x, y, a]) : Function.Injective (hfun g) := by
  intro F₁ F₂ hF
  funext x y
  exact h x y (congrFun (congrFun hF x) y)

omit [MagmaLanguage[[(∅ : Set G)]].Structure G] in
/-- **The orbit is a cycle.** An injective self-map of a finite type has a positive power that is
the identity, so every point comes back to itself. -/
theorem exists_pos_iterate_eq_self [Finite G] {f : (G → G → G) → (G → G → G)}
    (hf : Function.Injective f) : ∃ p : ℕ, 0 < p ∧ f^[p] = id := by
  obtain ⟨i, p, hp, hper⟩ := Function.exists_pos_period_iterate f
  refine ⟨p, hp, ?_⟩
  funext a
  show f^[p] a = a
  refine (hf.iterate i) ?_
  show f^[i] (f^[p] a) = f^[i] a
  rw [← Function.iterate_add_apply]
  exact congrFun (hper i le_rfl) a

/-- **The solution exists and is a term.** With the step injective, `g^{j+1}(w) = t` is solved by
`w = g^{n}(t)` for an `n` that the magma chooses. -/
theorem exists_hiter_iterate [Finite G] (g : HTerm G) (t : BTerm G) (j : ℕ)
    (hg : Function.Injective (hfun g)) :
    ∃ n : ℕ, (hfun g)^[j + 1] (bfun (hiter g n t)) = bfun t := by
  obtain ⟨p, hp, hid⟩ := exists_pos_iterate_eq_self hg
  refine ⟨p * (j + 1) - (j + 1), ?_⟩
  have hle : j + 1 ≤ p * (j + 1) := Nat.le_mul_of_pos_left (j + 1) hp
  rw [bfun_hiter, ← Function.iterate_add_apply,
    show j + 1 + (p * (j + 1) - (j + 1)) = p * (j + 1) by omega, Function.iterate_mul]
  -- `f^[p]` is the identity, so any number of rounds of it is too
  rw [hid, Function.iterate_id, id_eq]

end Realize

/-- The `MagmaLanguage[[∅]]`-realization of a hole term in a magma. -/
abbrev hsem (M : Magma G) (g : HTerm G) (x y a : G) : G :=
  @Term.realize _ G M.FOStructure₀ _ ![x, y, a] g

/-- The `MagmaLanguage[[∅]]`-realization of a binary term in a magma. -/
abbrev bsem (M : Magma G) (t : BTerm G) (x y : G) : G :=
  @Term.realize _ G M.FOStructure₀ _ ![x, y] t

/-- **The glue.** On a finite magma, to term-define `L` it is enough to give a hole term `g`, a
binary term `t` and an offset `j` such that filling the hole is injective, and such that *every*
binary function `w` with `g^{j+1}(w) = t` satisfies `L`. The defining term is `g` iterated at the
orbit length of this particular magma, so it is chosen after the magma. -/
theorem termDefinableOnMagma_of_orbit [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G) (g : HTerm G) (t : BTerm G) (j : ℕ)
    (hinj : ∀ x y : G, Function.Injective fun a ↦ hsem M g x y a)
    (hsat : ∀ w : G → G → G,
      (∀ x y, (@hfun G M.FOStructure₀ g)^[j + 1] w x y = bsem M t x y) →
      @satisfies _ G ⟨w⟩ L) :
    TermDefinableOnMagma L M := by
  letI := M.FOStructure₀
  obtain ⟨n, hn⟩ := exists_hiter_iterate (G := G) g t j (injective_hfun g hinj)
  refine ⟨⟨bfun (hiter g n t)⟩, hsat _ (fun x y ↦ congrFun (congrFun hn x) y), ⟨hiter g n t, ?_⟩⟩
  funext w
  have hw : ![w 0, w 1] = w := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  show bfun (hiter g n t) (w 0) (w 1) = _
  show Term.realize ![w 0, w 1] (hiter g n t) = _
  rw [hw]

/-- The `TermDefinableFromFin` wrapper. `g`, `t` and `j` are chosen uniformly; the iteration count,
and so the defining term, is chosen after the magma. -/
theorem termDefinableFromFin_of_orbit {β : Type} {L L' : Law.MagmaLaw β} (j : ℕ)
    (g : ∀ G : Type, HTerm G) (t : ∀ G : Type, BTerm G)
    (hinj : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ x y : G, Function.Injective fun a ↦ hsem M (g G) x y a)
    (hsat : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ w : G → G → G,
        (∀ x y, (@hfun G M.FOStructure₀ (g G))^[j + 1] w x y = bsem M (t G) x y) →
        @satisfies _ G ⟨w⟩ L) :
    TermDefinableFromFin L L' :=
  fun {G} _ M hM ↦
    termDefinableOnMagma_of_orbit M (g G) (t G) j (hinj G M hM) (hsat G M hM)

/-! ### What the prover is handed

`hsat` gives a superposition prover an opaque `w` and one equation about it. That is enough in
principle and useless in practice: the equation buries `w` under `j+1` copies of `g`, and there is
no rule that peels them off. What the proofs actually use is the *inverse* of the hole map, which
finiteness supplies for free -- injective on a finite carrier is bijective -- as a pair of unit
equations that superposition can rewrite with in either direction. -/

/-- The magma operation on hole terms. -/
abbrev hmul (a b : HTerm G) : HTerm G := Functions.apply₂ (Sum.inl ()) a b

/-- The magma operation on binary terms, for writing down the base of an orbit. -/
abbrev bmul (a b : BTerm G) : BTerm G := Functions.apply₂ (Sum.inl ()) a b

/-- **The hole map inverts.** Filling the hole is injective, hence surjective, hence has a
two-sided inverse -- one for each pair `(x, y)`, chosen together. -/
theorem exists_hinv [Finite G] (M : Magma G) (g : HTerm G)
    (hinj : ∀ x y : G, Function.Injective fun a ↦ hsem M g x y a) :
    ∃ gi : G → G → G → G, (∀ x y a : G, hsem M g x y (gi x y a) = a) ∧
      (∀ x y a : G, gi x y (hsem M g x y a) = a) := by
  choose gi hgi using fun x y c ↦ Finite.injective_iff_surjective.mp (hinj x y) c
  exact ⟨gi, hgi, fun x y a ↦ hinj x y (hgi x y _)⟩

/-- The orbit equation, written out. `hfun` iterates on binary *functions*; a prover reads the
same statement pointwise, as `g` nested `n` deep around `w x y`. -/
theorem hfun_iterate_apply (M : Magma G) (g : HTerm G) (w : G → G → G) (n : ℕ) (x y : G) :
    (@hfun G M.FOStructure₀ g)^[n] w x y = (fun a ↦ hsem M g x y a)^[n] (w x y) := by
  induction n generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

end Law.MagmaLaw

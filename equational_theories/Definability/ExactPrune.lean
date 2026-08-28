import equational_theories.Definability.ExactAut
import equational_theories.Definability.Prune

/-!
# Exact-automorphism refutations by pruned search

`Definability/ExactAut.lean` turns a conjugacy class of subgroup `H ≤ Sₙ` into a rectangle of
non-structurality facts: a structural companion has *exactly* the automorphisms of the model it
came from, so the laws with a model whose automorphism group is exactly `H` are not structural over
the laws with none. Every instance of that so far -- `ExactAut4.lean`, `ExactAut6S56.lean` -- writes
the exact class out member by member, which stops at a few thousand members.

The class this file is built for has `98,496` members inside an invariant family of `139,968`, and
it is worth `127,198` cells, more than the whole first `Fin 6` pass. Neither number can be listed.
What can be done instead is what `Definability/Prune.lean` does for the one-sided obstruction: walk
the family as a tree, one orbit value at a time, and let a violated instance of the target law kill
a subtree. Measured over the `1,375` target laws of that class the whole search is `144,058` nodes,
median `78` per law.

The one thing `Prune.lean` does not have is exactness. Its leaves are "a full invariant table
satisfying the law", and here a full invariant table is a counterexample only if its automorphism
group is not strictly bigger than `H` -- a table admitting one of the excess permutations `X` lies
in some other class and says nothing. So the leaf test gains a disjunct, `Magma.admitsP`, and a
leaf that exhibits an `X j` prunes exactly like a violated instance. Since a permutation is
exhibited by the *filled cells*, the test is sound on partial tables too, which is why it can be
stated once at the leaf and never re-checked.

The source side needs no search: one member of the class is exhibited, and `Magma.tupOK` is the
decidable statement that a transport tuple is in the class at all.

## Contents

* `Magma.anyFin` -- `∃ x : Fin n` unrolled, the dual of `Magma.allFin`;
* `Magma.admitsP` and `Magma.isEndo_of_admitsP` -- a partial table exhibiting an endomorphism;
* `Magma.searchY` and `Magma.searchY_sound` -- `Magma.searchA` with the exactness leaf;
* `Magma.tupOK` -- membership of the exact class, as a test on a transport tuple;
* `Magma.not_satisfies_of_searchY` -- what one search certificate proves;
* `Law.MagmaLaw.not_structuralFromFin_of_tupOK` -- the rectangle.
-/

open Law Law.MagmaLaw FreeMagma

namespace Magma

variable {α : Type*} {n m k kX : ℕ}

/-! ### Exhibiting an endomorphism on a partial table -/

/-- `∃ x : Fin n, f x`, unrolled the way `Magma.allFin` unrolls the universal quantifier. -/
def anyFin : (n : ℕ) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, f => f 0 || anyFin n fun i ↦ f i.succ

theorem anyFin_iff : ∀ {n : ℕ} {f : Fin n → Bool}, anyFin n f = true ↔ ∃ x, f x = true
  | 0, _ => ⟨fun h ↦ absurd h (by simp [anyFin]), fun ⟨x, _⟩ ↦ x.elim0⟩
  | n + 1, f => by
    simp only [anyFin, Bool.or_eq_true, anyFin_iff]
    refine ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
    · rcases h with h | ⟨i, hi⟩
      · exact ⟨0, h⟩
      · exact ⟨i.succ, hi⟩
    · cases x using Fin.cases with
      | zero => exact Or.inl hx
      | succ i => exact Or.inr ⟨i, hx⟩

/-- Whether the filled part of `t` already exhibits `p` as an endomorphism. An unfilled cell makes
the test fail, so `true` is a statement about every completion of `t` at once -- which is what lets
the exactness test be paid at a leaf and never revisited. -/
def admitsP (t : Array (Option (Fin n))) (p : Fin n → Fin n) : Bool :=
  allFin n fun x ↦ allFin n fun y ↦
    match tget t x y with
    | none => false
    | some a => tget t (p x) (p y) == some (p a)

theorem isEndo_of_admitsP {q : Fin n → Fin n → Fin n} {t : Array (Option (Fin n))}
    {p : Fin n → Fin n} (hc : ∀ x y c, tget t x y = some c → q x y = c)
    (h : admitsP t p = true) : (Magma.mk q).IsEndo p := by
  simp only [admitsP, allFin_iff] at h
  intro x y
  have hxy := h x y
  show p (q x y) = q (p x) (p y)
  split at hxy
  · exact absurd hxy (by simp)
  · next a ha =>
    have hb : tget t (p x) (p y) = some (p a) := by simpa using hxy
    rw [hc x y a ha]
    exact (hc _ _ _ hb).symm

/-! ### The search -/

/-- `Magma.searchA` with one more way for a branch to die: a leaf whose table exhibits one of the
excess permutations `X` has an automorphism group strictly bigger than the one intended, so it is
not a member of the exact class and refutes nothing. -/
def searchY (E : Fin k → Fin n → Fin n) (L : Law.MagmaLaw α) (X : Fin kX → Fin n → Fin n) :
    List ((Fin m × List (Fin n)) × List ((Fin n × Fin n) × Fin k)) →
      Array (Option (Fin n)) → List (α → Fin n) → Bool
  | [], t, envs => (sift (tget t) L envs).isNone || anyFin kX fun j ↦ admitsP t (X j)
  | (p, cs) :: rest, t, envs =>
      match sift (tget t) L envs with
      | none => true
      | some envs' => p.2.all fun x ↦ searchY E L X rest (fill E cs x t) envs'

/-- **The search is sound.** If it succeeds then no way of filling the orbits still to be assigned
gives an operation which satisfies the law *and* admits no `X j`. -/
theorem searchY_sound {E : Fin k → Fin n → Fin n} {tr : Fin n → Fin n → Fin m × Fin k}
    {L : Law.MagmaLaw α} {X : Fin kX → Fin n → Fin n} :
    ∀ (todo : List ((Fin m × List (Fin n)) × List ((Fin n × Fin n) × Fin k)))
      (t : Array (Option (Fin n))) (envs : List (α → Fin n)),
      searchY E L X todo t envs = true →
      ∀ w : Fin m → Fin n,
        (∀ x y c, tget t x y = some c → transport E tr w x y = c) →
        (∀ q ∈ todo, w q.1.1 ∈ q.1.2) →
        (∀ q ∈ todo, ∀ p ∈ q.2, tr p.1.1 p.1.2 = (q.1.1, p.2)) →
        (∀ j, ¬ (Magma.mk (transport E tr w)).IsEndo (X j)) →
        ¬ @satisfies α (Fin n) (Magma.mk (transport E tr w)) L := by
  intro todo
  induction todo with
  | nil =>
    intro t envs hs w hc _ _ hX
    have hs' : ((sift (tget t) L envs).isNone || anyFin kX fun j ↦ admitsP t (X j)) = true := hs
    rcases Bool.or_eq_true_iff.mp hs' with h1 | h2
    · obtain ⟨φ, hφ⟩ := sift_eq_none envs (Option.isNone_iff_eq_none.mp h1)
      exact not_satisfies_of_violated hc hφ
    · obtain ⟨j, hj⟩ := anyFin_iff.mp h2
      exact absurd (isEndo_of_admitsP hc hj) (hX j)
  | cons q rest ih =>
    obtain ⟨⟨i, d⟩, cs⟩ := q
    intro t envs hs w hc h₁ h₂ hX
    rcases hsi : sift (tget t) L envs with _ | envs'
    · obtain ⟨φ, hφ⟩ := sift_eq_none envs hsi
      exact not_satisfies_of_violated hc hφ
    · rw [searchY, hsi] at hs
      exact ih (fill E cs (w i) t) envs'
        (List.all_eq_true.mp hs (w i) (h₁ _ List.mem_cons_self)) w
        (fill_compat cs (h₂ _ List.mem_cons_self) t hc)
        (fun q hq ↦ h₁ q (List.mem_cons_of_mem _ hq))
        (fun q hq ↦ h₂ q (List.mem_cons_of_mem _ hq)) hX

/-! ### Membership of the exact class -/

/-- Whether a transport tuple names a member of the exact class: every orbit value is invariant,
the operation it builds admits every `E i`, and no excess permutation is an automorphism of it.

The middle conjunct is what makes this the *class* and not merely the tuple space. It is not
implied by the first -- `Magma.orbitOK` constrains the representatives, invariance is a statement
about all `n ^ 2` cells -- and the target search does not need it, but a source exhibit does, and
paying for it here means a source costs one `decide` and no lemma. -/
def tupOK (E : Fin k → Fin n → Fin n) (tr : Fin n → Fin n → Fin m × Fin k) (z : Fin m → Fin k)
    (st : Fin m → Fin k → Fin k) (X : Fin kX → Fin n → Fin n) (w : Fin m → Fin n) : Bool :=
  allFin m (fun i ↦ orbitOK E z st i (w i)) &&
    (allFin k (fun i ↦ isEndoFin (transport E tr w) (E i)) &&
      allFin kX fun j ↦ !isEndoFin (transport E tr w) (X j))

theorem tupOK_orbit {E : Fin k → Fin n → Fin n} {tr : Fin n → Fin n → Fin m × Fin k}
    {z : Fin m → Fin k} {st : Fin m → Fin k → Fin k} {X : Fin kX → Fin n → Fin n}
    {w : Fin m → Fin n} (h : tupOK E tr z st X w = true) (i : Fin m) :
    orbitOK E z st i (w i) = true :=
  allFin_iff.mp (Bool.and_eq_true_iff.mp h).1 i

theorem tupOK_isEndo {E : Fin k → Fin n → Fin n} {tr : Fin n → Fin n → Fin m × Fin k}
    {z : Fin m → Fin k} {st : Fin m → Fin k → Fin k} {X : Fin kX → Fin n → Fin n}
    {w : Fin m → Fin n} (h : tupOK E tr z st X w = true) (i : Fin k) :
    (Magma.mk (transport E tr w)).IsEndo (E i) :=
  isEndoFin_iff.mp (allFin_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1 i)

theorem tupOK_notEndo {E : Fin k → Fin n → Fin n} {tr : Fin n → Fin n → Fin m × Fin k}
    {z : Fin m → Fin k} {st : Fin m → Fin k → Fin k} {X : Fin kX → Fin n → Fin n}
    {w : Fin m → Fin n} (h : tupOK E tr z st X w = true) (j : Fin kX) :
    ¬ (Magma.mk (transport E tr w)).IsEndo (X j) := by
  have := allFin_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2 j
  rw [Bool.not_eq_true'] at this
  exact isEndoFin_eq_false_iff.mp this

/-- **What one search certificate proves**: no member of the exact class satisfies `L`. The
hypotheses on `ord` are the same non-hypotheses as in `Prune.lean` -- an `ord` that omits an orbit
or repeats one only makes the search harder to pass. -/
theorem not_satisfies_of_searchY {E : Fin k → Fin n → Fin n} {tr : Fin n → Fin n → Fin m × Fin k}
    {z : Fin m → Fin k} {st : Fin m → Fin k → Fin k} {X : Fin kX → Fin n → Fin n}
    {L : Law.MagmaLaw α} {envs : List (α → Fin n)} {ord : List (Fin m)}
    (hs : searchY E L X
      (ord.map fun i ↦ ((i, (List.finRange n).filter (orbitOK E z st i ·)), cells tr i))
      (Array.replicate (n * n) none) envs = true)
    (w : Fin m → Fin n) (hw : tupOK E tr z st X w = true) :
    ¬ @satisfies α (Fin n) (Magma.mk (transport E tr w)) L := by
  refine searchY_sound (tr := tr) _ _ _ hs w (fun x y c hc ↦ absurd hc (by simp))
    (fun q hq ↦ ?_) (fun q hq p hp ↦ ?_) (tupOK_notEndo hw)
  · obtain ⟨i, -, hi⟩ := List.mem_map.mp hq
    subst hi
    exact List.mem_filter.mpr ⟨List.mem_finRange _, tupOK_orbit hw i⟩
  · obtain ⟨i, -, hi⟩ := List.mem_map.mp hq
    subst hi
    exact tr_of_mem_cells hp

/-! ### Fewer assignments -/

/-- A tuple read as an `n`-ary numeral, least significant first. Only used to order tuples. -/
def tcode (n : ℕ) : List (Fin n) → ℕ
  | [] => 0
  | x :: t => x.1 + n * tcode n t

/-- `Magma.envs`, cut down to (at most) one assignment per orbit of the group generated by `E`.

Every member of the family this file searches is invariant under each `E i`, so an instance of the
law is violated at `φ` exactly when it is violated at `E i ∘ φ`, and keeping one assignment per
orbit loses nothing. Nothing is *required* of an assignment list -- `Magma.searchY` is sound for any
list -- so this needs no correctness lemma; a wrong reduction would only fail to close a law.

Keeping the tuples minimal in `Magma.tcode` among their images keeps at least the orbit minimum, so
the reduction is a reduction and not a loss. It is computed rather than emitted: the alternative is
a list literal with `8,051` entries in the six-variable case, in a module `native_decide` recompiles
once per target law. -/
def envsRed (n : ℕ) [NeZero n] (E : Fin k → Fin n → Fin n) (j : ℕ) : List (ℕ → Fin n) :=
  ((tuples n j).filter fun t ↦ allFin k fun i ↦ decide (tcode n t ≤ tcode n (t.map (E i)))).map
    fun t i ↦ t.getD i 0

end Magma

namespace Law.MagmaLaw

variable {n m k kX : ℕ}

/-- **The exact-`Aut` rectangle, with the target side certified by search.** `E` generates the
group, `X` are the excess permutations that pin it down from above, and `Magma.tupOK` is membership
of the exact class. If `L'` has a member `v` of the class as a model and no member of the class
satisfies `L`, then `L` is not structural from `L'`, even over finite carriers.

The point of the subtype in `htgt` is that it is exactly what a pruned search certifies: the family
is far too large to index by `Fin m → Fin n` and far too large to list, but each of its members is
refuted by `Magma.not_satisfies_of_searchY` from a single `native_decide` per target law.

Everything but `hsrc` and `htgt` is a `decide` on a concrete carrier. -/
theorem not_structuralFromFin_of_tupOK {L L' : Law.NatMagmaLaw}
    (E Einv : Fin k → Fin n → Fin n) (X Xinv : Fin kX → Fin n → Fin n)
    (rep : Fin m → Fin n × Fin n) (tr : Fin n → Fin n → Fin m × Fin k)
    (z : Fin m → Fin k) (st : Fin m → Fin k → Fin k)
    (hl : ∀ i, Function.LeftInverse (Einv i) (E i))
    (hr : ∀ i, Function.RightInverse (Einv i) (E i))
    (hxl : ∀ j, Function.LeftInverse (Xinv j) (X j))
    (hxr : ∀ j, Function.RightInverse (Xinv j) (X j))
    (htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧ E (tr x y).2 (rep (tr x y).1).2 = y)
    (hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i))
    (hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j))
    (v : Fin m → Fin n) (hv : Magma.tupOK E tr z st X v = true)
    (hsrc : @satisfies _ (Fin n) (Magma.mk (Magma.transport E tr v)) L')
    (htgt : ∀ u : {w : Fin m → Fin n // Magma.tupOK E tr z st X w = true},
      ¬ @satisfies _ (Fin n) (Magma.mk (Magma.transport E tr u.1)) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.mk (Magma.transport E tr v)) hsrc
  have hE' : ∀ i, M'.IsEndo (E i) := fun i ↦
    Magma.IsEndo.of_definable (e := ⟨E i, Einv i, hl i, hr i⟩) hfwd (Magma.tupOK_isEndo hv i)
  have hX' : ∀ j, ¬ M'.IsEndo (X j) := fun j hj ↦
    Magma.tupOK_notEndo hv j
      (Magma.IsEndo.of_definable (e := ⟨X j, Xinv j, hxl j, hxr j⟩) hback hj)
  have hop : M'.op = Magma.transport E tr (fun i ↦ M'.op (rep i).1 (rep i).2) :=
    Magma.op_eq_transport (rep := rep) hE' htr
  have hmk : Magma.mk (Magma.transport E tr fun i ↦ M'.op (rep i).1 (rep i).2) = M' := by
    rw [← hop, Magma.mk_op]
  -- the value at a representative transports to itself, so each orbit value is invariant
  have hfix : ∀ i, E (z i) (M'.op (rep i).1 (rep i).2) = M'.op (rep i).1 (rep i).2 := by
    intro i
    have h1 := congrFun (congrFun hop (rep i).1) (rep i).2
    simp only [Magma.transport, hz i] at h1
    exact h1.symm
  have hok : ∀ i, Magma.orbitOK E z st i (M'.op (rep i).1 (rep i).2) := by
    intro i
    simp only [Magma.orbitOK, decide_eq_true_eq]
    intro j
    rw [hfix i]
    have h2 := hE' j (rep i).1 (rep i).2
    rw [congrFun (congrFun hop (E j (rep i).1)) (E j (rep i).2)] at h2
    simpa only [Magma.transport, hst i j] using h2
  have hu : Magma.tupOK E tr z st X (fun i ↦ M'.op (rep i).1 (rep i).2) = true := by
    refine Bool.and_eq_true_iff.mpr ⟨Magma.allFin_iff.mpr hok,
      Bool.and_eq_true_iff.mpr ⟨Magma.allFin_iff.mpr fun i ↦ ?_, Magma.allFin_iff.mpr fun j ↦ ?_⟩⟩
    · rw [Magma.isEndoFin_iff, hmk]
      exact hE' i
    · rw [Bool.not_eq_true', Magma.isEndoFin_eq_false_iff, hmk]
      exact hX' j
  exact htgt ⟨_, hu⟩ (by rw [hmk]; exact hM')

end Law.MagmaLaw

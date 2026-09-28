import equational_theories.Spectrum.Equation63.Singular
import equational_theories.Spectrum.Status
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# An obstruction to Bennett's published construction at order 90

Lemma 5.46 of *Quasigroup Identities and Mendelsohn Designs* (1989) claims
that the singular product 16 = 5*(4-1)+1 contains a five-point subquasigroup.
Every allowed four-point C₃ fiber instead has constant diagonal at the
shared point. Its three-cycles force every nonempty closed subset of the
product to have cardinality 1 modulo 3. Thus that intermediate claim is false.

See `docs/63_order90.md` for the source definition, a hand proof of the
four-point classification, and the distinction between this obstruction and
nonexistence at order 90. The index/complement operations are arbitrary in
`singular_closed_card_mod_three`, so the obstruction is independent of them.
-/
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Spectrum.E63.BennettObstruction
variable {A : Type*}

abbrev E229 (op : A → A → A) : Prop := ∀ x y, op (op x (op x y)) x = y

private theorem right_injective [Finite A] {op : A → A → A}
    (h : E229 op) (x : A) : Function.Injective (fun y => op y x) := by
  apply Finite.injective_iff_surjective.mpr
  intro y
  exact ⟨op x (op x y), h x y⟩

private theorem own_cube [Finite A] {op : A → A → A}
    (h : E229 op) (x : A) : op x (op x (op x x)) = x := by
  apply right_injective h x
  exact h x (op x x)

private theorem square_commutes [Finite A] {op : A → A → A}
    (h : E229 op) (x : A) : op (op x x) x = op x (op x x) := by
  simpa only [own_cube h x] using h x (op x (op x x))

/-- A cubic permutation with one fixed point has order 1 modulo 3. -/
private theorem card_of_cube [Fintype A] (f : Function.End A) (c : A)
    (hf : f ^ 3 ^ 1 = 1) (fixed : ∀ x, f x = x ↔ x = c) :
    Fintype.card A % 3 = 1 := by
  classical
  let e : f.fixedPoints ≃ Unit := {
    toFun := fun _ => Unit.unit
    invFun := fun _ => ⟨c, (fixed c).mpr rfl⟩
    left_inv := fun x => Subtype.ext ((fixed x.val).mp x.property).symm
    right_inv := fun _ => rfl }
  have hm := Equiv.Perm.card_fixedPoints_modEq hf
  rw [Fintype.card_congr e] at hm
  simpa only [Nat.ModEq, Fintype.card_unique] using hm

/-- A finite E229 quasigroup whose squares all equal `c` has order 1 modulo 3. -/
theorem card_mod_three [Fintype A] {op : A → A → A} (h : E229 op)
    (c : A) (hd : ∀ x, op x x = c) : Fintype.card A % 3 = 1 := by
  classical
  have comm (x : A) : op c x = op x c := by
    simpa only [hd] using square_commutes h x
  let f : Function.End A := op c
  have hf : f ^ 3 ^ 1 = 1 := by
    funext x
    change op c (op c (op c x)) = x
    rw [comm]
    exact h c x
  have fixed (x : A) : f x = x ↔ x = c := by
    constructor
    · intro hx
      have he := own_cube h x
      rw [hd x, ← comm x] at he
      change op x (f x) = x at he
      rw [hx, hd x] at he
      exact he.symm
    · intro hx
      subst x
      exact hd c
  exact card_of_cube f c hf fixed

/-- Any closed nonempty subset inherits the same congruence obstruction. -/
theorem closed_card_mod_three [Fintype A] {op : A → A → A} (h : E229 op)
    (c : A) (hd : ∀ x, op x x = c) (S : Finset A) (hne : S.Nonempty)
    (hclosed : ∀ x ∈ S, ∀ y ∈ S, op x y ∈ S) : S.card % 3 = 1 := by
  classical
  obtain ⟨x,hx⟩ := hne
  have hc : c ∈ S := hd x ▸ hclosed x hx x hx
  let sop (x y : S) : S := ⟨op x y, hclosed x x.property y y.property⟩
  have hs : E229 sop := fun x y => Subtype.ext (h x y)
  have hd' (x : S) : sop x x = ⟨c,hc⟩ := Subtype.ext (hd x)
  simpa only [Fintype.card_coe] using card_mod_three hs ⟨c,hc⟩ hd'

/-- Every pointed four-element C₃ quasigroup has constant diagonal. -/
theorem c3_four_diagonal {A : Type*} [Fintype A] (hc : Fintype.card A = 4)
    (op : A → A → A) (hcomm : ∀ x y, op x y = op y x)
    (h3 : ∀ x y, op x (op x (op x y)) = y)
    (c : A) (hcc : op c c = c) (x : A) : op x x = c := by
  classical
  obtain ⟨a,b,d,e,hab,had,hae,hbd,hbe,hde,he⟩ := Finset.card_eq_four.mp hc
  have cover (y : A) : y = a ∨ y = b ∨ y = d ∨ y = e := by
    have hm : y ∈ Finset.univ := Finset.mem_univ y
    rw [he] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have inj (y z w : A) (h : op y z = op y w) : z = w := by
    have hh := congrArg (fun t => op y (op y t)) h
    simpa only [h3] using hh
  have cop (y z : A) : op y z = a ∨ op y z = b ∨ op y z = d ∨ op y z = e := cover _
  have := cover c
  have := cover x
  -- Ground the cubic law at all sixteen pairs of the four-element universe.
  -- `grind` produces an ordinary kernel-checked proof, not a solver axiom.
  have := h3 a a
  have := h3 a b
  have := h3 a d
  have := h3 a e
  have := h3 b a
  have := h3 b b
  have := h3 b d
  have := h3 b e
  have := h3 d a
  have := h3 d b
  have := h3 d d
  have := h3 d e
  have := h3 e a
  have := h3 e b
  have := h3 e d
  have := h3 e e
  grind (splits := 1000) (gen := 8) (ematch := 20)

/-- Every nonempty closed subset of Lindner's singular product with a
constant-diagonal C₃ fiber has size 1 modulo 3. The index and complement are
arbitrary: only the fiber operation enters the orbit-counting argument. -/
theorem singular_closed_card_mod_three {V B : Type*} [Fintype V] [Fintype B]
    [DecidableEq V] (v : V → V → V) (q : Option B → Option B → Option B)
    (b : B → B → B) (hcomm : ∀ x y, q x y = q y x)
    (h3 : ∀ x y, q x (q x (q x y)) = y) (hd : ∀ x, q x x = none)
    (S : Finset (Option (V × B))) (hne : S.Nonempty)
    (hclosed : ∀ x ∈ S, ∀ y ∈ S, singularOp v q b x y ∈ S) : S.card % 3 = 1 := by
  classical
  let t := singularOp v q b
  have diag (x) : t x x = none := by
    cases x with
    | none => rfl
    | some p => rcases p with ⟨i,a⟩; simp [t, singularOp, hd, embed]
  obtain ⟨x,hx⟩ := hne
  have hc : none ∈ S := diag x ▸ hclosed x hx x hx
  have fiber (i : V) (a : Option B) : t none (embed i a) = embed i (q none a) :=
    singular_embed v q b (hd none) i none a
  have cube (x) : t none (t none (t none x)) = x := by
    cases x with
    | none => rfl
    | some p =>
      rcases p with ⟨i,a⟩
      change t none (t none (t none (embed i (some a)))) = embed i (some a)
      rw [fiber, fiber, fiber, h3]
  have fixed_q (a) (ha : q none a = a) : a = none := by
    have he := h3 a a
    rw [hd a, hcomm a none, ha, hd a] at he
    exact he.symm
  have embed_inj (i : V) : Function.Injective (embed (B := B) i) := by
    intro a c he
    cases a <;> cases c <;> simp_all [embed]
  have fixed_t (x) : t none x = x ↔ x = none := by
    constructor
    · intro he
      cases x with
      | none => rfl
      | some p =>
        rcases p with ⟨i,a⟩
        change t none (embed i (some a)) = embed i (some a) at he
        rw [fiber] at he
        have hh := fixed_q (some a) (embed_inj i he)
        cases hh
    · rintro rfl
      rfl
  let f : Function.End S := fun x => ⟨t none x, hclosed none hc x x.property⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    funext x
    exact Subtype.ext (cube x)
  have fixed (x : S) : f x = x ↔ x = ⟨none,hc⟩ := by
    constructor
    · intro he
      exact Subtype.ext ((fixed_t x).mp (congrArg Subtype.val he))
    · intro he
      subst x
      rfl
  simpa only [Fintype.card_coe] using card_of_cube f ⟨none,hc⟩ hf fixed

/-- The sixteen-point singular product claimed in Bennett (1989), Lemma 5.46,
cannot contain a five-point subquasigroup. This covers every choice of the
pointed four-element C₃ factor, not just an enumerated multiplication table.
It does not exclude other sixteen-point models or models of order ninety. -/
theorem singular_no_five (v : Fin 5 → Fin 5 → Fin 5)
    (q : Option (Fin 3) → Option (Fin 3) → Option (Fin 3)) (b : Fin 3 → Fin 3 → Fin 3)
    (hcomm : ∀ x y, q x y = q y x)
    (h3 : ∀ x y, q x (q x (q x y)) = y) (h0 : q none none = none)
    (S : Finset (Option (Fin 5 × Fin 3))) (hcard : S.card = 5)
    (hclosed : ∀ x ∈ S, ∀ y ∈ S, singularOp v q b x y ∈ S) : False := by
  have hd := c3_four_diagonal (by simp : Fintype.card (Option (Fin 3)) = 4)
    q hcomm h3 none h0
  have hn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hm := singular_closed_card_mod_three v q b hcomm h3 hd S hn hclosed
  omega

spectrum_assert card_mod_three complete
spectrum_assert c3_four_diagonal complete
spectrum_assert singular_closed_card_mod_three complete
spectrum_assert singular_no_five complete

end Spectrum.E63.BennettObstruction

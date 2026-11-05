import equational_theories.Parastrophes.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate

/-!
# A finite right-unital crossed magma is a quasigroup

Suppose `x * e = x` and `x * (y * x) = e * y`, and write `f x = e * x`.
Rotating the second identity shows that f is an endomorphism. Its fibre over e
is a singleton. These two observations alone do not assert cancellation.

Instead, take a smallest image H of an iterate of f. On this finite submagma,
f is bijective; the crossed identity then makes every column bijective on H.
Given any a, solve `b * f^n(a) = e` inside H and lift b through f^n on H.
The singleton fibre of f^n over e gives a left inverse of a in H. Applying
the crossed identity once more expresses a as f of an element of H. Thus f
is surjective on the entire carrier, and both translations are bijective.

This is a finite argument with no enumeration and no assumption that f has
some fixed, order-independent period. It is useful for E481's division image.
-/
namespace Parastrophes.FiniteCrossedIdentity

/-- An iterate of a map on a finite set has a range on which the map is onto. -/
private theorem stable_range {G : Type*} [Finite G] (f : G → G) :
    ∃ n, ∀ y ∈ Set.range (f^[n]), ∃ x ∈ Set.range (f^[n]), f x = y := by
  classical
  letI := Fintype.ofFinite G
  let S (n : ℕ) : Finset G := Finset.univ.image (f^[n])
  have hex : ∃ k, ∃ n, (S n).card = k := ⟨(S 0).card, 0, rfl⟩
  obtain ⟨n, hn⟩ := Nat.find_spec hex
  have hsub : S (n + 1) ⊆ S n := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨f x, Finset.mem_univ _, rfl⟩
  have heq : S n = S (n + 1) := Finset.eq_of_subset_of_card_le hsub
    (by rw [hn]; exact Nat.find_min' hex ⟨n + 1, rfl⟩) |>.symm
  refine ⟨n, ?_⟩
  intro y hy
  have hy' : y ∈ S n := by simpa [S] using hy
  rw [heq] at hy'
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy'
  exact ⟨f^[n] x, ⟨x, rfl⟩, (Function.iterate_succ_apply' f n x).symm.trans hx⟩

/-- Right identity and the crossed identity force both translations to be
bijective on a finite carrier. -/
theorem quasigroup {G : Type*} [Finite G] (M : Magma G) (e : G)
    (unit : ∀ x, M.op x e = x)
    (cross : ∀ x y, M.op x (M.op y x) = M.op e y) : IsQuasigroup M := by
  let f := M.op e
  have fe : f e = e := unit e
  have rotate (x y : G) : M.op (M.op x y) (f x) = f y := by
    change M.op (M.op x y) (M.op e x) = M.op e y
    rw [← cross y x]
    exact cross (M.op x y) y
  have endo : Function.Semiconj₂ f M.op M.op := by
    intro x y
    exact (rotate y (M.op x y)).symm.trans (congrArg (fun z => M.op z (f y)) (cross y x))
  have fibre (x : G) (hx : f x = e) : x = e := by
    have h := cross x e
    change M.op x (f x) = f e at h
    simpa only [hx, fe, unit] using h
  have fibre_iterate (n : ℕ) (x : G) (hx : f^[n] x = e) : x = e := by
    induction n generalizing x with
    | zero => exact hx
    | succ n ih => exact fibre x (ih (f x) hx)
  obtain ⟨n, hn⟩ := stable_range f
  let H := Set.range (f^[n])
  have he : e ∈ H := ⟨e, Function.iterate_fixed fe n⟩
  have hm {a b : G} (ha : a ∈ H) (hb : b ∈ H) : M.op a b ∈ H := by
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨M.op x y, endo.iterate n x y⟩
  have hf {a : G} (ha : a ∈ H) : f a ∈ H := hm he ha
  let F : H → H := fun a => ⟨f a, hf a.2⟩
  have hFs : Function.Surjective F := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hn y.1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hFi : Function.Injective F := Finite.injective_iff_surjective.mpr hFs
  have hcol (a : H) : Function.Surjective (fun b : H =>
      (⟨M.op b.1 a.1, hm b.2 a.2⟩ : H)) := by
    apply Finite.surjective_of_injective
    intro b c hbc
    apply hFi
    apply Subtype.ext
    have hh := congrArg (fun z : H => M.op a.1 z.1) hbc
    simpa only [cross] using hh
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨b, hb⟩ := hcol ⟨f^[n] a, ⟨a, rfl⟩⟩ ⟨e, he⟩
    obtain ⟨c, hc⟩ := hFs.iterate n b
    have hFn (k : ℕ) (x : H) : (F^[k] x).1 = f^[k] x.1 := by
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact congrArg f ih
    have hc' : f^[n] c.1 = b.1 := (hFn n c).symm.trans (congrArg Subtype.val hc)
    have hzero : M.op c.1 a = e := by
      apply fibre_iterate n
      rw [endo.iterate n, hc']
      exact congrArg Subtype.val hb
    refine ⟨c.1, ?_⟩
    have hh := cross a c.1
    rw [hzero, unit] at hh
    exact hh.symm
  have hi : Function.Injective f := Finite.injective_iff_surjective.mpr hs
  constructor
  · intro x
    have hr : Function.Surjective (M.op x) := by
      intro y
      obtain ⟨z, rfl⟩ := hs y
      exact ⟨M.op z x, cross x z⟩
    exact ⟨Finite.injective_iff_surjective.mpr hr, hr⟩
  · intro x
    have hr : Function.Injective (fun y => M.op y x) := by
      intro a b hab
      apply hi
      simpa only [cross] using congrArg (M.op x) hab
    exact ⟨hr, Finite.surjective_of_injective hr⟩

end Parastrophes.FiniteCrossedIdentity

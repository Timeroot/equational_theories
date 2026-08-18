import equational_theories.Definability.Certificates
import equational_theories.Equations.All

/-!
# Fixed-point-free involutions

A symmetry certificate that needs almost nothing from the target law. Suppose the source `L'` has
a model `M` on `G` carrying an automorphism `e` with `e ∘ e = id` and *no fixed point*. Any
operation definable from `M` inherits `e` as an automorphism, so to refute definability it is
enough to show that every model of the target `L` with an involutive automorphism has a fixed
point -- a statement about `L` alone, with the source nowhere in it.

The target side is a one-line argument whenever `L` proves `W x y = W y x` for some binary term
`W`: the element `c = W a (e a)` satisfies

  `e c = W (e a) (e (e a)) = W (e a) a = W a (e a) = c`,

the middle step being involutivity and the last being the symmetry of `W`. So a *single* commuting
term in the target, plus a *single* fixed-point-free involution in the source, refutes
`DefinableFrom` -- and therefore `TermDefinableFrom` too -- over both finite and arbitrary magmas.

Here the target is equation `4482`, `x ◇ (y ◇ y) = (y ◇ y) ◇ x`, whose commuting term is
`W x y = (x ◇ x) ◇ (y ◇ y)`: substituting `x ◇ x` for `x` in the law is already the symmetry. The
three sources each have a model on `Fin 8` with the translation `x ↦ x + 1` of `GF(8)`, i.e.
`Fin.xorPerm8 1`, as an automorphism; that permutation is a product of four transpositions, so it
is involutive and fixed-point-free.
-/

open Law Law.MagmaLaw

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- **Fixed-point-free obstruction.** If `L'` has a model with a fixed-point-free automorphism `e`,
but every model of `L` admitting `e` has an `e`-fixed point, then `L` is not definable from `L'`.
-/
theorem not_definableFrom_of_fixedPointFree {G : Type} (M : Magma G) (hM : @satisfies _ G M L')
    {e : G ≃ G} (he : M.IsEndo ⇑e) (hfpf : ∀ a : G, e a ≠ a)
    (hL : ∀ M' : Magma G, @satisfies _ G M' L → M'.IsEndo ⇑e → ∃ c : G, e c = c) :
    ¬ L.DefinableFrom L' :=
  not_definableFrom_of_isAuto M hM he fun M' hM' hendo ↦
    let ⟨c, hc⟩ := hL M' hM' hendo
    hfpf c hc

end Law.MagmaLaw

namespace Magma

/-- The target side for equation `4482`: `W x y = (x ◇ x) ◇ (y ◇ y)` is commutative, so `W a (f a)`
is fixed by any involutive endomorphism `f`. Note that `f` is not asked to be an automorphism, and
that a single point `a` of the carrier is all the input needed. -/
theorem exists_fixed_of_4482 {G : Type} (M : Magma G) (h : @Equation4482 G M) {f : G → G}
    (hf : ∀ a : G, f (f a) = a) (hendo : M.IsEndo f) (a : G) : ∃ c : G, f c = c := by
  refine ⟨M.op (M.op a a) (M.op (f a) (f a)), ?_⟩
  rw [hendo, hendo, hendo, hf]
  exact h (M.op (f a) (f a)) a

/-- A model of equation `3342`, `x ◇ y = y ◇ (x ◇ (x ◇ x))`, on `Fin 8`. -/
@[implicit_reducible]
def fpfCert3342 : Magma (Fin 8) :=
  ⟨![![4, 6, 0, 3, 6, 5, 4, 7],
     ![7, 5, 2, 1, 4, 7, 6, 5],
     ![6, 4, 1, 6, 1, 7, 0, 2],
     ![5, 7, 7, 0, 6, 0, 3, 1],
     ![0, 2, 1, 7, 1, 6, 6, 4],
     ![3, 1, 6, 0, 7, 0, 5, 7],
     ![4, 7, 6, 5, 0, 3, 4, 6],
     ![6, 5, 4, 7, 2, 1, 7, 5]]⟩

/-- A model of equation `3545`, `x ◇ y = y ◇ ((x ◇ x) ◇ x)`, on `Fin 8`. -/
@[implicit_reducible]
def fpfCert3545 : Magma (Fin 8) :=
  ⟨![![6, 4, 4, 3, 6, 5, 0, 7],
     ![5, 7, 2, 5, 4, 7, 6, 1],
     ![0, 6, 5, 6, 4, 2, 5, 7],
     ![7, 1, 7, 4, 3, 5, 6, 4],
     ![6, 5, 0, 7, 6, 4, 4, 3],
     ![4, 7, 6, 1, 5, 7, 2, 5],
     ![4, 2, 5, 7, 0, 6, 5, 6],
     ![3, 5, 6, 4, 7, 1, 7, 4]]⟩

/-- A model of equation `4415`, `x ◇ (x ◇ y) = (z ◇ x) ◇ x`, on `Fin 8`. -/
@[implicit_reducible]
def fpfCert4415 : Magma (Fin 8) :=
  ⟨![![5, 2, 5, 5, 0, 5, 2, 3],
     ![3, 4, 4, 4, 4, 1, 2, 3],
     ![5, 4, 7, 4, 7, 7, 2, 7],
     ![5, 4, 5, 6, 6, 6, 6, 3],
     ![0, 4, 7, 6, 0, 7, 0, 0],
     ![5, 1, 7, 6, 6, 1, 1, 1],
     ![2, 2, 2, 6, 0, 1, 2, 1],
     ![3, 3, 7, 3, 0, 1, 0, 3]]⟩

theorem fpfCert3342_satisfies : @Equation3342 (Fin 8) fpfCert3342 := by decide!

theorem fpfCert3545_satisfies : @Equation3545 (Fin 8) fpfCert3545 := by decide!

theorem fpfCert4415_satisfies : @Equation4415 (Fin 8) fpfCert4415 := by decide!

theorem fpfCert3342_isEndo : fpfCert3342.IsEndo ⇑(Fin.xorPerm8 1) := by decide!

theorem fpfCert3545_isEndo : fpfCert3545.IsEndo ⇑(Fin.xorPerm8 1) := by decide!

theorem fpfCert4415_isEndo : fpfCert4415.IsEndo ⇑(Fin.xorPerm8 1) := by decide!

/-- Translation by `1` in `GF(8)` has no fixed point. -/
theorem xorPerm8_one_ne (a : Fin 8) : Fin.xorPerm8 1 a ≠ a := by revert a; decide

/-- Translation by `1` in `GF(8)` is an involution. -/
theorem xorPerm8_one_involutive (a : Fin 8) : Fin.xorPerm8 1 (Fin.xorPerm8 1 a) = a :=
  Fin.xor8_self 1 a

end Magma

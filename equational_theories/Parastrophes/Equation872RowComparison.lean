import equational_theories.Parastrophes.Equation872ImageBasis

/-!
# Comparing the two square rows in E872's division image

Put `c(x)=x*((x*x)*x)`. Every actual image has `c(c(z))=z*z`, so the
cross identity can use `c(c(z))*y` as its outer row index and `(z*z)*y`
as its inner row index. This gives the 24-operation identity `Matched`.

It forces every row to be surjective, even on an infinite carrier. First,
all rows indexed by `c(c(z))*y` are onto. This includes the row at `c³(z)`;
that row is itself one of the indexing rows, so its range covers all indices.
Finiteness then gives row bijectivity.

The converse nevertheless fails on six elements. The checked table below
satisfies `Matched` but violates E614 at 0. Its rows 0 and 3 coincide, and
cancellation of rows does not permit cancellation of their indices.

The 26-operation variant `Prefixed` applies a further arbitrary left
translation to both compared indices. It excludes this counterexample.
Only its forward implication is proved here: no characterization attribute
is attached to either candidate.
-/
namespace Parastrophes.Eq872RowComparison
open Law Eq872Image

def Matched {G : Type} (D : Magma G) : Prop := ∀ x y z,
  x = D.op (D.op (core D (core D z)) y)
    (D.op (core D x) (D.op (D.op (D.op z z) y) x))

def Prefixed {G : Type} (D : Magma G) : Prop := ∀ x y z w,
  x = D.op (D.op w (D.op (core D (core D z)) y))
    (D.op (core D x) (D.op (D.op w (D.op (D.op z z) y)) x))

theorem matched_of_image {G : Type} (D : Magma G)
    (h : InImage Law872 .left D) : Matched D := by
  obtain ⟨M, hm, hd⟩ := h
  have hb := forward M D hd ((@Law872.models_iff G M).mp hm)
  intro x y z
  rw [core_core_eq_square D ⟨M, hm, hd⟩ z]
  exact hb.2 x (D.op (D.op z z) y)

theorem prefixed_of_image {G : Type} (D : Magma G)
    (h : InImage Law872 .left D) : Prefixed D := by
  obtain ⟨M, hm, hd⟩ := h
  have hb := forward M D hd ((@Law872.models_iff G M).mp hm)
  intro x y z w
  rw [core_core_eq_square D ⟨M, hm, hd⟩ z]
  exact hb.2 x (D.op w (D.op (D.op z z) y))

/-- A range argument supplies every row, not just the displayed outer rows. -/
theorem rows_surjective {G : Type} (D : Magma G) (h : Matched D) :
    ∀ a, Function.Surjective (D.op a) := by
  have hs (z y : G) : Function.Surjective (D.op (D.op (core D (core D z)) y)) :=
    fun x => ⟨_, (h x y z).symm⟩
  have hc (z : G) : Function.Surjective (D.op (core D (core D (core D z)))) := by
    exact hs z (D.op (D.op (core D (core D z)) (core D (core D z)))
      (core D (core D z)))
  intro a
  obtain ⟨y, hy⟩ := hc a a
  have hh := hs (core D a) y
  rw [hy] at hh
  exact hh

theorem left_quasigroup_fin {G : Type} [Finite G] (D : Magma G)
    (h : Matched D) : IsSideQuasigroup .left D := by
  intro a
  have hs := rows_surjective D h a
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

@[implicit_reducible] def bad : Magma (Fin 6) := ⟨fun x y =>
  (![![1, 2, 5, 4, 3, 0], ![3, 5, 2, 0, 4, 1], ![3, 1, 4, 0, 2, 5],
      ![1, 2, 5, 4, 3, 0], ![0, 5, 2, 3, 4, 1], ![2, 1, 0, 3, 4, 5]] :
    Fin 6 → Fin 6 → Fin 6) x y⟩

theorem bad_matched : Matched bad := by unfold Matched; decide

theorem bad_not_unit : ¬ @Equation614 (Fin 6) bad := by decide

theorem bad_not_image : ¬ InImage Law872 .left bad := by
  intro h
  exact bad_not_unit ((characterizes_fin bad).mpr h).1

theorem bad_not_prefixed : ¬ Prefixed bad := by
  intro h
  have he := h 0 0 0 0
  exact (by decide : (0 : Fin 6) ≠ 3) he

end Parastrophes.Eq872RowComparison

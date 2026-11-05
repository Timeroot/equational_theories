import equational_theories.Parastrophes.Equation872RowComparison

/-!
# A further E872 row comparison

The indices c(c(z))*y and (z*z)*y agree in every actual image. Apply an
arbitrary left translation and then an arbitrary right translation to both.
The resulting 28-operation candidate excludes the old six-element example.

Unlike the merely left-prefixed comparison, this candidate has a short proof
of row surjectivity. If T is the set of indices c(c(z))*y, then c³(z) belongs
to T. Put a=c³(z). Both a*a and (a*a)*a are in G*T, while (a*a)*a also lies
in (G*T)*G. The candidate makes every row indexed by (G*T)*G onto. The row
at (a*a)*a consequently supplies every possible index in (G*T)*G.

The converse is false: a different six-element example, checked below,
satisfies this stronger comparison but fails the unit identity. Consequently
no characterization attribute is attached.
-/
namespace Parastrophes.Eq872DoubleComparison
open Law Eq872Image

def Compared {G : Type} (D : Magma G) : Prop := ∀ x y z w v,
  x = D.op (D.op (D.op w (D.op (core D (core D z)) y)) v)
    (D.op (core D x) (D.op (D.op (D.op w (D.op (D.op z z) y)) v) x))

theorem of_image {G : Type} (D : Magma G) (h : InImage Law872 .left D) :
    Compared D := by
  obtain ⟨M, hm, hd⟩ := h
  have hb := forward M D hd ((@Law872.models_iff G M).mp hm)
  intro x y z w v
  rw [core_core_eq_square D ⟨M, hm, hd⟩ z]
  exact hb.2 x _

theorem rows_surjective {G : Type} (D : Magma G) (h : Compared D) :
    ∀ a, Function.Surjective (D.op a) := by
  have hs (y z w v : G) : Function.Surjective
      (D.op (D.op (D.op w (D.op (core D (core D z)) y)) v)) :=
    fun x => ⟨_, (h x y z w v).symm⟩
  intro t
  let a := core D (core D (core D t))
  let y := D.op (D.op (core D (core D t)) (core D (core D t)))
    (core D (core D t))
  have ha : D.op (core D (core D t)) y = a := rfl
  have hr : Function.Surjective (D.op (D.op (D.op a a) a)) := by
    simpa only [ha] using hs y t a a
  obtain ⟨v, hv⟩ := hr t
  have hh := hs y t (D.op a a) v
  simpa only [ha, hv] using hh

theorem left_quasigroup_fin {G : Type} [Finite G] (D : Magma G) (h : Compared D) :
    IsSideQuasigroup .left D := by
  intro x
  have hs := rows_surjective D h x
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

theorem excludes_old_example : ¬ Compared Eq872RowComparison.bad := by
  intro h
  have he := h 0 0 0 5 0
  exact (by decide : (0 : Fin 6) ≠ 4) he

/-- A second example: more row contexts still do not identify row indices. -/
@[implicit_reducible] def bad : Magma (Fin 6) := ⟨fun x y =>
  (![![1, 3, 0, 2, 5, 4], ![4, 2, 1, 3, 0, 5], ![3, 1, 2, 0, 5, 4],
      ![0, 2, 1, 3, 4, 5], ![1, 3, 0, 2, 5, 4], ![0, 2, 1, 3, 4, 5]] :
    Fin 6 → Fin 6 → Fin 6) x y⟩

private def rowTag (x : Fin 6) : Fin 4 := ![0,1,2,3,0,3] x

private theorem same_row (a b : Fin 6) (h : rowTag a = rowTag b) :
    bad.op a = bad.op b := by
  fin_cases a <;> fin_cases b <;> first | rfl | contradiction

private theorem context_tags : ∀ w v : Fin 6,
    rowTag (bad.op (bad.op w 0) v) = rowTag (bad.op (bad.op w 4) v) := by decide

private theorem compared_tags (y z w v : Fin 6) :
    rowTag (bad.op (bad.op w (bad.op (core bad (core bad z)) y)) v) =
      rowTag (bad.op (bad.op w (bad.op (bad.op z z) y)) v) := by
  fin_cases z <;> fin_cases y
  all_goals first | rfl | exact context_tags w v | exact (context_tags w v).symm

private theorem bad_cross : ∀ x y : Fin 6,
    x = bad.op y (bad.op (core bad x) (bad.op y x)) := by decide

/-- Only the exceptional row pair needs checking; the full five-variable
identity follows from row equality and the ordinary crossed identity. -/
theorem bad_compared : Compared bad := by
  intro x y z w v
  rw [same_row _ _ (compared_tags y z w v)]
  exact bad_cross x _

theorem bad_not_unit : ¬ @Equation614 (Fin 6) bad := by decide

theorem bad_not_image : ¬ InImage Law872 .left bad := by
  intro h
  exact bad_not_unit ((characterizes_fin bad).mpr h).1

end Parastrophes.Eq872DoubleComparison

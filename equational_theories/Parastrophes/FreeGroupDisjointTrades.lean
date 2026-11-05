import equational_theories.Parastrophes.FreeGroupTradeLabels

/-!
# A disjoint family of controlled noncommutative group trades

An old orbit has one protected point; a new orbit has none. Distinct new
orbits are separated by exponent sums at the larger of their fresh labels.
Thus all trades can be performed simultaneously. Later only finitely many
of them are needed to refute a given identity in a finite model.
-/
namespace Parastrophes.FreeGroupDisjointTrades
open FreeGroupWordCones FreeGroupTradeBlocks FreeGroupTradeLabels GroupTriangleTrades

abbrev Input := {x : Word × Word // Good x}
noncomputable def letter (x : Input) : Word := FreeGroup.of (label x.val)

theorem old_orbit_injective (x : Input) : Function.Injective (orbit x.val) := by
  apply orbit_injective
  · intro he
    have h := outside x.property.1 x.property.2 (label_pos x.val)
      (fresh_of_label_le x.val le_rfl).2 0 1 (Or.inr (by decide))
    have hx : ZeroCone (rotate x.val).1 := by rw [← he]; exact x.property.1
    exact h (by simpa [orbit,row] using hx)
  · intro he
    have h := outside x.property.1 x.property.2 (label_pos x.val)
      (fresh_of_label_le x.val le_rfl).2 0 2 (Or.inr (by decide))
    have hx : ZeroCone (rotate (rotate x.val)).1 := by rw [← he]; exact x.property.1
    exact h (by simpa [orbit,row] using hx)

/-- No original orbit meets a new orbit; two original orbits are identical
only when their designated protected inputs are identical. -/
theorem old_eq {x y : Input} {j i' j' : Fin 3}
    (he : orbit x.val j = orbit (row y.val (letter y) i') j') :
    i'=0 ∧ x=y ∧ j=j' := by
  obtain ⟨k,hk⟩ := orbit_back j j' he
  have hg : ZeroCone (orbit (row y.val (letter y) i') k).1 := by
    rw [← hk]
    exact x.property.1
  have hi' : i'=0 := by
    by_contra hi'
    exact outside y.property.1 y.property.2 (label_pos y.val)
      (fresh_of_label_le y.val le_rfl).2 i' k (Or.inl hi') hg
  subst i'
  have hk0 : k=0 := by
    by_contra hk0
    exact outside y.property.1 y.property.2 (label_pos y.val)
      (fresh_of_label_le y.val le_rfl).2 0 k (Or.inr hk0) hg
  subst k
  have hxy : x=y := Subtype.ext (by simpa [row,orbit] using hk)
  subst y
  exact ⟨rfl,rfl,old_orbit_injective x (by simpa [row] using he)⟩

theorem points_injective : Function.Injective (point (fun x : Input => x.val) letter) := by
  rintro ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ he
  change orbit (row x.val (letter x) i) j = orbit (row y.val (letter y) k) l at he
  by_cases hi : i=0
  · subst i
    have h := old_eq (by simpa [row] using he)
    rcases h with ⟨rfl,rfl,rfl⟩
    rfl
  by_cases hk : k=0
  · subst k
    have h := old_eq (by simpa [row] using he.symm)
    exact (hi h.1).elim
  rcases lt_trichotomy (label x.val) (label y.val) with hlt | heq | hgt
  · have hw := congrArg (fun z : Word × Word =>
        (weight (label y.val) z.1,weight (label y.val) z.2)) he
    change (weight (label y.val) (orbit (row x.val (FreeGroup.of (label x.val)) i) j).1,
      weight (label y.val) (orbit (row x.val (FreeGroup.of (label x.val)) i) j).2) =
      (weight (label y.val) (orbit (row y.val (FreeGroup.of (label y.val)) k) l).1,
      weight (label y.val) (orbit (row y.val (FreeGroup.of (label y.val)) k) l).2) at hw
    rw [point_weight_above x.val hlt,point_weight] at hw
    exact (mark_nonzero hk hw.symm).elim
  · have hxy : x=y := Subtype.ext (label_injective heq)
    subst y
    have hw := congrArg (fun z : Word × Word =>
        (weight (label x.val) z.1,weight (label x.val) z.2)) he
    change (weight (label x.val) (orbit (row x.val (FreeGroup.of (label x.val)) i) j).1,
      weight (label x.val) (orbit (row x.val (FreeGroup.of (label x.val)) i) j).2) =
      (weight (label x.val) (orbit (row x.val (FreeGroup.of (label x.val)) k) l).1,
      weight (label x.val) (orbit (row x.val (FreeGroup.of (label x.val)) k) l).2) at hw
    rw [point_weight,point_weight] at hw
    obtain ⟨rfl,rfl⟩ := mark_injective hi hk hw
    rfl
  · have hw := congrArg (fun z : Word × Word =>
        (weight (label x.val) z.1,weight (label x.val) z.2)) he
    change (weight (label x.val) (orbit (row x.val (FreeGroup.of (label x.val)) i) j).1,
      weight (label x.val) (orbit (row x.val (FreeGroup.of (label x.val)) i) j).2) =
      (weight (label x.val) (orbit (row y.val (FreeGroup.of (label y.val)) k) l).1,
      weight (label x.val) (orbit (row y.val (FreeGroup.of (label y.val)) k) l).2) at hw
    rw [point_weight,point_weight_above y.val hgt] at hw
    exact (mark_nonzero hi hw).elim

end Parastrophes.FreeGroupDisjointTrades

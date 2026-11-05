import equational_theories.Parastrophes.Equation1518
import equational_theories.Parastrophes.TranslationChains

/-!
# A square-root reparameterization of E1518

In finite E1518 magmas, squaring is bijective. If `r*r = y`, then
left division satisfies `y \\ x = x * (r*x)` and `y \\ y = r`.
Two further cancellations give E1518 for the division operation itself.
-/
namespace Parastrophes.Catalogue

theorem square_bijective1518 {G : Type} (M : Magma G) [Finite G]
    (h : @Equation1518 G M) : Function.Bijective (fun x => M.op x x) := by
  have hQ := leftQuasigroup1518_fin G M (inferInstance : Finite G)
    ((@Law1518.models_iff G M).mpr h)
  have hi : Function.Injective (fun x => M.op x x) := by
    intro x y he
    change M.op x x = M.op y y at he
    apply (hQ (M.op x x)).1
    rw [square_mul1518 M h x, he, square_mul1518 M h y]
  exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- The transfer needs only actual left division and surjectivity of squaring;
finiteness supplies the latter in the catalogue theorem below. -/
theorem division1518 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1518 G M)
    (hs : Function.Surjective (fun x => M.op x x)) : @Equation1518 G D := by
  intro x y
  obtain ⟨r, hr⟩ := hs y
  change M.op r r = y at hr
  have hy : D.op y x = M.op x (M.op r x) := by
    have he := congrArg (D.op y) (h x r)
    rw [hr, hd.2] at he
    exact he
  have hdiag : D.op y y = r := by
    have he := square_mul1518 M h r
    rw [hr] at he
    exact (congrArg (D.op y) he).symm.trans (hd.2 y r)
  change x = D.op (D.op y y) (D.op x (D.op y x))
  rw [hdiag, hy, hd.2, hd.2]

/-- Finite E1518 magmas are closed under left division, and every finite
E1518 magma is the left division of another E1518 magma. -/
@[parastrophe_result] theorem left_characterizes1518_fin :
    Characterizes .fin Law1518 .left Law1518 := by
  apply characterizes_of_division
  · exact leftQuasigroup1518_fin
  all_goals
    intro G M D hG hd h
    letI : Finite G := hG
    have hm := (@Law1518.models_iff G M).mp h
    exact (@Law1518.models_iff G D).mpr
      (division1518 M D hd hm (square_bijective1518 M hm).2)

end Parastrophes.Catalogue

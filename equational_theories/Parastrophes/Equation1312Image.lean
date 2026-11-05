import equational_theories.Parastrophes.CyclicImageShape

/-!
# E1312 in left-division notation

The source and its left division have the same square map. Right translation
in the division is the cube of right translation in the source, so those two
right translations commute. This gives a pure division identity preserving
each product fibre. These are necessary laws. The final section gives an exact quasiidentity
criterion with row bijectivity retained; it is not a pure equational basis.

The cyclic obstruction also shows that any single defining identity must be
`x=A*(B*x)`, up to reversing its sides, and the leftmost variable in A must
differ from x. Neither assertion closes the single-equation catalogue field.
-/
namespace Parastrophes.Eq1312Image
open Law FreeMagma Eq872ImageShape

section

variable {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
  (h : @Equation1312 G M)

include hd h

/-- Three cancellations in one instance of the source equation suffice. -/
theorem square_eq (x : G) : D.op x x = M.op x x := by
  have he := h (D.op x x) x
  simpa only [hd.1] using he

theorem division_formula (y x : G) :
    D.op y x = M.op (M.op (M.op y x) x) x := by
  have he := congrArg (D.op y) (h x y)
  simpa only [hd.2] using he

theorem right_commute (y x : G) :
    M.op (D.op y x) x = D.op (M.op y x) x := by
  rw [division_formula M D hd h, division_formula M D hd h]

theorem equation8 : @Equation8 G D := by
  intro x
  rw [square_eq M D hd h, hd.2]

/-- If x*y=t in division, translating both inputs on the right by t
preserves that product. No finiteness or column bijectivity is used. -/
theorem fibre_step (x y : G) :
    D.op (D.op x (D.op x y)) (D.op y (D.op x y)) = D.op x y := by
  have he := right_commute M D hd h x (D.op x y)
  rw [hd.1] at he
  rw [← he, hd.2]

omit hd h in
theorem image_equation8 (hi : InImage Law1312 .left D) : @Equation8 G D := by
  obtain ⟨M, hm, hd⟩ := hi
  exact equation8 M D hd ((@Law1312.models_iff G M).mp hm)

omit hd h in
private theorem cyclic (n : Nat) :
    @satisfies _ (ZMod n) (unshift n) Law1312 ↔ (2 : ZMod n) = 0 := by
  rw [@Law1312.models_iff (ZMod n) (unshift n)]
  constructor
  · intro hh
    have he := hh 0 0
    change (0 : ZMod n) = (0-1)-1 at he
    linear_combination he
  · intro hh x y
    change x = (x-1)-1
    linear_combination hh

omit hd h in
theorem target_shape {K : NatMagmaLaw} (hk : Characterizes .fin Law1312 .left K) :
    ∃ i t, (K = ⟨.Leaf i,t⟩ ∨ K = ⟨t,.Leaf i⟩) ∧
      rightmost t = i ∧ rightDepth t = 2 ∧ CyclicImageShape.leftmost t ≠ i := by
  apply CyclicImageShape.target_shape (by decide : 0 < 2) _ cyclic hk
  exact (@Law1312.models_iff Bool (rightProjection Bool)).mpr (fun _ _ => rfl)

omit hd h in
theorem two_step_shape {K : NatMagmaLaw} (hk : Characterizes .fin Law1312 .left K) :
    ∃ i a b, (K = ⟨.Leaf i,.Fork a (.Fork b (.Leaf i))⟩ ∨
      K = ⟨.Fork a (.Fork b (.Leaf i)),.Leaf i⟩) ∧ CyclicImageShape.leftmost a ≠ i := by
  obtain ⟨i,t,he,hr,hd,hl⟩ := target_shape hk
  cases t with
  | Leaf => simp [rightDepth] at hd
  | Fork a r =>
    cases r with
    | Leaf => simp [rightDepth] at hd
    | Fork b r =>
      cases r with
      | Leaf j =>
        change j = i at hr
        subst j
        exact ⟨i,a,b,he,hl⟩
      | Fork c r => simp [rightDepth] at hd


end

/-- Following two edges carrying the same division value forces the third
edge. This is a quasiidentity, not a single ordinary identity. -/
def Rotation {G : Type} (D : Magma G) : Prop :=
  ∀ a b c, D.op a b = D.op b c →
    D.op c (D.op a (D.op a b)) = D.op a b

/-- If a*b=b*c=t in division, the original right-translation chain is
 a -> b -> c. E1312 specifies its third step as a*t. -/
theorem rotation_forward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation1312 G M) : Rotation D := by
  intro a b c hab
  have he := h (D.op a b) a
  rw [hd.1] at he
  have hbc : M.op b (D.op a b) = c := by rw [hab, hd.1]
  rw [hbc] at he
  have hh := congrArg (D.op a) he
  rw [hd.2] at hh
  rw [hh, hd.2]

theorem rotation_backward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : Rotation D) : @Equation1312 G M := by
  intro x y
  have he := h y (M.op y x) (M.op (M.op y x) x) (by rw [hd.2, hd.2])
  rw [hd.2] at he
  have hh := congrArg (M.op (M.op (M.op y x) x)) he
  rw [hd.1] at hh
  have hh' := congrArg (M.op y) hh
  rw [hd.1] at hh'
  exact hh'

/-- A complete division-only criterion, retaining left bijectivity.
Unlike the earlier square and fibre identities, this has a proved converse. -/
theorem characterizes {G : Type} (D : Magma G) :
    InImage Law1312 .left D ↔ IsSideQuasigroup .left D ∧ Rotation D := by
  constructor
  · rintro ⟨M, hM, hd⟩
    exact ⟨sideQuasigroup_of_division (division_symm hd),
      rotation_forward M D hd ((@Law1312.models_iff G M).mp hM)⟩
  · rintro ⟨hq, hr⟩
    classical
    let e (x : G) := Equiv.ofBijective (D.op x) (hq x)
    let M : Magma G := ⟨fun x y => (e x).symm y⟩
    have hd : IsDivision .left M D :=
      ⟨fun x y => (e x).symm_apply_apply y, fun x y => (e x).apply_symm_apply y⟩
    exact ⟨M, (@Law1312.models_iff G M).mpr (rotation_backward M D hd hr), hd⟩

end Parastrophes.Eq1312Image

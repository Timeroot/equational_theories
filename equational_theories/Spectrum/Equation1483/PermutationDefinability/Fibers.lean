import equational_theories.Spectrum.Equation1483.PermutationDefinability.Basic

/-! Homomorphisms preserving the zero fiber preserve every base fiber and split
into two coordinate functions. For finite automorphisms the hypothesis follows
from the intrinsic minimum-rank characterization. -/
namespace Spectrum.E1483.PermutationDefinability.Data
variable {G S : Type} [Magma G] (D : Data G S)
variable (F : Point G S → Point G S)
  (hhom : ∀ X Y, F (D.operation X Y) = D.operation (F X) (F Y))
  (hz : ∀ u v, (F (D.zero, u, v)).1 = D.zero)

include hhom hz

theorem map_one (u v : S) : (F (D.one, u, v)).1 = D.one := by
  have he := congrArg Prod.fst (hhom
    (D.zero, u, D.B D.zero D.zero u)
    (D.zero, (D.A D.zero D.zero).symm v, v))
  simpa only [operation, D.constant, Equiv.symm_apply_apply, Equiv.apply_symm_apply, hz] using he

theorem first_independent (x : G) (u u' v : S) :
    (F (x, u, v)).1 = (F (x, u', v)).1 := by
  have he (s : S) := congrArg Prod.fst (hhom
    (D.one, v, D.B D.one (x ◇ D.one) s)
    (x ◇ D.one, (D.A D.one (x ◇ D.one)).symm v, v))
  simp only [operation, D.left_inverse, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    D.map_one F hhom hz] at he
  exact (he u).trans (he u').symm

theorem second_independent (x : G) (u v v' : S) :
    (F (x, u, v)).1 = (F (x, u, v')).1 := by
  have he (s : S) := congrArg Prod.fst (hhom
    (D.one ◇ x, u, D.B (D.one ◇ x) D.one u)
    (D.one, (D.A (D.one ◇ x) D.one).symm s, u))
  simp only [operation, D.right_inverse, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    D.map_one F hhom hz] at he
  exact (he v).trans (he v').symm

theorem fiber_constant (x : G) (u v u' v' : S) :
    (F (x, u, v)).1 = (F (x, u', v')).1 :=
  (D.first_independent F hhom hz x u u' v).trans
    (D.second_independent F hhom hz x u' v v')

omit hhom hz in
def baseMap (s : S) (x : G) : G := (F (x, s, s)).1

theorem map_base (s : S) (X : Point G S) : (F X).1 = baseMap F s X.1 :=
  D.fiber_constant F hhom hz X.1 X.2.1 X.2.2 s s

theorem baseMap_hom (s : S) (x y : G) :
    baseMap F s (x ◇ y) = baseMap F s x ◇ baseMap F s y := by
  have he := congrArg Prod.fst (hhom (x, s, s) (y, s, s))
  rw [D.map_base F hhom hz s] at he
  exact he

omit hhom in
theorem baseMap_zero (s : S) : baseMap F s D.zero = D.zero := hz s s

theorem baseMap_one (s : S) : baseMap F s D.one = D.one :=
  D.map_one F hhom hz s s

omit hhom hz in
def splice (Y Z X₁ X₂ : Point G S) : Point G S :=
  D.operation (D.operation Y X₁) (D.operation X₂ (D.operation Y Z))

omit hhom hz in
theorem splice_eq (Y Z X₁ X₂ : Point G S) (he : X₁.1 = X₂.1) :
    D.splice Y Z X₁ X₂ = (X₁.1, X₁.2.1, X₂.2.2) := by
  rcases X₁ with ⟨x, u, v⟩
  rcases X₂ with ⟨y, s, t⟩
  dsimp only at he
  subst y
  simpa only [splice, operation] using D.lawful (x, u, t) Y Z

omit hz in
theorem map_splice (Y Z X₁ X₂ : Point G S) :
    F (D.splice Y Z X₁ X₂) = D.splice (F Y) (F Z) (F X₁) (F X₂) := by
  simp only [splice, hhom]

omit hhom hz in
def leftMap (s : S) (x : G) (u : S) : S := (F (x, u, s)).2.1
omit hhom hz in
def rightMap (s : S) (x : G) (v : S) : S := (F (x, s, v)).2.2

/-- The rectangular splice makes the two fiber coordinates independent. -/
theorem map_split (s : S) (x : G) (u v : S) :
    F (x, u, v) = (baseMap F s x, leftMap F s x u, rightMap F s x v) := by
  let Z : Point G S := (D.zero, s, s)
  calc
    F (x, u, v) = F (D.splice Z Z (x, u, s) (x, s, v)) :=
      congrArg F (D.splice_eq Z Z (x, u, s) (x, s, v) rfl).symm
    _ = D.splice (F Z) (F Z) (F (x, u, s)) (F (x, s, v)) :=
      D.map_splice F hhom Z Z _ _
    _ = ((F (x, u, s)).1, (F (x, u, s)).2.1, (F (x, s, v)).2.2) := by
      apply D.splice_eq
      rw [D.map_base F hhom hz s, D.map_base F hhom hz s]
    _ = _ := by rw [D.map_base F hhom hz s]; rfl

/-- info: 'Spectrum.E1483.PermutationDefinability.Data.fiber_constant' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fiber_constant

end Spectrum.E1483.PermutationDefinability.Data

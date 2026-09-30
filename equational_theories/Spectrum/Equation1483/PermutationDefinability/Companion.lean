import equational_theories.Spectrum.Equation1483.PermutationDefinability.Fibers

/-! Every finite permutation cover of a constant-row E1483 base admits a
parameter-free first-order definable E1485 companion. -/
namespace Spectrum.E1483.PermutationDefinability.Data
variable {G S : Type} [Magma G] (D : Data G S)

def alpha (x : G) : S ≃ S :=
  (D.A D.zero x).trans (D.B D.one D.zero).symm

def beta (x : G) : S ≃ S := (D.B x D.zero).symm

def coordinates : Point G S ≃ Point G S where
  toFun X := (X.1, D.alpha X.1 X.2.1, D.beta X.1 X.2.2)
  invFun X := (X.1, (D.alpha X.1).symm X.2.1, (D.beta X.1).symm X.2.2)
  left_inv X := by simp only [Equiv.symm_apply_apply]
  right_inv X := by simp only [Equiv.apply_symm_apply]

def plainCompanion (X Y : Point G S) : Point G S :=
  (Constant.untwist D.one X.1 Y.1, X.2.2, Y.2.1)

def companion (X Y : Point G S) : Point G S :=
  D.coordinates.symm (D.plainCompanion (D.coordinates X) (D.coordinates Y))

theorem coordinates_companion (X Y : Point G S) :
    D.coordinates (D.companion X Y) =
      D.plainCompanion (D.coordinates X) (D.coordinates Y) :=
  D.coordinates.apply_symm_apply _

theorem plain_lawful (X Y Z : Point G S) :
    D.plainCompanion (D.plainCompanion Y X)
      (D.plainCompanion X (D.plainCompanion Z Y)) = X :=
  Prod.ext
    (Constant.untwist_eqn D.law D.zero D.one D.constant X.1 Y.1 Z.1) rfl

theorem companion_lawful (X Y Z : Point G S) :
    D.companion (D.companion Y X)
      (D.companion X (D.companion Z Y)) = X := by
  apply D.coordinates.injective
  simp only [D.coordinates_companion, D.plain_lawful]

section Maps
variable (F : Point G S → Point G S)
  (hhom : ∀ X Y, F (D.operation X Y) = D.operation (F X) (F Y))
  (hz : ∀ u v, (F (D.zero, u, v)).1 = D.zero)
include hhom hz

theorem beta_map (s : S) (x : G) (v : S) :
    D.beta (baseMap F s x) (rightMap F s x v) =
      leftMap F s D.one (D.beta x v) := by
  have he := congrArg (fun X : Point G S => X.2.1)
    (hhom (x, s, v) (D.zero, s, s))
  simp only [operation, D.column, D.map_split F hhom hz s,
    D.baseMap_zero F hz] at he
  exact he.symm

theorem alpha_map (s : S) (x : G) (u : S) :
    D.alpha (baseMap F s x) (leftMap F s x u) =
      leftMap F s D.one (D.alpha x u) := by
  have he := congrArg (fun X : Point G S => X.2.2)
    (hhom (D.zero, s, s) (x, u, s))
  simp only [operation, D.constant, D.map_split F hhom hz s,
    D.baseMap_zero F hz] at he
  have hb := D.beta_map F hhom hz s D.one (D.A D.zero x u)
  rw [D.baseMap_one F hhom hz s] at hb
  change (D.B D.one D.zero).symm
    (D.A D.zero (baseMap F s x) (leftMap F s x u)) = _
  rw [← he]
  exact hb

omit hhom hz in
def diagonal (s : S) (X : Point G S) : Point G S :=
  (baseMap F s X.1, leftMap F s D.one X.2.1, leftMap F s D.one X.2.2)

theorem coordinates_map (s : S) (X : Point G S) :
    D.coordinates (F X) = D.diagonal F s (D.coordinates X) := by
  rcases X with ⟨x, u, v⟩
  rw [D.map_split F hhom hz s]
  apply Prod.ext
  · rfl
  exact Prod.ext (D.alpha_map F hhom hz s x u) (D.beta_map F hhom hz s x v)

theorem baseMap_twist (s : S) (x : G) :
    baseMap F s (Constant.twist D.one x) =
      Constant.twist D.one (baseMap F s x) := by
  dsimp only [Constant.twist]
  rw [D.baseMap_hom F hhom hz s, D.baseMap_hom F hhom hz s,
    D.baseMap_one F hhom hz s]

theorem baseMap_untwist (s : S) (x y : G) :
    baseMap F s (Constant.untwist D.one x y) =
      Constant.untwist D.one (baseMap F s x) (baseMap F s y) := by
  dsimp only [Constant.untwist]
  rw [D.baseMap_hom F hhom hz s,
    D.baseMap_twist F hhom hz s, D.baseMap_twist F hhom hz s,
    D.baseMap_twist F hhom hz s]

theorem diagonal_plain (s : S) (X Y : Point G S) :
    D.diagonal F s (D.plainCompanion X Y) =
      D.plainCompanion (D.diagonal F s X) (D.diagonal F s Y) :=
  Prod.ext (D.baseMap_untwist F hhom hz s X.1 Y.1) rfl

theorem companion_map (s : S) (X Y : Point G S) :
    F (D.companion X Y) = D.companion (F X) (F Y) := by
  apply D.coordinates.injective
  calc
    D.coordinates (F (D.companion X Y)) =
        D.diagonal F s (D.coordinates (D.companion X Y)) :=
      D.coordinates_map F hhom hz s _
    _ = D.diagonal F s (D.plainCompanion (D.coordinates X) (D.coordinates Y)) := by
      rw [D.coordinates_companion]
    _ = D.plainCompanion (D.diagonal F s (D.coordinates X))
        (D.diagonal F s (D.coordinates Y)) := D.diagonal_plain F hhom hz s _ _
    _ = D.plainCompanion (D.coordinates (F X)) (D.coordinates (F Y)) := by
      rw [D.coordinates_map F hhom hz s X, D.coordinates_map F hhom hz s Y]
    _ = D.coordinates (D.companion (F X) (F Y)) := (D.coordinates_companion _ _).symm
end Maps

theorem companion_definable [Finite G] [Finite S] [Nonempty S] :
    Law.MagmaLaw.DefinableOnMagma Law1485 D.magma := by
  classical
  let N : Magma (Point G S) := ⟨D.companion⟩
  refine ⟨N, (@Law1485.models_iff (Point G S) N).mpr
    (fun X Y Z => (D.companion_lawful X Y Z).symm), ?_⟩
  apply Magma.definable_of_aut_invariant D.magma N.Graph
  intro F hbij hhom v hv
  have hz := D.map_zero F hbij hhom
  have hm := D.companion_map F hhom hz (Classical.choice ‹Nonempty S›)
  change D.companion (F (v (some 0))) (F (v (some 1))) = F (v none)
  rw [← hm]
  exact congrArg F hv

/-- info: 'Spectrum.E1483.PermutationDefinability.Data.companion_definable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms companion_definable

end Spectrum.E1483.PermutationDefinability.Data

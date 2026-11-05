import equational_theories.Parastrophes.SquareRoots
import equational_theories.Parastrophes.ImageBasis
import equational_theories.Parastrophes.TranslationChains

/-!
# A short exact basis for E467's finite left-division image

Put `c(x)=x*(x*x)`. The image is characterized by E411 and E7681,
`x=y*(y*(c(x)*y))`. The original multiplication is recovered as
`M(x,y)=D(x,D(c(y),x))`. A single-equation compression is proved in
`Equation467SingleImage.lean`.
-/
namespace Parastrophes.Eq467Image
open Law FreeMagma

def cube {G : Type} (M : Magma G) (x : G) := M.op x (M.op x x)

def Diagonal {G : Type} (M : Magma G) : Prop :=
  ∀ x, M.op x (M.op x (M.op x (M.op x x))) = x

def Cross {G : Type} (M : Magma G) : Prop :=
  ∀ x y, M.op y (M.op y (M.op (cube M x) y)) = x

def Basis {G : Type} (M : Magma G) : Prop := Diagonal M ∧ Cross M

/-- Inverting a four-step diagonal orbit preserves it. -/
theorem diagonal_division {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : Diagonal M) : Diagonal D := by
  intro x
  have he := congrArg (fun z => D.op x (D.op x (D.op x (D.op x z)))) (h x)
  simpa only [hd.2] using he.symm

/-- The midpoint of that orbit is unchanged by reversing its direction. -/
theorem cube_division {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : Diagonal M) (x : G) : cube D x = cube M x := by
  have he := congrArg (fun z => D.op x (D.op x z)) (h x)
  simpa only [hd.2, cube] using he.symm

theorem source_diagonal {G : Type} (M : Magma G)
    (h : @Equation467 G M) : Diagonal M := fun x => (h x x).symm

theorem forward {G : Type} [Finite G] (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation467 G M) : Basis D := by
  have hdiag := source_diagonal M h
  have hr : ∀ x, cube M (M.op x x) = x :=
    Catalogue.square_root467 M inferInstance ((@Law467.models_iff G M).mpr h)
  have hs (x : G) : M.op (cube M x) (cube M x) = x := rotate_finite hr x
  refine ⟨diagonal_division M D hd hdiag, ?_⟩
  intro x y
  have he := (h y (cube M x)).symm
  rw [hs] at he
  have hi := (leftWord_eq_iff hd [cube M x, y, y] x y).mp he
  simpa only [leftWord, List.reverse_cons, List.reverse_nil, List.foldr_cons,
    List.foldr_nil, List.append_assoc, List.nil_append, List.cons_append,
    cube_division M D hd hdiag] using hi

/-- Both identities are needed in the converse: the diagonal law identifies
the cubic map with its expression in multiplication. -/
theorem backward {G : Type} [Finite G] (M D : Magma G)
    (hd : IsDivision .left M D) (h : Basis D) : @Equation467 G M := by
  have hc (x : G) : cube M x = cube D x :=
    cube_division D M (division_symm hd) h.1 x
  have rot (x y : G) : M.op (cube D x) (M.op y (M.op y x)) = y := by
    have he := (leftWord_eq_iff (division_symm hd) [y, y, cube D x] y x).mp (h.2 x y)
    exact he
  have hs (x : G) : M.op (cube D x) (cube D x) = x := by
    have he := rot x x
    change M.op (cube D x) (cube M x) = x at he
    rwa [hc] at he
  have hr (x : G) : cube D (M.op x x) = x :=
    rotate_finite (f := fun x => M.op x x) (g := cube D) hs x
  intro x y
  have he := rot (M.op y y) x
  rw [hr] at he
  exact he.symm

theorem multiplication_eq {G : Type} [Finite G] (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation467 G M) (x y : G) :
    M.op x y = D.op x (D.op (cube D y) x) := by
  have he := congrArg (M.op x) ((forward M D hd h).2 y x)
  simpa only [hd.1] using he.symm

theorem characterizes_fin {G : Type} [Finite G] (D : Magma G) :
    Basis D ↔ InImage Law467 .left D := by
  constructor
  · intro h
    let M : Magma G := ⟨fun x y => D.op x (D.op (cube D y) x)⟩
    have he (x y : G) : D.op x (M.op x y) = y := h.2 y x
    have hi (x : G) : Function.Injective (D.op x) :=
      Finite.injective_iff_surjective.mpr (fun y => ⟨M.op x y, he x y⟩)
    have hd : IsDivision .left M D :=
      ⟨fun x y => hi x (he x (D.op x y)), he⟩
    exact ⟨M, (@Law467.models_iff G M).mpr (backward M D hd h), hd⟩
  · rintro ⟨M, h, hd⟩
    exact forward M D hd ((@Law467.models_iff G M).mp h)

/-- E7681 in `data/eq_size5.txt`. -/
def crossLaw : NatMagmaLaw :=
  ⟨Lf 0, Lf 1 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ Lf 1))⟩

private theorem crossLaw_iff {G : Type} (D : Magma G) :
    @satisfies _ G D crossLaw ↔ Cross D := by
  constructor
  · intro h x y; exact (h (fun n => if n = 0 then x else y)).symm
  · intro h v; exact (h (v 0) (v 1)).symm

/-- A two-equation basis, with a total of nine operations. This does not
assert that the pair compresses to a single equation. -/
@[parastrophe_basis] theorem left467_fin :
    CharacterizesBasis .fin Law467 .left [Law411, crossLaw] := by
  intro G D hG
  letI : Finite G := hG
  have hd : @satisfies _ G D Law411 ↔ Diagonal D := by
    rw [Law411.models_iff]
    exact ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩
  have hb : (∀ t ∈ [Law411, crossLaw], @satisfies _ G D t) ↔ Basis D := by
    simp [hd, crossLaw_iff, Basis]
  exact hb.trans (characterizes_fin D)

/-- `x + q*y` on F₂[q]/(q³+q+1). This is a quasigroup satisfying
E7681, but it fails the diagonal identity E411. -/
@[implicit_reducible] def crossOnly : Magma (Fin 8) :=
  ⟨fun x y => (![
    ![0, 2, 4, 6, 3, 1, 7, 5],
    ![1, 3, 5, 7, 2, 0, 6, 4],
    ![2, 0, 6, 4, 1, 3, 5, 7],
    ![3, 1, 7, 5, 0, 2, 4, 6],
    ![4, 6, 0, 2, 7, 5, 3, 1],
    ![5, 7, 1, 3, 6, 4, 2, 0],
    ![6, 4, 2, 0, 5, 7, 1, 3],
    ![7, 5, 3, 1, 4, 6, 0, 2]] : Fin 8 → Fin 8 → Fin 8) x y⟩

theorem crossOnly_cross : Cross crossOnly := by
  unfold Cross cube
  decide

theorem crossOnly_quasigroup : IsQuasigroup crossOnly := by
  unfold IsQuasigroup Function.Bijective Function.Injective Function.Surjective
  decide

theorem crossOnly_not_diagonal : ¬ Diagonal crossOnly := by
  intro h
  have he : (2 : Fin 8) = 1 := h 1
  exact (by decide : (2 : Fin 8) ≠ 1) he

/-- The extra diagonal condition cannot be dropped, even among finite
quasigroups. This refutes E7681 alone, not every possible single identity. -/
theorem crossOnly_not_image : ¬ InImage Law467 .left crossOnly := by
  intro h
  exact crossOnly_not_diagonal ((characterizes_fin crossOnly).mpr h).1

/-! A surviving compression candidate. Only its forward implication and
finite bijectivity consequences are proved here; the converse remains open. -/

def fourth {G : Type} (M : Magma G) (x : G) := M.op x (M.op x (cube M x))

def bridge {G : Type} (M : Magma G) (y z : G) :=
  M.op (fourth M z) (M.op z (M.op (cube M y) z))

/-- A fourteen-operation candidate for a single equation. -/
def Joined {G : Type} (M : Magma G) : Prop :=
  ∀ x y z, M.op y (M.op (bridge M y z) (M.op (cube M x) y)) = x

theorem joined_of_basis {G : Type} (M : Magma G) (h : Basis M) : Joined M := by
  have hb (y z : G) : bridge M y z = y := by
    unfold bridge fourth cube
    rw [h.1 z]
    exact h.2 y z
  intro x y z
  rw [hb]
  exact h.2 x y

/-- The candidate enforces bijectivity of the cubic map and of both sides
on finite carriers. No additional quasigroup hypothesis is needed. -/
theorem joined_bijective_fin {G : Type} [Finite G] (M : Magma G) (h : Joined M) :
    Function.Bijective (cube M) ∧ IsQuasigroup M := by
  have ci : Function.Injective (cube M) := by
    intro a b he
    have ha := h a a a
    have hb := h b a a
    rw [he] at ha
    exact ha.symm.trans hb
  have cs := Finite.surjective_of_injective ci
  refine ⟨⟨ci, cs⟩, ?_, ?_⟩
  · intro y
    have hs : Function.Surjective (M.op y) :=
      fun x => ⟨M.op (bridge M y y) (M.op (cube M x) y), h x y y⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro y
    have hi : Function.Injective (fun x => M.op x y) := by
      intro a b he
      obtain ⟨u, rfl⟩ := cs a
      obtain ⟨v, rfl⟩ := cs b
      change M.op (cube M u) y = M.op (cube M v) y at he
      have hu := h u y y
      have hv := h v y y
      rw [he] at hu
      exact congrArg (cube M) (hu.symm.trans hv)
    exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- The apparent second parameter in the bridge is redundant. Establishing
that this common map is the identity would finish the candidate's converse. -/
theorem joined_bridge_independent_fin {G : Type} [Finite G] (M : Magma G)
    (h : Joined M) (y z w : G) : bridge M y z = bridge M y w := by
  have hq := (joined_bijective_fin M h).2
  apply (hq.2 (M.op (cube M y) y)).1
  apply (hq.1 y).1
  exact (h y y z).trans (h y y w).symm

theorem basis_of_joined_bridge_fin {G : Type} [Finite G] (M : Magma G)
    (h : Joined M) (hf : ∀ x, bridge M x x = x) : Basis M := by
  have hb (y z : G) : bridge M y z = y :=
    (joined_bridge_independent_fin M h y z y).trans (hf y)
  have hc : Cross M := by
    intro x y
    simpa only [hb] using h x y y
  refine ⟨?_, hc⟩
  intro x
  have hq := (joined_bijective_fin M h).2
  apply (hq.2 (M.op x (M.op (cube M x) x))).1
  exact (hb x x).trans (hc x x).symm

end Parastrophes.Eq467Image

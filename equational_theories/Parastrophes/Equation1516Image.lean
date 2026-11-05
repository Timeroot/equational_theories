import equational_theories.Parastrophes.SquareRoots
import equational_theories.Parastrophes.TranslationChains

/-! A translation criterion for E1516's finite left-division image.

This is not yet a single-equation characterization: the converse explicitly
requires bijective rows. In particular, the short identity below must not be
registered as a characterization among all magmas.
-/
namespace Parastrophes.Eq1516Image
open Law

def turn {G : Type} (D : Magma G) (x : G) := D.op x (D.op x (D.op x x))

def cross {G : Type} (D : Magma G) (x y : G) := D.op y (D.op y (D.op x y))

def Common {G : Type} (D : Magma G) : Prop := ∀ x y, cross D x y = turn D x

def Fixed {G : Type} (D : Magma G) : Prop := ∀ x, D.op (turn D x) x = turn D x

/-- Each original square has the same inverse under every triple translation. -/
theorem cross_square {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation1516 G M) (x y : G) : cross D (M.op x x) y = x := by
  have he := congrArg (D.op (M.op x x)) (h y x)
  rw [hd.2] at he
  unfold cross
  rw [he, hd.2, hd.2]

theorem forward {G : Type} [Finite G] (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1516 G M) :
    Common D ∧ Fixed D := by
  have hg (x : G) : turn D (M.op x x) = x := cross_square M D hd h x (M.op x x)
  have hs (x : G) : M.op (turn D x) (turn D x) = x :=
    rotate_finite (f := turn D) (g := fun x => M.op x x) hg x
  constructor
  · intro x y
    rw [← hs x]
    exact (cross_square M D hd h (turn D x) y).trans (hg (turn D x)).symm
  · intro x
    have he := hd.2 (turn D x) (turn D x)
    rwa [hs] at he

/-- The criterion recovers the original law by reversing three row maps. -/
theorem backward {G : Type} [Finite G] (M D : Magma G)
    (hd : IsDivision .left M D) (hc : Common D) (hf : Fixed D) :
    @Equation1516 G M := by
  have hs (x : G) : M.op (turn D x) (turn D x) = x := by
    have he := congrArg (M.op (turn D x)) (hf x)
    rw [hd.1] at he
    exact he.symm
  have hg (x : G) : turn D (M.op x x) = x :=
    rotate_finite (f := fun x => M.op x x) (g := turn D) hs x
  intro x y
  have he := hc (M.op y y) x
  rw [hg] at he
  have hh := congrArg (fun z => M.op x (M.op x z)) he
  change M.op x (M.op x (D.op x (D.op x (D.op (M.op y y) x)))) = _ at hh
  rw [hd.1, hd.1] at hh
  have hh' := congrArg (M.op (M.op y y)) hh
  rw [hd.1] at hh'
  exact hh'

/-- An eight-operation identity valid in every image. Bijectivity remains
an essential explicit hypothesis of the converse proved here. -/
def Short {G : Type} (D : Magma G) : Prop :=
  ∀ x y z, D.op (cross D x y) (D.op x (cross D x z)) = x

theorem short_of_criterion {G : Type} (D : Magma G)
    (hq : IsSideQuasigroup .left D) (hc : Common D) (hf : Fixed D) : Short D := by
  have hp (x : G) : D.op (turn D x) (D.op x (turn D x)) = x := by
    apply (hq (turn D x)).1
    exact (hc x (turn D x)).trans (hf x).symm
  intro x y z
  rw [hc, hc, hp]

theorem criterion_of_short {G : Type} (D : Magma G)
    (hq : IsSideQuasigroup .left D) (h : Short D) : Common D ∧ Fixed D := by
  have hc : Common D := by
    intro x z
    apply (hq x).1
    apply (hq (cross D x x)).1
    exact (h x x z).trans (h x x x).symm
  refine ⟨hc, ?_⟩
  intro x
  have he := hc x (turn D x)
  change D.op (turn D x) (D.op (turn D x) (D.op x (turn D x))) = turn D x at he
  have hp := h x x x
  change D.op (turn D x) (D.op x (turn D x)) = x at hp
  rwa [hp] at he

theorem short_of_image {G : Type} [Finite G] (D : Magma G)
    (h : InImage Law1516 .left D) : Short D := by
  obtain ⟨M, hm, hd⟩ := h
  have hf := forward M D hd ((@Law1516.models_iff G M).mp hm)
  exact short_of_criterion D (sideQuasigroup_of_division (division_symm hd)) hf.1 hf.2

theorem characterizes_leftQuasigroups_fin {G : Type} [Finite G] (D : Magma G)
    (hq : IsSideQuasigroup .left D) : Short D ↔ InImage Law1516 .left D := by
  constructor
  · intro h
    classical
    let e (x : G) := Equiv.ofBijective (D.op x) (hq x)
    let M : Magma G := ⟨fun x y => (e x).symm y⟩
    have hd : IsDivision .left M D :=
      ⟨fun x y => (e x).symm_apply_apply y, fun x y => (e x).apply_symm_apply y⟩
    have hc := criterion_of_short D hq h
    exact ⟨M, (@Law1516.models_iff G M).mpr (backward M D hd hc.1 hc.2), hd⟩
  · exact short_of_image D

/-- The common-value map is bijective in every finite image: the source
square is its inverse. This is not a claim about division's square map. -/
theorem turn_bijective_fin {G : Type} [Finite G] (D : Magma G)
    (h : InImage Law1516 .left D) : Function.Bijective (turn D) := by
  obtain ⟨M, hm, hd⟩ := h
  have hm' := (@Law1516.models_iff G M).mp hm
  have hs : Function.Surjective (turn D) := fun x =>
    ⟨M.op x x, cross_square M D hd hm' x (M.op x x)⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

/-- For the two-identity proposal Common + Short, it suffices to settle one
unary cancellation question. A bad finite model necessarily has a collision
of turn, so searching such collisions covers every failure of that proposal.
The injectivity hypothesis is essential: `Equation1516CommonCounterexample`
constructs a 38-element model of the two identities in which turn has a
collision. -/
theorem characterizes_turn_injective_fin {G : Type} [Finite G] (D : Magma G) :
    (Common D ∧ Short D ∧ Function.Injective (turn D)) ↔
      InImage Law1516 .left D := by
  constructor
  · rintro ⟨hc, hs, hi⟩
    have ht := Finite.surjective_of_injective hi
    have hq : IsSideQuasigroup .left D := by
      intro y
      have onto : Function.Surjective (D.op y) := by
        intro x
        obtain ⟨z, rfl⟩ := ht x
        exact ⟨D.op y (D.op z y), hc z y⟩
      exact ⟨Finite.injective_iff_surjective.mpr onto, onto⟩
    exact (characterizes_leftQuasigroups_fin D hq).mp hs
  · intro h
    refine ⟨?_, short_of_image D h, (turn_bijective_fin D h).1⟩
    obtain ⟨M, hm, hd⟩ := h
    exact (forward M D hd ((@Law1516.models_iff G M).mp hm)).1

/-- The short identity by itself does not ensure bijectivity, even at order four. -/
@[implicit_reducible] def shortCounterexample : Magma (Fin 4) :=
  ⟨fun x y => (![![2,2,1,1], ![3,0,3,2], ![3,0,2,1], ![2,0,0,1]] :
    Fin 4 → Fin 4 → Fin 4) x y⟩

theorem shortCounterexample_short : Short shortCounterexample := by
  unfold Short cross
  decide

theorem shortCounterexample_not_image : ¬ InImage Law1516 .left shortCounterexample := by
  rintro ⟨M, _, hd⟩
  have hq := sideQuasigroup_of_division (division_symm hd)
  have he : (0 : Fin 4) = 1 := (hq 0).1 (a₁ := 0) (a₂ := 1) rfl
  exact (by decide : (0 : Fin 4) ≠ 1) he

end Parastrophes.Eq1516Image

import equational_theories.Parastrophes.TranslationChains

/-!
# A two-equation description of E872's finite left-division image

Put `c(x)=x*((x*x)*x)`. The two identities are E614, `x=x*c(x)`,
and `x=y*(c(x)*(y*x))`. Combining them into one identity remains open.
On arbitrary carriers an additional inverse identity gives an exact
three-equation characterization; see `characterizes_all` below.
-/
namespace Parastrophes.Eq872Image
open Law

def core {G : Type} (M : Magma G) (x : G) : G := M.op x (M.op (M.op x x) x)

def Basis {G : Type} (M : Magma G) : Prop :=
  @Equation614 G M ∧ ∀ x y, x = M.op y (M.op (core M x) (M.op y x))

theorem core_eq_square {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation872 G M) (x : G) : core D x = M.op x x := by
  have he (a b : G) : D.op b a = M.op (M.op a a) (M.op b a) := by
    have hh := congrArg (D.op b) (h a b)
    rwa [hd.2] at hh
  have hs : D.op x x = M.op (M.op x x) (M.op x x) := he x x
  have ht : x = M.op (D.op x x) (M.op x (M.op x x)) := by
    have hh := he (M.op x x) x
    rwa [hd.2, ← hs] at hh
  have hh := congrArg (D.op (D.op x x)) ht
  rw [hd.2] at hh
  change D.op x (D.op (D.op x x) x) = _
  rw [hh, hd.2]

theorem forward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation872 G M) : Basis D := by
  constructor
  · intro x
    change x = D.op x (core D x)
    rw [core_eq_square M D hd h, hd.2]
  · intro x y
    rw [core_eq_square M D hd h]
    have he := congrArg (D.op y) (h x y)
    rw [hd.2] at he
    rw [he, hd.2, hd.2]

theorem backward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : Basis D) : @Equation872 G M := by
  intro x y
  have hc : M.op x x = core D x := by
    have he := congrArg (M.op x) (h.1 x)
    change M.op x x = M.op x (D.op x (core D x)) at he
    rwa [hd.1] at he
  have he := congrArg (M.op y) (h.2 x y)
  rw [hd.1] at he
  have he' := congrArg (M.op (core D x)) he
  rw [hd.1] at he'
  rw [hc, he', hd.1]

/-- A concrete inverse: `M(x,y)=c(y)*(x*y)`. Finiteness turns the
displayed right inverse of each row into its two-sided inverse. -/
theorem division_term_fin {G : Type} [Finite G] (D : Magma G) (h : Basis D) :
    IsDivision .left D ⟨fun x y => D.op (core D y) (D.op x y)⟩ := by
  have he (x y : G) := (h.2 y x).symm
  have hi (x : G) : Function.Injective (D.op x) :=
    Finite.injective_iff_surjective.mpr (fun y => ⟨_, he x y⟩)
  exact ⟨he, fun x y => hi x (he x (D.op x y))⟩

/-- On finite carriers this conjunction is exactly the left-division image.
The second identity makes every row surjective, so finiteness supplies the
division needed for the converse. -/
theorem characterizes_fin {G : Type} [Finite G] (D : Magma G) :
    Basis D ↔ InImage Law872 .left D := by
  constructor
  · intro h
    let M : Magma G := ⟨fun x y => D.op (core D y) (D.op x y)⟩
    have hd : IsDivision .left D M := division_term_fin D h
    exact ⟨M, (@Law872.models_iff G M).mpr (backward M D (division_symm hd) h),
      division_symm hd⟩
  · rintro ⟨M, h, hd⟩
    exact forward M D hd ((@Law872.models_iff G M).mp h)

/-- In an actual division image, the original multiplication is recovered by
this term without a finiteness assumption. -/
theorem multiplication_eq {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation872 G M) (x y : G) :
    M.op x y = D.op (core D y) (D.op x y) := by
  have he := congrArg (M.op x) ((forward M D hd h).2 y x)
  rwa [hd.1] at he

/-- The second inverse equation is automatic on finite carriers, but can also
be imposed explicitly. Together with `Basis`, it gives three identities. -/
def CompleteBasis {G : Type} (D : Magma G) : Prop :=
  Basis D ∧ ∀ x y,
    D.op (core D (D.op x y)) (D.op x (D.op x y)) = y

/-- Exact three-equation characterization on arbitrary carriers. No
quasigroup assumption is imposed on the candidate operation. -/
theorem characterizes_all {G : Type} (D : Magma G) :
    CompleteBasis D ↔ InImage Law872 .left D := by
  constructor
  · rintro ⟨hb, hi⟩
    let M : Magma G := ⟨fun x y => D.op (core D y) (D.op x y)⟩
    have hd : IsDivision .left M D := ⟨hi, fun x y => (hb.2 y x).symm⟩
    exact ⟨M, (@Law872.models_iff G M).mpr (backward M D hd hb), hd⟩
  · rintro ⟨M, hM, hd⟩
    have h := (@Law872.models_iff G M).mp hM
    refine ⟨forward M D hd h, fun x y => ?_⟩
    rw [← multiplication_eq M D hd h, hd.1]

/-- The recovered original square map is a compositional square root of the
square map of division. This holds for every actual image, on any carrier. -/
theorem core_core_eq_square {G : Type} (D : Magma G) (h : InImage Law872 .left D)
    (x : G) : core D (core D x) = D.op x x := by
  obtain ⟨M,hM,hd⟩ := h
  have hm := (@Law872.models_iff G M).mp hM
  have hs := congrArg (D.op x) (hm x x)
  rw [hd.2] at hs
  rw [core_eq_square M D hd hm, core_eq_square M D hd hm]
  exact hs.symm

theorem core_core_eq_square_fin {G : Type} [Finite G] (D : Magma G) (h : Basis D)
    (x : G) : core D (core D x) = D.op x x :=
  core_core_eq_square D ((characterizes_fin D).mp h) x

/-- In the presence of the cross identity, the square-root condition recovers
the missing unit identity by two cancellations. Only row injectivity is used. -/
theorem unit_of_core_square {G : Type} (D : Magma G)
    (hi : ∀ x, Function.Injective (D.op x))
    (ht : ∀ x y, x = D.op y (D.op (core D x) (D.op y x)))
    (hc : ∀ x, core D (core D x) = D.op x x) : @Equation614 G D := by
  intro x
  have he := ht (core D x) x
  rw [hc] at he
  change D.op x (D.op (D.op x x) x) =
    D.op x (D.op (D.op x x) (D.op x (core D x))) at he
  exact hi (D.op x x) (hi x he)

/-- An alternative exact finite description: the cross identity and the fact
that the recovered square is a compositional square root of division's square. -/
theorem characterizes_core_square_fin {G : Type} [Finite G] (D : Magma G) :
    ((∀ x y, x = D.op y (D.op (core D x) (D.op y x))) ∧
      ∀ x, core D (core D x) = D.op x x) ↔ InImage Law872 .left D := by
  constructor
  · rintro ⟨ht, hc⟩
    have hi (y : G) : Function.Injective (D.op y) :=
      Finite.injective_iff_surjective.mpr (fun x => ⟨_, (ht x y).symm⟩)
    exact (characterizes_fin D).mp ⟨unit_of_core_square D hi ht hc, ht⟩
  · intro h
    exact ⟨((characterizes_fin D).mpr h).2, core_core_eq_square D h⟩

end Parastrophes.Eq872Image

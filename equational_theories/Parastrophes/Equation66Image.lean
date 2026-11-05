import equational_theories.Parastrophes.TranslationLoops
import equational_theories.Superposition

/-!
# An exact single identity for E66's left-division image

Write `s(x) = x * (x*x)` and `c(y) = L_y^5(y)`. The defining identity is
`x = y * (z * ((x * c(y)) * z))`, with nine operation symbols.
The translation-loop argument below works on arbitrary carriers.
-/
namespace Parastrophes
open Law FreeMagma

/-- Five successive applications of the row indexed by `y`. -/
def fifthPower {G : Type*} (M : Magma G) (y : G) : G :=
  M.op y (M.op y (M.op y (M.op y (M.op y y))))

/-- The nine-operation identity defining E66's left-division image. -/
def leftImage66 : NatMagmaLaw :=
  ⟨Lf 0, Lf 1 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆
    (Lf 1 ⋆ (Lf 1 ⋆ (Lf 1 ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 1)))))) ⋆ Lf 2))⟩

theorem leftImage66_iff {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage66 ↔
      ∀ x y z, x = M.op y (M.op z (M.op (M.op x (fifthPower M y)) z)) := by
  constructor
  · intro h x y z
    exact h (fun n => if n = 0 then x else if n = 1 then y else z)
  · intro h v
    exact h (v 0) (v 1) (v 2)

namespace Eq66Image

/-- Reversing the four multiplication constraints turns E66 into E53,
provided the two operations really are left divisions of one another. -/
theorem transfer66_53 {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation66 G M) : @Equation53 G D := by
  intro x y
  have he := congrArg (fun v => D.op x (D.op y (D.op x v))) (h y x)
  simpa only [hd.1, hd.2] using he.symm

theorem transfer53_66 {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation53 G M) : @Equation66 G D := by
  intro x y
  have he := congrArg (fun v => D.op y (D.op x (D.op y v))) (h y x)
  simpa only [hd.1, hd.2] using he.symm

/-- A mixed translation loop has a left inverse as well as the displayed
right inverse. Four equational substitutions establish the reverse loop. -/
private theorem reverse_loop {G : Type} (M : Magma G) (c : G → G)
    (h : ∀ x y z, x = M.op y (M.op z (M.op (M.op x (c y)) z))) :
    ∀ x y z, M.op z (M.op (M.op (M.op x y) (c x)) z) = y := by
  have e6 (X0 X1 X2 : G) :
      M.op X1 (M.op X2 (M.op (M.op X0 (c X1)) X2)) = X0 := (h ..).symm
  have e9 (X0 X1 X2 X3 : G) :
      M.op X1 (M.op (M.op X2 (M.op (M.op X0 (c (M.op X3 (c X1)))) X2)) X0) = X3 :=
    superpose e6 e6
  have e12 (X0 X1 X2 X3 X4 : G) :
      M.op X1 (M.op (M.op (M.op X2
        (M.op (M.op X3 (c (M.op X0 (c (M.op X4 (c X1)))))) X2)) X3) X0) = X4 :=
    superpose e9 e6
  have e17 (X0 X1 X2 X3 : G) :
      M.op X3 (M.op (M.op (c X1) (c (M.op X2 (c (M.op X0 (c X2)))))) X3) = M.op X1 X0 :=
    superpose e12 e6
  have e41 (X0 X1 X2 : G) :
      M.op X2 (M.op (M.op (M.op X0 X1) (c X0)) X2) = X1 :=
    superpose e17 e12
  exact e41

/-- The mixed loop forces bijective rows without finiteness. -/
theorem loop_leftQuasigroup {G : Type} (M : Magma G) (c : G → G)
    (h : ∀ x y z, x = M.op y (M.op z (M.op (M.op x (c y)) z))) :
    IsSideQuasigroup .left M := by
  have hi := reverse_loop M c h
  intro y
  constructor
  · intro a b hab
    rw [← hi y a y, ← hi y b y, hab]
  · intro x
    exact ⟨M.op y (M.op (M.op x (c y)) y), (h x y y).symm⟩

/-- The same loop forces surjective columns and makes `L_z R_z`
independent of `z`. These are consequences, not extra hypotheses. -/
theorem loop_common {G : Type} (M : Magma G) (c : G → G)
    (h : ∀ x y z, x = M.op y (M.op z (M.op (M.op x (c y)) z))) :
    ∀ x y, M.op y (M.op x y) = M.op x (M.op x x) := by
  have hq := loop_leftQuasigroup M c h
  have hs (z : G) : Function.Surjective (fun x => M.op x z) := by
    intro t
    refine ⟨M.op (M.op z (M.op z t)) (c z), ?_⟩
    exact ((hq z).1 ((hq z).1 (h (M.op z (M.op z t)) z z))).symm
  intro x y
  obtain ⟨a, ha⟩ := hs (c y) x
  change M.op a (c y) = x at ha
  apply (hq y).1
  have hy := h a y y
  have hx := h a y x
  rw [ha] at hy hx
  exact hy.symm.trans hx

/-- E53 and bijective rows imply the common-translation identity E4332. -/
theorem common_of53 {G : Type} (M : Magma G) (hq : IsSideQuasigroup .left M)
    (h : @Equation53 G M) :
    ∀ x y, M.op y (M.op x y) = M.op x (M.op x x) := by
  intro x y
  exact (hq x).1 ((h x y).symm.trans (h x x))

/-- The common-translation map preserves multiplication. -/
theorem common_map {G : Type} (M : Magma G) (s : G → G)
    (hf : ∀ x y, M.op y (M.op x y) = s x) :
    ∀ x y, s (M.op x y) = M.op (s x) (s y) := by
  intro x y
  have h1 := hf y (M.op x y)
  rw [hf x y] at h1
  have h2 := hf (M.op x y) (s x)
  rw [h1] at h2
  exact h2.symm

/-- Under E53 the common-translation map is an involution. -/
theorem common_involutive {G : Type} (M : Magma G) (s : G → G)
    (hf : ∀ x y, M.op y (M.op x y) = s x)
    (ha : ∀ x, M.op x (s x) = x) : ∀ x, s (s x) = x := by
  intro x
  have h1 := hf x (s x)
  rw [ha x] at h1
  have h2 := hf (s x) x
  rw [h1, ha x] at h2
  exact h2.symm

/-- Five row iterations make the mixed loop enforce E53. The proof uses
only two cancellations after extracting `x*s(x) = s(s(x))`. -/
theorem equation53_of_long {G : Type} (M : Magma G)
    (h : ∀ x y z, x = M.op y (M.op z (M.op (M.op x (fifthPower M y)) z))) :
    @Equation53 G M := by
  let s (x : G) := M.op x (M.op x x)
  have hq := loop_leftQuasigroup M (fifthPower M) h
  have hf : ∀ x y, M.op y (M.op x y) = s x := loop_common M (fifthPower M) h
  have hk (x y : G) : x = M.op y (s (M.op x (fifthPower M y))) := by
    simpa only [hf] using h x y y
  have he (y : G) : M.op y (s y) = s (s y) := by
    have hp := hf y (M.op y (M.op y (s y)))
    change M.op (M.op y (M.op y (s y))) (fifthPower M y) = s y at hp
    have hh := hk (M.op y (M.op y (s y))) y
    rw [hp] at hh
    exact (hq y).1 hh
  have ha (x : G) : M.op x (s x) = x := by
    have h1 := hf (s x) x
    rw [← he x] at h1
    have h2 := (hq x).1 h1
    have h3 := hf x (s x)
    exact (hq (s x)).1 (h3.trans h2.symm)
  intro x y
  rw [hf, ha]

/-- Conversely, E53 and its common-translation identity give the longer law. -/
theorem long_of53 {G : Type} (M : Magma G) (hq : IsSideQuasigroup .left M)
    (h : @Equation53 G M) : @satisfies _ G M leftImage66 := by
  let s (x : G) := M.op x (M.op x x)
  have hf : ∀ x y, M.op y (M.op x y) = s x := common_of53 M hq h
  have ha (x : G) : M.op x (s x) = x := (h x x).symm
  have hs := common_involutive M s hf ha
  have hm := common_map M s hf
  have hc (y : G) : fifthPower M y = s y := by
    change M.op y (M.op y (M.op y (s y))) = s y
    rw [ha y]
  apply (leftImage66_iff M).mpr
  intro x y z
  rw [hc, hf, hm, hs, hf, hs]

end Eq66Image

namespace Catalogue

/-- The nine-operation identity characterizes E66's left-division image
on arbitrary carriers, with no finiteness assumption or extra axioms. -/
@[parastrophe_result] theorem left_characterizes66_all_long :
    Characterizes .all Law66 .left leftImage66 := by
  apply characterizes_of_division
  · intro G M _ h
    exact Eq66Image.loop_leftQuasigroup M (fifthPower M) ((leftImage66_iff M).mp h)
  · intro G M D _ hd h
    exact Eq66Image.long_of53 D (sideQuasigroup_of_division (division_symm hd))
      (Eq66Image.transfer66_53 M D hd ((@Law66.models_iff G M).mp h))
  · intro G M D _ hd h
    exact (@Law66.models_iff G D).mpr (Eq66Image.transfer53_66 M D hd
      (Eq66Image.equation53_of_long M ((leftImage66_iff M).mp h)))

end Catalogue
end Parastrophes

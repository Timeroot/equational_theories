import equational_theories.Spectrum.Equation667BinaryFive
import Mathlib.Data.List.Nodup

/-! Every two distinct elements of a finite commutative idempotent E667
magma lie in a copy of the five-point mean algebra. -/
namespace Spectrum.E667.CommutativeBlocks
variable {Q : Type*} [Magma Q] [Finite Q]
    (h : Equation667 Q) (hc : ∀ x y : Q, x ◇ y = y ◇ x)
    (hi : ∀ x : Q, x ◇ x = x)
include h hc hi

/-- The four-cycle through b and the ten forced products give a five-point
subalgebra containing any prescribed distinct pair. -/
theorem five_embedding (a b : Q) (hab : a ≠ b) :
    ∃ f : ZMod 5 ↪ Q, f 0 = a ∧ f 1 = b ∧
      ∀ i j, f (BinaryFive.base i j) = f i ◇ f j := by
  have law63 (x y : Q) : y ◇ (x ◇ (x ◇ y)) = x := by
    simpa only [hi] using (h x y).symm
  have linj := E667883.left_injective667 h
  have rinj := E667883.right_injective667 h
  let c := a ◇ b
  let d := a ◇ c
  let e := a ◇ d
  have h_ab : a ◇ b = c := rfl
  have h_ac : a ◇ c = d := rfl
  have h_ad : a ◇ d = e := rfl
  have h_bd : b ◇ d = a := law63 a b
  have h_ce : c ◇ e = a := law63 a c
  have h_ae : a ◇ e = b := by
    apply linj d
    exact (law63 a d).trans ((hc d b).trans h_bd).symm
  have h_cd : c ◇ d = b := by
    apply linj a
    have hh := law63 c a
    rw [hc c a] at hh
    exact hh.trans h_ab.symm
  have h_de : d ◇ e = c := by
    apply linj a
    have hh := law63 d a
    rw [hc d a] at hh
    exact hh.trans h_ac.symm
  have h_be : b ◇ e = d := by
    have hh := law63 e a
    rw [hc e a, h_ae] at hh
    have he_b : e ◇ b = d := linj a (hh.trans h_ad.symm)
    exact (hc b e).trans he_b
  have h_bc : b ◇ c = e := by
    apply linj b
    apply linj c
    exact (law63 b c).trans ((congrArg (fun z => c ◇ z) h_be).trans h_cd).symm
  have hac : a ≠ c := by
    intro he
    apply hab
    exact linj a ((hi a).trans he |>.trans h_ab.symm)
  have had : a ≠ d := by
    intro he
    apply hac
    exact linj a ((hi a).trans he |>.trans h_ac.symm)
  have hae : a ≠ e := by
    intro he
    apply had
    exact linj a ((hi a).trans he |>.trans h_ad.symm)
  have hbc : b ≠ c := by
    intro he
    apply hab
    exact rinj b (h_ab.trans (he.symm.trans (hi b).symm))
  have hbd : b ≠ d := by
    intro he
    apply hab
    have hh := h_bd
    rw [← he, hi] at hh
    exact hh.symm
  have hbe : b ≠ e := by
    intro he
    apply hbc
    have hh := congrArg (fun z => a ◇ z) he
    change a ◇ b = a ◇ e at hh
    rw [h_ab, h_ae] at hh
    exact hh.symm
  have hcd : c ≠ d := fun he => hbc (linj a he)
  have hce : c ≠ e := fun he => hbd (linj a he)
  have hde : d ≠ e := fun he => hcd (linj a he)
  have hn : [a,b,e,c,d].Nodup := by
    simp [hab,hac,had,hae,hbc,hbd,hbe,hcd,hce,hde,ne_comm]
  let f : ZMod 5 → Q := [a,b,e,c,d].get
  have hf : Function.Injective f := hn.injective_get
  refine ⟨⟨f,hf⟩, rfl, rfl, ?_⟩
  have h_ba := (hc b a).trans h_ab
  have h_ca := (hc c a).trans h_ac
  have h_da := (hc d a).trans h_ad
  have h_ea := (hc e a).trans h_ae
  have h_cb := (hc c b).trans h_bc
  have h_db := (hc d b).trans h_bd
  have h_eb := (hc e b).trans h_be
  have h_dc := (hc d c).trans h_cd
  have h_ec := (hc e c).trans h_ce
  have h_ed := (hc e d).trans h_de
  intro i j
  fin_cases i <;> fin_cases j <;> dsimp [f, BinaryFive.base]
  all_goals simp only [hi,h_ab,h_ac,h_ad,h_ae,h_bc,h_bd,h_be,h_cd,h_ce,h_de,
    h_ba,h_ca,h_da,h_ea,h_cb,h_db,h_eb,h_dc,h_ec,h_ed]
  all_goals rfl

spectrum_assert five_embedding complete
end Spectrum.E667.CommutativeBlocks

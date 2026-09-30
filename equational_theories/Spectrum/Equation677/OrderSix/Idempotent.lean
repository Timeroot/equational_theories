import equational_theories.Spectrum.Equation677.OrderSix.OtherCycles

namespace Spectrum.E677.OrderSix
universe u
open scoped Spectrum.E677.OrderSix
local infixl:70 " * " => Magma.op
variable {M : Type u} [Magma M] [Fact (Equation677 M)] [Finite M]

/-- **No six-element magma satisfies Equation 677 and the idempotent law.**

Under the idempotent law a product $x \diamond y$ with $x \neq y$ avoids both factors
(`eq_of_mul_eq_self_left`, `eq_of_mul_eq_self_right`) and both backward steps $x / y$ and
$x / y / y$ (`eq_of_mul_eq_div`, `eq_of_mul_eq_div_div`). Name two distinct elements $a, b$,
their product $c = a \diamond b$, and the remaining three elements $d, e, f$. The diagonal is
known, every other cell ranges over a handful of values, and a case analysis — each step an
instance of Equation 677, a left cancellation, one of the removals above, or the separation
lemma `eq_of_mul_eq_of_mul_mul_eq` — refutes every assignment. -/
theorem not_forall_isIdempotentElem_of_card_eq_six (hM : Nat.card M = 6)
    (hidem : ∀ x : M, Idempotent x) : False := by
  -- two distinct elements and their product
  obtain ⟨a, -⟩ := exists_notMem (l := ([] : List M))
    (by simp [hM])
  obtain ⟨b, hbm⟩ := exists_notMem (l := [a]) (by simp [hM])
  have hab : a ≠ b := fun h => hbm (by rw [h]; simp)
  obtain ⟨c, hc⟩ : ∃ c, c = a * b := ⟨_, rfl⟩
  have hac : a ≠ c := by
    intro h
    have h' : a * b = a := by rw [← hc, ← h]
    exact hab (eq_of_mul_eq_self_left (hidem a) h').symm
  have hbc : b ≠ c := by
    intro h
    have h' : a * b = b := by rw [← hc, ← h]
    exact hab (eq_of_mul_eq_self_right (hidem b) h')
  -- the remaining three elements
  obtain ⟨d, hdm⟩ := exists_notMem (l := [a, b, c])
    (by simp [hM])
  obtain ⟨e, hem⟩ := exists_notMem (l := [a, b, c, d])
    (by simp [hM])
  obtain ⟨f, hfm⟩ := exists_notMem (l := [a, b, c, d, e])
    (by simp [hM])
  have had : a ≠ d := fun h => hdm (by rw [h]; simp)
  have hbd : b ≠ d := fun h => hdm (by rw [h]; simp)
  have hcd : c ≠ d := fun h => hdm (by rw [h]; simp)
  have hae : a ≠ e := fun h => hem (by rw [h]; simp)
  have hbe : b ≠ e := fun h => hem (by rw [h]; simp)
  have hce : c ≠ e := fun h => hem (by rw [h]; simp)
  have hde : d ≠ e := fun h => hem (by rw [h]; simp)
  have haf : a ≠ f := fun h => hfm (by rw [h]; simp)
  have hbf : b ≠ f := fun h => hfm (by rw [h]; simp)
  have hcf : c ≠ f := fun h => hfm (by rw [h]; simp)
  have hdf : d ≠ f := fun h => hfm (by rw [h]; simp)
  have hef : e ≠ f := fun h => hfm (by rw [h]; simp)
  -- the six elements exhaust the carrier
  have hspan : ∀ z : M, z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f :=
    span_six hM hab hac had hae haf hbc hbd hbe hbf hcd hce hcf hde hdf hef
  rcases hspan (a * d) with hcs1 | hcs1 | hcs1 | hcs1 | hcs1 | hcs1
  · -- $a \diamond d = a$
    exact absurd (mul_left_cancel (hcs1.trans (hidem a).eq.symm)) (had.symm)
  · -- $a \diamond d = b$
    rcases hspan (a * e) with hcs2 | hcs2 | hcs2 | hcs2 | hcs2 | hcs2
    · -- $a \diamond e = a$
      exact absurd (mul_left_cancel (hcs2.trans (hidem a).eq.symm)) (hae.symm)
    · -- $a \diamond e = b$
      exact absurd (mul_left_cancel (hcs2.trans hcs1.symm)) (hde.symm)
    · -- $a \diamond e = c$
      exact absurd (mul_left_cancel (hcs2.trans hc.symm.symm)) (hbe.symm)
    · -- $a \diamond e = d$
      rcases hspan (a * f) with hcs3 | hcs3 | hcs3 | hcs3 | hcs3 | hcs3
      · -- $a \diamond f = a$
        exact absurd (mul_left_cancel (hcs3.trans (hidem a).eq.symm)) (haf.symm)
      · -- $a \diamond f = b$
        exact absurd (mul_left_cancel (hcs3.trans hcs1.symm)) (hdf.symm)
      · -- $a \diamond f = c$
        exact absurd (mul_left_cancel (hcs3.trans hc.symm.symm)) (hbf.symm)
      · -- $a \diamond f = d$
        exact absurd (mul_left_cancel (hcs3.trans hcs2.symm)) (hef.symm)
      · -- $a \diamond f = e$
        have hv4 : a * c = f := by
          rcases hspan (a * c) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (hac.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) hcd
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbc.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs2.symm)) hce
          · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) hcf
          · exact hz
        rcases hspan (b * a) with hcs5 | hcs5 | hcs5 | hcs5 | hcs5 | hcs5
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs5) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs5.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv6 : d * c = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs5))).symm.trans
              (eq677 d a)).trans hcs2.symm)
          rcases hspan (c * a) with hcs7 | hcs7 | hcs7 | hcs7 | hcs7 | hcs7
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs7) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs7.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs7.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs7.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv8 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs7))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * f) with hcs9 | hcs9 | hcs9 | hcs9 | hcs9 | hcs9
            · -- $b \diamond f = a$
              have hv10 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs5))).symm.trans
                  (eq677 a b)).trans hcs9.symm)).trans hv4.symm)
              exact absurd (mul_left_cancel (hv10.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond f = b$
              exact absurd (mul_left_cancel (hcs9.trans (hidem b).eq.symm)) (hbf.symm)
            · -- $b \diamond f = c$
              exact absurd (mul_left_cancel (hcs9.trans hcs5.symm)) (haf.symm)
            · -- $b \diamond f = d$
              exact absurd (mul_left_cancel (hcs9.trans hv8.symm)) (hef.symm)
            · -- $b \diamond f = e$
              have e1 : b * f = a * f := hcs9.trans hcs3.symm
              have e2 : b * (a * f) = a * (a * f) := by
                rw [hcs3]
                exact hv8.trans hcs2.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
            · -- $b \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs9) hbf
          · -- $c \diamond a = f$
            have hv11 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs7))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * e) with hcs12 | hcs12 | hcs12 | hcs12 | hcs12 | hcs12
            · -- $b \diamond e = a$
              have hv13 : c * b = f :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs5))).symm.trans
                  (eq677 a b)).trans hcs12.symm)).trans hcs3.symm)
              exact absurd (mul_left_cancel (hv13.trans hcs7.symm)) (hab.symm)
            · -- $b \diamond e = b$
              exact absurd (mul_left_cancel (hcs12.trans (hidem b).eq.symm)) (hbe.symm)
            · -- $b \diamond e = c$
              exact absurd (mul_left_cancel (hcs12.trans hcs5.symm)) (hae.symm)
            · -- $b \diamond e = d$
              exact absurd (mul_left_cancel (hcs12.trans hv11.symm)) hef
            · -- $b \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs12) hbe
            · -- $b \diamond e = f$
              rcases hspan (b * c) with hcs14 | hcs14 | hcs14 | hcs14 | hcs14 | hcs14
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs14
                have hik : Idempotent (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs14.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs14.trans hcs5.symm)) (hac.symm)
              · -- $b \diamond c = d$
                exact absurd (mul_left_cancel (hcs14.trans hv11.symm)) hcf
              · -- $b \diamond c = e$
                have hv15 : b * d = a := by
                  rcases hspan (b * d) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbd.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs5.symm)) (had.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv11.symm)) hdf
                  · exact absurd (mul_left_cancel (hz.trans hcs14.symm)) (hcd.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs12.symm)) hde
                have hv16 : c * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs5))).symm.trans
                    (eq677 a b)).trans hv15.symm)).trans hcs2.symm)
                have hv17 : b * e = d :=
                  (congrArg (b * ·) ((congrArg (d * ·) ((congrArg (· * b) hv15).trans
                    hc.symm)).trans hv6)).symm.trans (eq677 d b)
                exact absurd (hv17.symm.trans hcs12) hdf
              · -- $b \diamond c = f$
                exact absurd (mul_left_cancel (hcs14.trans hcs12.symm)) hce
        · -- $b \diamond a = d$
          have hdv : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hik : Idempotent (b / a) := hdv ▸ hidem d
          exact absurd (eq_of_mul_eq_div hik (hcs5.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = e$
          have hdv1 : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hdv2 : b / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs2
          have hik : Idempotent (b / a / a) := hdv2 ▸ hidem e
          exact absurd (eq_of_mul_eq_div_div hik (hcs5.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = f$
          have hv18 : d * f = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs5))).symm.trans
              (eq677 d a)).trans hcs2.symm)
          rcases hspan (c * a) with hcs19 | hcs19 | hcs19 | hcs19 | hcs19 | hcs19
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs19) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs19.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs19.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs19.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv20 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs19))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * c) with hcs21 | hcs21 | hcs21 | hcs21 | hcs21 | hcs21
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs21
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs21.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs21) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs21.trans hv20.symm)) hce
            · -- $b \diamond c = e$
              rcases hspan (b * d) with hcs22 | hcs22 | hcs22 | hcs22 | hcs22 | hcs22
              · -- $b \diamond d = a$
                have hv23 : f * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs5))).symm.trans
                    (eq677 a b)).trans hcs22.symm)).trans hcs2.symm)
                have hv24 : d * c = e :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs22).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hv20.symm)
                exact absurd (mul_left_cancel (hv24.trans hv18.symm)) hcf
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs22.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv25 : c * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (d * ·) (congrArg (· * b) hcs22))).symm.trans
                    (eq677 d b)).trans hv20.symm)).trans hv18.symm)
                have hv26 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs22.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv20.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs21.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs5.symm)) (haf.symm)
                have hv27 : f * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs5))).symm.trans
                    (eq677 a b)).trans hv26.symm)).trans hv4.symm)
                have hv28 : f * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv26).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hcs5.symm)
                have hv29 : c * f = b :=
                  (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv25).trans
                    hv28)).trans hcs5)).symm.trans (eq677 b c)
                have hdv : c / f = b := div_eq_iff_mul_eq.mpr hv27
                have hik : Idempotent (c / f) := hdv ▸ hidem b
                exact absurd (eq_of_mul_eq_div hik (hv29.trans hdv.symm)) hcf
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs22.trans hv20.symm)) hde
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs22.trans hcs21.symm)) (hcd.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs22.trans hcs5.symm)) (had.symm)
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs21.trans hcs5.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv30 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs19))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (d * b) with hcs31 | hcs31 | hcs31 | hcs31 | hcs31 | hcs31
            · -- $d \diamond b = a$
              have hdv1 : d / b = f := div_eq_iff_mul_eq.mpr hv30
              have hdv2 : d / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs5
              have hik : Idempotent (d / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs31.trans hdv2.symm)) (hbd.symm)
            · -- $d \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs31) (hbd.symm)
            · -- $d \diamond b = c$
              have hv32 : f * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                  ((congrArg (· * b) hv30).trans hcs31))).symm.trans
                  (eq677 f b)).trans hcs5.symm)
              have hdv : f / c = a := div_eq_iff_mul_eq.mpr hcs19
              have hik : Idempotent (f / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv32.trans hdv.symm)) (hcf.symm)
            · -- $d \diamond b = d$
              exact absurd (mul_left_cancel (hcs31.trans (hidem d).eq.symm)) hbd
            · -- $d \diamond b = e$
              exact absurd (mul_left_cancel (hcs31.trans hv18.symm)) hbf
            · -- $d \diamond b = f$
              have hdv : d / b = f := div_eq_iff_mul_eq.mpr hv30
              have hik : Idempotent (d / b) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs31.trans hdv.symm)) (hbd.symm)
      · -- $a \diamond f = f$
        exact absurd (eq_of_mul_eq_self_right (hidem f) hcs3) haf
    · -- $a \diamond e = e$
      exact absurd (eq_of_mul_eq_self_right (hidem e) hcs2) hae
    · -- $a \diamond e = f$
      rcases hspan (a * c) with hcs33 | hcs33 | hcs33 | hcs33 | hcs33 | hcs33
      · -- $a \diamond c = a$
        exact absurd (mul_left_cancel (hcs33.trans (hidem a).eq.symm)) (hac.symm)
      · -- $a \diamond c = b$
        exact absurd (mul_left_cancel (hcs33.trans hcs1.symm)) hcd
      · -- $a \diamond c = c$
        exact absurd (mul_left_cancel (hcs33.trans hc.symm.symm)) (hbc.symm)
      · -- $a \diamond c = d$
        have hv34 : a * f = e := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs33.symm)) (hcf.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs2.symm)) (hef.symm)
        rcases hspan (b * a) with hcs35 | hcs35 | hcs35 | hcs35 | hcs35 | hcs35
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs35) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs35.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hdv1 : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hdv2 : b / a / a = c := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs33
          have hik : Idempotent (b / a / a) := hdv2 ▸ hidem c
          exact absurd (eq_of_mul_eq_div_div hik (hcs35.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = d$
          have hdv : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hik : Idempotent (b / a) := hdv ▸ hidem d
          exact absurd (eq_of_mul_eq_div hik (hcs35.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = e$
          have hv36 : d * e = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs35))).symm.trans
              (eq677 d a)).trans hcs33.symm)
          rcases hspan (c * a) with hcs37 | hcs37 | hcs37 | hcs37 | hcs37 | hcs37
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs37) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs37.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs37.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs37.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv38 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs37))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (d * b) with hcs39 | hcs39 | hcs39 | hcs39 | hcs39 | hcs39
            · -- $d \diamond b = a$
              have hdv1 : d / b = e := div_eq_iff_mul_eq.mpr hv38
              have hdv2 : d / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs35
              have hik : Idempotent (d / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs39.trans hdv2.symm)) (hbd.symm)
            · -- $d \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs39) (hbd.symm)
            · -- $d \diamond b = c$
              exact absurd (mul_left_cancel (hcs39.trans hv36.symm)) hbe
            · -- $d \diamond b = d$
              exact absurd (mul_left_cancel (hcs39.trans (hidem d).eq.symm)) hbd
            · -- $d \diamond b = e$
              have hdv : d / b = e := div_eq_iff_mul_eq.mpr hv38
              have hik : Idempotent (d / b) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs39.trans hdv.symm)) (hbd.symm)
            · -- $d \diamond b = f$
              have hv40 : e * f = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                  ((congrArg (· * b) hv38).trans hcs39))).symm.trans
                  (eq677 e b)).trans hcs35.symm)
              have hdv : a / e = f := div_eq_iff_mul_eq.mpr hv40
              have hik : Idempotent (a / e) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs2.trans hdv.symm)) hae
          · -- $c \diamond a = f$
            have hv41 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs37))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * c) with hcs42 | hcs42 | hcs42 | hcs42 | hcs42 | hcs42
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs42
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs42.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs42) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs42.trans hv41.symm)) hcf
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs42.trans hcs35.symm)) (hac.symm)
            · -- $b \diamond c = f$
              rcases hspan (b * d) with hcs43 | hcs43 | hcs43 | hcs43 | hcs43 | hcs43
              · -- $b \diamond d = a$
                have hv44 : e * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs35))).symm.trans
                    (eq677 a b)).trans hcs43.symm)).trans hcs33.symm)
                have hv45 : d * c = f :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs43).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hv41.symm)
                have hv46 : b * e = c := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs43.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hv41.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs35.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs42.symm)) (hce.symm)
                have e1 : d * e = b * e := hv36.trans hv46.symm
                have e2 : d * (b * e) = b * (b * e) := by
                  rw [hv46]
                  exact hv45.trans hcs42.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbd.symm)
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs43.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv47 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs43.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv41.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs35.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs42.symm)) (hce.symm)
                have hv48 : e * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs35))).symm.trans
                    (eq677 a b)).trans hv47.symm)).trans hv34.symm)
                have hv49 : e * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hv47).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hcs35.symm)
                have hv50 : f * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (e * ·) (congrArg (· * a) hcs2))).symm.trans
                    (eq677 e a)).trans hv34.symm)).trans hv48.symm)
                have hv51 : f * b = a :=
                  (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hv50).trans
                    hv41)).trans hcs1)).symm.trans (eq677 a f)
                have hv52 : b * f = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs42).trans
                    hv51)).trans hcs37)).symm.trans (eq677 c b)
                exact absurd (hv52.symm.trans hv41) hcd
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs43.trans hv41.symm)) hdf
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs43.trans hcs35.symm)) (had.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs43.trans hcs42.symm)) (hcd.symm)
        · -- $b \diamond a = f$
          have hv53 : d * f = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs35))).symm.trans
              (eq677 d a)).trans hcs33.symm)
          rcases hspan (c * a) with hcs54 | hcs54 | hcs54 | hcs54 | hcs54 | hcs54
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs54) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs54.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs54.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs54.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv55 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs54))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * c) with hcs56 | hcs56 | hcs56 | hcs56 | hcs56 | hcs56
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs56
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs56.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs56) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs56.trans hv55.symm)) hce
            · -- $b \diamond c = e$
              rcases hspan (b * d) with hcs57 | hcs57 | hcs57 | hcs57 | hcs57 | hcs57
              · -- $b \diamond d = a$
                have hv58 : f * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs35))).symm.trans
                    (eq677 a b)).trans hcs57.symm)).trans hcs33.symm)
                have hv59 : d * c = e :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs57).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hv55.symm)
                have hv60 : b * f = c := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs57.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hv55.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs56.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs35.symm)) (haf.symm)
                have e1 : d * f = b * f := hv53.trans hv60.symm
                have e2 : d * (b * f) = b * (b * f) := by
                  rw [hv60]
                  exact hv59.trans hcs56.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbd.symm)
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs57.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv61 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs57.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv55.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs56.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs35.symm)) (haf.symm)
                have hv62 : f * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs35))).symm.trans
                    (eq677 a b)).trans hv61.symm)).trans hcs2.symm)
                have hv63 : f * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv61).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hcs35.symm)
                have hv64 : e * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (f * ·) (congrArg (· * a) hv34))).symm.trans
                    (eq677 f a)).trans hcs2.symm)).trans hv62.symm)
                have hv65 : e * b = a :=
                  (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hv64).trans
                    hv55)).trans hcs1)).symm.trans (eq677 a e)
                have hv66 : b * e = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs56).trans
                    hv65)).trans hcs54)).symm.trans (eq677 c b)
                exact absurd (hv66.symm.trans hv55) hcd
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs57.trans hv55.symm)) hde
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs57.trans hcs56.symm)) (hcd.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs57.trans hcs35.symm)) (had.symm)
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs56.trans hcs35.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv67 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs54))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (d * b) with hcs68 | hcs68 | hcs68 | hcs68 | hcs68 | hcs68
            · -- $d \diamond b = a$
              have hdv1 : d / b = f := div_eq_iff_mul_eq.mpr hv67
              have hdv2 : d / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs35
              have hik : Idempotent (d / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs68.trans hdv2.symm)) (hbd.symm)
            · -- $d \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs68) (hbd.symm)
            · -- $d \diamond b = c$
              exact absurd (mul_left_cancel (hcs68.trans hv53.symm)) hbf
            · -- $d \diamond b = d$
              exact absurd (mul_left_cancel (hcs68.trans (hidem d).eq.symm)) hbd
            · -- $d \diamond b = e$
              have hv69 : f * e = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                  ((congrArg (· * b) hv67).trans hcs68))).symm.trans
                  (eq677 f b)).trans hcs35.symm)
              have hdv : a / f = e := div_eq_iff_mul_eq.mpr hv69
              have hik : Idempotent (a / f) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hv34.trans hdv.symm)) haf
            · -- $d \diamond b = f$
              have hdv : d / b = f := div_eq_iff_mul_eq.mpr hv67
              have hik : Idempotent (d / b) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs68.trans hdv.symm)) (hbd.symm)
      · -- $a \diamond c = e$
        have hv70 : a * f = d := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs33.symm)) (hcf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs2.symm)) (hef.symm)
        rcases hspan (b * a) with hcs71 | hcs71 | hcs71 | hcs71 | hcs71 | hcs71
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs71) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs71.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv72 : d * c = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs71))).symm.trans
              (eq677 d a)).trans hv70.symm)
          rcases hspan (c * a) with hcs73 | hcs73 | hcs73 | hcs73 | hcs73 | hcs73
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs73) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs73.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs73.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs73.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv74 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * f) with hcs75 | hcs75 | hcs75 | hcs75 | hcs75 | hcs75
            · -- $b \diamond f = a$
              have hv76 : c * b = e :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs71))).symm.trans
                  (eq677 a b)).trans hcs75.symm)).trans hcs2.symm)
              exact absurd (mul_left_cancel (hv76.trans hcs73.symm)) (hab.symm)
            · -- $b \diamond f = b$
              exact absurd (mul_left_cancel (hcs75.trans (hidem b).eq.symm)) (hbf.symm)
            · -- $b \diamond f = c$
              exact absurd (mul_left_cancel (hcs75.trans hcs71.symm)) (haf.symm)
            · -- $b \diamond f = d$
              exact absurd (mul_left_cancel (hcs75.trans hv74.symm)) (hef.symm)
            · -- $b \diamond f = e$
              rcases hspan (b * c) with hcs77 | hcs77 | hcs77 | hcs77 | hcs77 | hcs77
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs77
                have hik : Idempotent (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs77.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs77.trans hcs71.symm)) (hac.symm)
              · -- $b \diamond c = d$
                exact absurd (mul_left_cancel (hcs77.trans hv74.symm)) hce
              · -- $b \diamond c = e$
                exact absurd (mul_left_cancel (hcs77.trans hcs75.symm)) hcf
              · -- $b \diamond c = f$
                have hv78 : b * d = a := by
                  rcases hspan (b * d) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbd.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs71.symm)) (had.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv74.symm)) hde
                  · exact absurd (mul_left_cancel (hz.trans hcs75.symm)) hdf
                  · exact absurd (mul_left_cancel (hz.trans hcs77.symm)) (hcd.symm)
                have hv79 : c * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs71))).symm.trans
                    (eq677 a b)).trans hv78.symm)).trans hv70.symm)
                have hv80 : b * f = d :=
                  (congrArg (b * ·) ((congrArg (d * ·) ((congrArg (· * b) hv78).trans
                    hc.symm)).trans hv72)).symm.trans (eq677 d b)
                exact absurd (hv80.symm.trans hcs75) hde
            · -- $b \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs75) hbf
          · -- $c \diamond a = f$
            have hv81 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * e) with hcs82 | hcs82 | hcs82 | hcs82 | hcs82 | hcs82
            · -- $b \diamond e = a$
              have hv83 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs71))).symm.trans
                  (eq677 a b)).trans hcs82.symm)).trans hcs33.symm)
              exact absurd (mul_left_cancel (hv83.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond e = b$
              exact absurd (mul_left_cancel (hcs82.trans (hidem b).eq.symm)) (hbe.symm)
            · -- $b \diamond e = c$
              exact absurd (mul_left_cancel (hcs82.trans hcs71.symm)) (hae.symm)
            · -- $b \diamond e = d$
              exact absurd (mul_left_cancel (hcs82.trans hv81.symm)) hef
            · -- $b \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs82) hbe
            · -- $b \diamond e = f$
              have e1 : b * e = a * e := hcs82.trans hcs2.symm
              have e2 : b * (a * e) = a * (a * e) := by
                rw [hcs2]
                exact hv81.trans hv70.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
        · -- $b \diamond a = d$
          have hdv : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hik : Idempotent (b / a) := hdv ▸ hidem d
          exact absurd (eq_of_mul_eq_div hik (hcs71.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = e$
          have hv84 : d * e = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs71))).symm.trans
              (eq677 d a)).trans hv70.symm)
          rcases hspan (c * a) with hcs85 | hcs85 | hcs85 | hcs85 | hcs85 | hcs85
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs85) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs85.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs85.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs85.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv86 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs85))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (d * b) with hcs87 | hcs87 | hcs87 | hcs87 | hcs87 | hcs87
            · -- $d \diamond b = a$
              have hdv1 : d / b = e := div_eq_iff_mul_eq.mpr hv86
              have hdv2 : d / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs71
              have hik : Idempotent (d / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs87.trans hdv2.symm)) (hbd.symm)
            · -- $d \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs87) (hbd.symm)
            · -- $d \diamond b = c$
              have hv88 : e * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                  ((congrArg (· * b) hv86).trans hcs87))).symm.trans
                  (eq677 e b)).trans hcs71.symm)
              have hdv : e / c = a := div_eq_iff_mul_eq.mpr hcs85
              have hik : Idempotent (e / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv88.trans hdv.symm)) (hce.symm)
            · -- $d \diamond b = d$
              exact absurd (mul_left_cancel (hcs87.trans (hidem d).eq.symm)) hbd
            · -- $d \diamond b = e$
              have hdv : d / b = e := div_eq_iff_mul_eq.mpr hv86
              have hik : Idempotent (d / b) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs87.trans hdv.symm)) (hbd.symm)
            · -- $d \diamond b = f$
              exact absurd (mul_left_cancel (hcs87.trans hv84.symm)) hbe
          · -- $c \diamond a = f$
            have hv89 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs85))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * c) with hcs90 | hcs90 | hcs90 | hcs90 | hcs90 | hcs90
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs90
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs90.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs90) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs90.trans hv89.symm)) hcf
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs90.trans hcs71.symm)) (hac.symm)
            · -- $b \diamond c = f$
              rcases hspan (b * d) with hcs91 | hcs91 | hcs91 | hcs91 | hcs91 | hcs91
              · -- $b \diamond d = a$
                have hv92 : e * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs71))).symm.trans
                    (eq677 a b)).trans hcs91.symm)).trans hv70.symm)
                have hv93 : d * c = f :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs91).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hv89.symm)
                exact absurd (mul_left_cancel (hv93.trans hv84.symm)) hce
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs91.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv94 : c * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (d * ·) (congrArg (· * b) hcs91))).symm.trans
                    (eq677 d b)).trans hv89.symm)).trans hv84.symm)
                have hv95 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs91.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv89.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs71.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs90.symm)) (hce.symm)
                have hv96 : e * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs71))).symm.trans
                    (eq677 a b)).trans hv95.symm)).trans hcs33.symm)
                have hv97 : e * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hv95).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hcs71.symm)
                have hv98 : c * e = b :=
                  (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv94).trans
                    hv97)).trans hcs71)).symm.trans (eq677 b c)
                have hdv : c / e = b := div_eq_iff_mul_eq.mpr hv96
                have hik : Idempotent (c / e) := hdv ▸ hidem b
                exact absurd (eq_of_mul_eq_div hik (hv98.trans hdv.symm)) hce
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs91.trans hv89.symm)) hdf
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs91.trans hcs71.symm)) (had.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs91.trans hcs90.symm)) (hcd.symm)
        · -- $b \diamond a = f$
          have hdv1 : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hdv2 : b / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv70
          have hik : Idempotent (b / a / a) := hdv2 ▸ hidem f
          exact absurd (eq_of_mul_eq_div_div hik (hcs71.trans hdv2.symm)) (hab.symm)
      · -- $a \diamond c = f$
        exact absurd (mul_left_cancel (hcs33.trans hcs2.symm)) hce
  · -- $a \diamond d = c$
    exact absurd (mul_left_cancel (hcs1.trans hc.symm.symm)) (hbd.symm)
  · -- $a \diamond d = d$
    exact absurd (eq_of_mul_eq_self_right (hidem d) hcs1) had
  · -- $a \diamond d = e$
    rcases hspan (a * f) with hcs99 | hcs99 | hcs99 | hcs99 | hcs99 | hcs99
    · -- $a \diamond f = a$
      exact absurd (mul_left_cancel (hcs99.trans (hidem a).eq.symm)) (haf.symm)
    · -- $a \diamond f = b$
      rcases hspan (a * c) with hcs100 | hcs100 | hcs100 | hcs100 | hcs100 | hcs100
      · -- $a \diamond c = a$
        exact absurd (mul_left_cancel (hcs100.trans (hidem a).eq.symm)) (hac.symm)
      · -- $a \diamond c = b$
        exact absurd (mul_left_cancel (hcs100.trans hcs99.symm)) hcf
      · -- $a \diamond c = c$
        exact absurd (mul_left_cancel (hcs100.trans hc.symm.symm)) (hbc.symm)
      · -- $a \diamond c = d$
        have hv101 : a * e = f := by
          rcases hspan (a * e) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (hae.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs99.symm)) hef
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbe.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs100.symm)) (hce.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hde.symm)
          · exact hz
        rcases hspan (b * a) with hcs102 | hcs102 | hcs102 | hcs102 | hcs102 | hcs102
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs102) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs102.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv103 : f * c = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs102))).symm.trans
              (eq677 f a)).trans hv101.symm)
          rcases hspan (c * a) with hcs104 | hcs104 | hcs104 | hcs104 | hcs104 | hcs104
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs104) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs104.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs104.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv105 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs104))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (b * e) with hcs106 | hcs106 | hcs106 | hcs106 | hcs106 | hcs106
            · -- $b \diamond e = a$
              have hv107 : c * b = d :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs102))).symm.trans
                  (eq677 a b)).trans hcs106.symm)).trans hcs1.symm)
              exact absurd (mul_left_cancel (hv107.trans hcs104.symm)) (hab.symm)
            · -- $b \diamond e = b$
              exact absurd (mul_left_cancel (hcs106.trans (hidem b).eq.symm)) (hbe.symm)
            · -- $b \diamond e = c$
              exact absurd (mul_left_cancel (hcs106.trans hcs102.symm)) (hae.symm)
            · -- $b \diamond e = d$
              rcases hspan (b * c) with hcs108 | hcs108 | hcs108 | hcs108 | hcs108 | hcs108
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs108
                have hik : Idempotent (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs108.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs108.trans hcs102.symm)) (hac.symm)
              · -- $b \diamond c = d$
                exact absurd (mul_left_cancel (hcs108.trans hcs106.symm)) hce
              · -- $b \diamond c = e$
                have hv109 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs102.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs106.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs108.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv105.symm)) (hdf.symm)
                have hv110 : c * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs102))).symm.trans
                    (eq677 a b)).trans hv109.symm)).trans hv101.symm)
                have hv111 : b * e = f :=
                  (congrArg (b * ·) ((congrArg (f * ·) ((congrArg (· * b) hv109).trans
                    hc.symm)).trans hv103)).symm.trans (eq677 f b)
                exact absurd (hv111.symm.trans hcs106) (hdf.symm)
              · -- $b \diamond c = f$
                exact absurd (mul_left_cancel (hcs108.trans hv105.symm)) hcd
            · -- $b \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs106) hbe
            · -- $b \diamond e = f$
              exact absurd (mul_left_cancel (hcs106.trans hv105.symm)) (hde.symm)
          · -- $c \diamond a = e$
            have hv112 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs104))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (b * d) with hcs113 | hcs113 | hcs113 | hcs113 | hcs113 | hcs113
            · -- $b \diamond d = a$
              have hv114 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs102))).symm.trans
                  (eq677 a b)).trans hcs113.symm)).trans hcs100.symm)
              exact absurd (mul_left_cancel (hv114.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond d = b$
              exact absurd (mul_left_cancel (hcs113.trans (hidem b).eq.symm)) (hbd.symm)
            · -- $b \diamond d = c$
              exact absurd (mul_left_cancel (hcs113.trans hcs102.symm)) (had.symm)
            · -- $b \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs113) hbd
            · -- $b \diamond d = e$
              have e1 : b * d = a * d := hcs113.trans hcs1.symm
              have e2 : b * (a * d) = a * (a * d) := by
                rw [hcs1]
                exact hv112.trans hv101.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
            · -- $b \diamond d = f$
              exact absurd (mul_left_cancel (hcs113.trans hv112.symm)) hde
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs104.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = d$
          have hv115 : f * d = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs102))).symm.trans
              (eq677 f a)).trans hv101.symm)
          rcases hspan (c * a) with hcs116 | hcs116 | hcs116 | hcs116 | hcs116 | hcs116
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs116) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs116.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs116.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv117 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs116))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (f * b) with hcs118 | hcs118 | hcs118 | hcs118 | hcs118 | hcs118
            · -- $f \diamond b = a$
              have hdv1 : f / b = d := div_eq_iff_mul_eq.mpr hv117
              have hdv2 : f / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs102
              have hik : Idempotent (f / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs118.trans hdv2.symm)) (hbf.symm)
            · -- $f \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs118) (hbf.symm)
            · -- $f \diamond b = c$
              have hv119 : d * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                  ((congrArg (· * b) hv117).trans hcs118))).symm.trans
                  (eq677 d b)).trans hcs102.symm)
              have hdv : d / c = a := div_eq_iff_mul_eq.mpr hcs116
              have hik : Idempotent (d / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv119.trans hdv.symm)) (hcd.symm)
            · -- $f \diamond b = d$
              have hdv : f / b = d := div_eq_iff_mul_eq.mpr hv117
              have hik : Idempotent (f / b) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hcs118.trans hdv.symm)) (hbf.symm)
            · -- $f \diamond b = e$
              exact absurd (mul_left_cancel (hcs118.trans hv115.symm)) hbd
            · -- $f \diamond b = f$
              exact absurd (mul_left_cancel (hcs118.trans (hidem f).eq.symm)) hbf
          · -- $c \diamond a = e$
            have hv120 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs116))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (b * c) with hcs121 | hcs121 | hcs121 | hcs121 | hcs121 | hcs121
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs121
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs121.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs121) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs121.trans hcs102.symm)) (hac.symm)
            · -- $b \diamond c = e$
              rcases hspan (b * d) with hcs122 | hcs122 | hcs122 | hcs122 | hcs122 | hcs122
              · -- $b \diamond d = a$
                have hv123 : d * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs102))).symm.trans
                    (eq677 a b)).trans hcs122.symm)).trans hcs100.symm)
                have hv124 : d * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs122).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hcs102.symm)
                have hv125 : c * e = b :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (c * ·)
                    ((congrArg (· * d) hv124).trans hcs1))).symm.trans
                    (eq677 c d)).trans hv123.symm)
                have hdv : b / c = e := div_eq_iff_mul_eq.mpr hv125
                have hik : Idempotent (b / c) := hdv ▸ hidem e
                exact absurd (eq_of_mul_eq_div hik (hcs121.trans hdv.symm)) hbc
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs122.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv126 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs122.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs102.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs121.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv120.symm)) (hef.symm)
                have hv127 : d * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs102))).symm.trans
                    (eq677 a b)).trans hv126.symm)).trans hv101.symm)
                have hv128 : f * c = e :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv126).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hv120.symm)
                exact absurd (mul_left_cancel (hv128.trans hv115.symm)) hcd
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs122.trans hcs102.symm)) (had.symm)
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs122.trans hcs121.symm)) (hcd.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs122.trans hv120.symm)) hde
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs121.trans hv120.symm)) hce
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs116.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = e$
          have hdv1 : b / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hdv2 : b / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv101
          have hik : Idempotent (b / a / a) := hdv2 ▸ hidem e
          exact absurd (eq_of_mul_eq_div_div hik (hcs102.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = f$
          have hdv : b / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hik : Idempotent (b / a) := hdv ▸ hidem f
          exact absurd (eq_of_mul_eq_div hik (hcs102.trans hdv.symm)) (hab.symm)
      · -- $a \diamond c = e$
        exact absurd (mul_left_cancel (hcs100.trans hcs1.symm)) hcd
      · -- $a \diamond c = f$
        have hv129 : a * e = d := by
          rcases hspan (a * e) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (hae.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs99.symm)) hef
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbe.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hde.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs100.symm)) (hce.symm)
        rcases hspan (b * a) with hcs130 | hcs130 | hcs130 | hcs130 | hcs130 | hcs130
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs130) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs130.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hdv1 : b / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hdv2 : b / a / a = c := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs100
          have hik : Idempotent (b / a / a) := hdv2 ▸ hidem c
          exact absurd (eq_of_mul_eq_div_div hik (hcs130.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = d$
          have hv131 : f * d = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs130))).symm.trans
              (eq677 f a)).trans hcs100.symm)
          rcases hspan (c * a) with hcs132 | hcs132 | hcs132 | hcs132 | hcs132 | hcs132
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs132) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs132.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs132.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv133 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs132))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (f * b) with hcs134 | hcs134 | hcs134 | hcs134 | hcs134 | hcs134
            · -- $f \diamond b = a$
              have hdv1 : f / b = d := div_eq_iff_mul_eq.mpr hv133
              have hdv2 : f / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs130
              have hik : Idempotent (f / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs134.trans hdv2.symm)) (hbf.symm)
            · -- $f \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs134) (hbf.symm)
            · -- $f \diamond b = c$
              exact absurd (mul_left_cancel (hcs134.trans hv131.symm)) hbd
            · -- $f \diamond b = d$
              have hdv : f / b = d := div_eq_iff_mul_eq.mpr hv133
              have hik : Idempotent (f / b) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hcs134.trans hdv.symm)) (hbf.symm)
            · -- $f \diamond b = e$
              have hv135 : d * e = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                  ((congrArg (· * b) hv133).trans hcs134))).symm.trans
                  (eq677 d b)).trans hcs130.symm)
              have hdv : a / d = e := div_eq_iff_mul_eq.mpr hv135
              have hik : Idempotent (a / d) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
            · -- $f \diamond b = f$
              exact absurd (mul_left_cancel (hcs134.trans (hidem f).eq.symm)) hbf
          · -- $c \diamond a = e$
            have hv136 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs132))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (b * c) with hcs137 | hcs137 | hcs137 | hcs137 | hcs137 | hcs137
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs137
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs137.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs137) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs137.trans hcs130.symm)) (hac.symm)
            · -- $b \diamond c = e$
              rcases hspan (b * d) with hcs138 | hcs138 | hcs138 | hcs138 | hcs138 | hcs138
              · -- $b \diamond d = a$
                have hv139 : d * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs130))).symm.trans
                    (eq677 a b)).trans hcs138.symm)).trans hv129.symm)
                have hv140 : d * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs138).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hcs130.symm)
                have hv141 : b * f = c := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs138.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs130.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs137.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv136.symm)) (hef.symm)
                have hv142 : e * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (d * ·) (congrArg (· * a) hcs1))).symm.trans
                    (eq677 d a)).trans hv129.symm)).trans hv139.symm)
                have hv143 : e * b = a :=
                  (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hv142).trans
                    hv136)).trans hcs99)).symm.trans (eq677 a e)
                have hv144 : b * e = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs137).trans
                    hv143)).trans hcs132)).symm.trans (eq677 c b)
                exact absurd (hv144.symm.trans hv136) hcf
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs138.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv145 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs138.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs130.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs137.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv136.symm)) (hef.symm)
                have hv146 : d * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs130))).symm.trans
                    (eq677 a b)).trans hv145.symm)).trans hcs100.symm)
                have hv147 : f * c = e :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv145).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hv136.symm)
                have e1 : f * d = b * d := hv131.trans hcs138.symm
                have e2 : f * (b * d) = b * (b * d) := by
                  rw [hcs138]
                  exact hv147.trans hcs137.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbf.symm)
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs138.trans hcs130.symm)) (had.symm)
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs138.trans hcs137.symm)) (hcd.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs138.trans hv136.symm)) hde
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs137.trans hv136.symm)) hce
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs132.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = e$
          have hv148 : f * e = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs130))).symm.trans
              (eq677 f a)).trans hcs100.symm)
          rcases hspan (c * a) with hcs149 | hcs149 | hcs149 | hcs149 | hcs149 | hcs149
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs149) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs149.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs149.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv150 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs149))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (b * c) with hcs151 | hcs151 | hcs151 | hcs151 | hcs151 | hcs151
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs151
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs151.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs151) hbc
            · -- $b \diamond c = d$
              rcases hspan (b * e) with hcs152 | hcs152 | hcs152 | hcs152 | hcs152 | hcs152
              · -- $b \diamond e = a$
                have hv153 : e * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs130))).symm.trans
                    (eq677 a b)).trans hcs152.symm)).trans hcs1.symm)
                have hv154 : e * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hcs152).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hcs130.symm)
                have hv155 : b * f = c := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs152.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs151.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs130.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv150.symm)) (hdf.symm)
                have hv156 : d * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (e * ·) (congrArg (· * a) hv129))).symm.trans
                    (eq677 e a)).trans hcs1.symm)).trans hv153.symm)
                have hv157 : d * b = a :=
                  (congrArg (d * ·) ((congrArg (a * ·) ((congrArg (· * d) hv156).trans
                    hv150)).trans hcs99)).symm.trans (eq677 a d)
                have hv158 : b * d = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs151).trans
                    hv157)).trans hcs149)).symm.trans (eq677 c b)
                exact absurd (hv158.symm.trans hv150) hcf
              · -- $b \diamond e = b$
                exact absurd (mul_left_cancel (hcs152.trans (hidem b).eq.symm)) (hbe.symm)
              · -- $b \diamond e = c$
                have hv159 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs152.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs151.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs130.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv150.symm)) (hdf.symm)
                have hv160 : e * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs130))).symm.trans
                    (eq677 a b)).trans hv159.symm)).trans hcs100.symm)
                have hv161 : f * c = d :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv159).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hv150.symm)
                have e1 : f * e = b * e := hv148.trans hcs152.symm
                have e2 : f * (b * e) = b * (b * e) := by
                  rw [hcs152]
                  exact hv161.trans hcs151.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbf.symm)
              · -- $b \diamond e = d$
                exact absurd (mul_left_cancel (hcs152.trans hcs151.symm)) (hce.symm)
              · -- $b \diamond e = e$
                exact absurd (mul_left_cancel (hcs152.trans hcs130.symm)) (hae.symm)
              · -- $b \diamond e = f$
                exact absurd (mul_left_cancel (hcs152.trans hv150.symm)) (hde.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs151.trans hcs130.symm)) (hac.symm)
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs151.trans hv150.symm)) hcd
          · -- $c \diamond a = e$
            have hv162 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs149))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (f * b) with hcs163 | hcs163 | hcs163 | hcs163 | hcs163 | hcs163
            · -- $f \diamond b = a$
              have hdv1 : f / b = e := div_eq_iff_mul_eq.mpr hv162
              have hdv2 : f / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs130
              have hik : Idempotent (f / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs163.trans hdv2.symm)) (hbf.symm)
            · -- $f \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs163) (hbf.symm)
            · -- $f \diamond b = c$
              exact absurd (mul_left_cancel (hcs163.trans hv148.symm)) hbe
            · -- $f \diamond b = d$
              have hv164 : e * d = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                  ((congrArg (· * b) hv162).trans hcs163))).symm.trans
                  (eq677 e b)).trans hcs130.symm)
              have hdv : a / e = d := div_eq_iff_mul_eq.mpr hv164
              have hik : Idempotent (a / e) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hv129.trans hdv.symm)) hae
            · -- $f \diamond b = e$
              have hdv : f / b = e := div_eq_iff_mul_eq.mpr hv162
              have hik : Idempotent (f / b) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs163.trans hdv.symm)) (hbf.symm)
            · -- $f \diamond b = f$
              exact absurd (mul_left_cancel (hcs163.trans (hidem f).eq.symm)) hbf
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs149.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = f$
          have hdv : b / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hik : Idempotent (b / a) := hdv ▸ hidem f
          exact absurd (eq_of_mul_eq_div hik (hcs130.trans hdv.symm)) (hab.symm)
    · -- $a \diamond f = c$
      exact absurd (mul_left_cancel (hcs99.trans hc.symm.symm)) (hbf.symm)
    · -- $a \diamond f = d$
      rcases hspan (a * c) with hcs165 | hcs165 | hcs165 | hcs165 | hcs165 | hcs165
      · -- $a \diamond c = a$
        exact absurd (mul_left_cancel (hcs165.trans (hidem a).eq.symm)) (hac.symm)
      · -- $a \diamond c = b$
        have hv166 : a * e = f := by
          rcases hspan (a * e) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (hae.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs165.symm)) (hce.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbe.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs99.symm)) hef
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hde.symm)
          · exact hz
        rcases hspan (d * a) with hcs167 | hcs167 | hcs167 | hcs167 | hcs167 | hcs167
        · -- $d \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs167) (had.symm)
        · -- $d \diamond a = b$
          have hv168 : f * b = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs167))).symm.trans
              (eq677 f a)).trans hv166.symm)
          rcases hspan (e * a) with hcs169 | hcs169 | hcs169 | hcs169 | hcs169 | hcs169
          · -- $e \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs169) (hae.symm)
          · -- $e \diamond a = b$
            have hv170 : d * b = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
                ((congrArg (· * a) hcs1).trans hcs169))).symm.trans
                (eq677 d a)).trans hcs99.symm)
            rcases hspan (f * d) with hcs171 | hcs171 | hcs171 | hcs171 | hcs171 | hcs171
            · -- $f \diamond d = a$
              have hdv1 : f / d = b := div_eq_iff_mul_eq.mpr hv170
              have hdv2 : f / d / d = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs167
              have hik : Idempotent (f / d / d) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs171.trans hdv2.symm)) (hdf.symm)
            · -- $f \diamond d = b$
              have hdv : f / d = b := div_eq_iff_mul_eq.mpr hv170
              have hik : Idempotent (f / d) := hdv ▸ hidem b
              exact absurd (eq_of_mul_eq_div hik (hcs171.trans hdv.symm)) (hdf.symm)
            · -- $f \diamond d = c$
              have hv172 : b * c = a :=
                mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
                  ((congrArg (· * d) hv170).trans hcs171))).symm.trans
                  (eq677 b d)).trans hcs167.symm)
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hv172
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $f \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs171) (hdf.symm)
            · -- $f \diamond d = e$
              exact absurd (mul_left_cancel (hcs171.trans hv168.symm)) (hbd.symm)
            · -- $f \diamond d = f$
              exact absurd (mul_left_cancel (hcs171.trans (hidem f).eq.symm)) hdf
          · -- $e \diamond a = c$
            have hv173 : d * c = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
                ((congrArg (· * a) hcs1).trans hcs169))).symm.trans
                (eq677 d a)).trans hcs99.symm)
            rcases hspan (d * e) with hcs174 | hcs174 | hcs174 | hcs174 | hcs174 | hcs174
            · -- $d \diamond e = a$
              have hdv : a / d = e := div_eq_iff_mul_eq.mpr hcs174
              have hik : Idempotent (a / d) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
            · -- $d \diamond e = b$
              exact absurd (mul_left_cancel (hcs174.trans hcs167.symm)) (hae.symm)
            · -- $d \diamond e = c$
              rcases hspan (d * b) with hcs175 | hcs175 | hcs175 | hcs175 | hcs175 | hcs175
              · -- $d \diamond b = a$
                have hv176 : b * d = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                    (congrArg (a * ·) (congrArg (· * d) hcs167))).symm.trans
                    (eq677 a d)).trans hcs175.symm)).trans hcs165.symm)
                have hv177 : b * e = a :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
                    ((congrArg (· * d) hcs175).trans hcs1))).symm.trans
                    (eq677 b d)).trans hcs167.symm)
                have hv178 : d * f = e := by
                  rcases hspan (d * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs175.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs167.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs174.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem d).eq.symm)) (hdf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hv173.symm)) (hcf.symm)
                have hv179 : c * a = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
                    (eq677 b a)).trans hcs165.symm)).trans hv176.symm)
                have hv180 : c * d = a :=
                  (congrArg (c * ·) ((congrArg (a * ·) ((congrArg (· * c) hv179).trans
                    hv173)).trans hcs99)).symm.trans (eq677 a c)
                have hv181 : d * c = e :=
                  (congrArg (d * ·) ((congrArg (e * ·) ((congrArg (· * d) hcs174).trans
                    hv180)).trans hcs169)).symm.trans (eq677 e d)
                exact absurd (hv181.symm.trans hv173) hef
              · -- $d \diamond b = b$
                exact absurd (mul_left_cancel (hcs175.trans hcs167.symm)) (hab.symm)
              · -- $d \diamond b = c$
                exact absurd (mul_left_cancel (hcs175.trans hcs174.symm)) hbe
              · -- $d \diamond b = d$
                exact absurd (mul_left_cancel (hcs175.trans (hidem d).eq.symm)) hbd
              · -- $d \diamond b = e$
                have hv182 : d * f = a := by
                  rcases hspan (d * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs167.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs174.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem d).eq.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs175.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv173.symm)) (hcf.symm)
                have hv183 : b * d = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                    (congrArg (a * ·) (congrArg (· * d) hcs167))).symm.trans
                    (eq677 a d)).trans hv182.symm)).trans hv166.symm)
                have hv184 : f * e = c :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (f * ·)
                    ((congrArg (· * d) hv182).trans hcs1))).symm.trans
                    (eq677 f d)).trans hv173.symm)
                have e1 : f * b = d * b := hv168.trans hcs175.symm
                have e2 : f * (d * b) = d * (d * b) := by
                  rw [hcs175]
                  exact hv184.trans hcs174.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hdf.symm)
              · -- $d \diamond b = f$
                exact absurd (mul_left_cancel (hcs175.trans hv173.symm)) hbc
            · -- $d \diamond e = d$
              exact absurd (mul_left_cancel (hcs174.trans (hidem d).eq.symm)) (hde.symm)
            · -- $d \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs174) hde
            · -- $d \diamond e = f$
              exact absurd (mul_left_cancel (hcs174.trans hv173.symm)) (hce.symm)
          · -- $e \diamond a = d$
            have hdv : e / a = d := div_eq_iff_mul_eq.mpr hcs1
            have hik : Idempotent (e / a) := hdv ▸ hidem d
            exact absurd (eq_of_mul_eq_div hik (hcs169.trans hdv.symm)) (hae.symm)
          · -- $e \diamond a = e$
            exact absurd (mul_left_cancel (hcs169.trans (hidem e).eq.symm)) hae
          · -- $e \diamond a = f$
            have hdv1 : e / a = d := div_eq_iff_mul_eq.mpr hcs1
            have hdv2 : e / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : Idempotent (e / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs169.trans hdv2.symm)) (hae.symm)
        · -- $d \diamond a = c$
          have hv185 : f * c = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs167))).symm.trans
              (eq677 f a)).trans hv166.symm)
          rcases hspan (e * a) with hcs186 | hcs186 | hcs186 | hcs186 | hcs186 | hcs186
          · -- $e \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs186) (hae.symm)
          · -- $e \diamond a = b$
            have hv187 : d * b = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
                ((congrArg (· * a) hcs1).trans hcs186))).symm.trans
                (eq677 d a)).trans hcs99.symm)
            rcases hspan (d * e) with hcs188 | hcs188 | hcs188 | hcs188 | hcs188 | hcs188
            · -- $d \diamond e = a$
              have hdv : a / d = e := div_eq_iff_mul_eq.mpr hcs188
              have hik : Idempotent (a / d) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
            · -- $d \diamond e = b$
              rcases hspan (d * c) with hcs189 | hcs189 | hcs189 | hcs189 | hcs189 | hcs189
              · -- $d \diamond c = a$
                have hv190 : c * d = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                    (congrArg (a * ·) (congrArg (· * d) hcs167))).symm.trans
                    (eq677 a d)).trans hcs189.symm)).trans hc.symm.symm)
                have hv191 : c * e = a :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (c * ·)
                    ((congrArg (· * d) hcs189).trans hcs1))).symm.trans
                    (eq677 c d)).trans hcs167.symm)
                have hv192 : d * f = e := by
                  rcases hspan (d * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs189.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs188.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs167.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem d).eq.symm)) (hdf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hv187.symm)) (hbf.symm)
                have hv193 : b * a = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (c * ·) (congrArg (· * a) hcs165))).symm.trans
                    (eq677 c a)).trans hc.symm.symm)).trans hv190.symm)
                have hv194 : b * d = a :=
                  (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hv193).trans
                    hv187)).trans hcs99)).symm.trans (eq677 a b)
                have hv195 : d * b = e :=
                  (congrArg (d * ·) ((congrArg (e * ·) ((congrArg (· * d) hcs188).trans
                    hv194)).trans hcs186)).symm.trans (eq677 e d)
                exact absurd (hv195.symm.trans hv187) hef
              · -- $d \diamond c = b$
                exact absurd (mul_left_cancel (hcs189.trans hcs188.symm)) hce
              · -- $d \diamond c = c$
                exact absurd (mul_left_cancel (hcs189.trans hcs167.symm)) (hac.symm)
              · -- $d \diamond c = d$
                exact absurd (mul_left_cancel (hcs189.trans (hidem d).eq.symm)) hcd
              · -- $d \diamond c = e$
                have hv196 : d * f = a := by
                  rcases hspan (d * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs188.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs167.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem d).eq.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs189.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv187.symm)) (hbf.symm)
                have hv197 : c * d = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                    (congrArg (a * ·) (congrArg (· * d) hcs167))).symm.trans
                    (eq677 a d)).trans hv196.symm)).trans hv166.symm)
                have hv198 : f * e = b :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (f * ·)
                    ((congrArg (· * d) hv196).trans hcs1))).symm.trans
                    (eq677 f d)).trans hv187.symm)
                have e1 : f * c = d * c := hv185.trans hcs189.symm
                have e2 : f * (d * c) = d * (d * c) := by
                  rw [hcs189]
                  exact hv198.trans hcs188.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hdf.symm)
              · -- $d \diamond c = f$
                exact absurd (mul_left_cancel (hcs189.trans hv187.symm)) (hbc.symm)
            · -- $d \diamond e = c$
              exact absurd (mul_left_cancel (hcs188.trans hcs167.symm)) (hae.symm)
            · -- $d \diamond e = d$
              exact absurd (mul_left_cancel (hcs188.trans (hidem d).eq.symm)) (hde.symm)
            · -- $d \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs188) hde
            · -- $d \diamond e = f$
              exact absurd (mul_left_cancel (hcs188.trans hv187.symm)) (hbe.symm)
          · -- $e \diamond a = c$
            have hv199 : d * c = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
                ((congrArg (· * a) hcs1).trans hcs186))).symm.trans
                (eq677 d a)).trans hcs99.symm)
            rcases hspan (f * d) with hcs200 | hcs200 | hcs200 | hcs200 | hcs200 | hcs200
            · -- $f \diamond d = a$
              have hdv1 : f / d = c := div_eq_iff_mul_eq.mpr hv199
              have hdv2 : f / d / d = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs167
              have hik : Idempotent (f / d / d) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs200.trans hdv2.symm)) (hdf.symm)
            · -- $f \diamond d = b$
              have hv201 : c * b = a :=
                mul_left_cancel (((congrArg (d * ·) (congrArg (c * ·)
                  ((congrArg (· * d) hv199).trans hcs200))).symm.trans
                  (eq677 c d)).trans hcs167.symm)
              have hdv : a / c = b := div_eq_iff_mul_eq.mpr hv201
              have hik : Idempotent (a / c) := hdv ▸ hidem b
              exact absurd (eq_of_mul_eq_div hik (hcs165.trans hdv.symm)) hac
            · -- $f \diamond d = c$
              have hdv : f / d = c := div_eq_iff_mul_eq.mpr hv199
              have hik : Idempotent (f / d) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hcs200.trans hdv.symm)) (hdf.symm)
            · -- $f \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs200) (hdf.symm)
            · -- $f \diamond d = e$
              exact absurd (mul_left_cancel (hcs200.trans hv185.symm)) (hcd.symm)
            · -- $f \diamond d = f$
              exact absurd (mul_left_cancel (hcs200.trans (hidem f).eq.symm)) hdf
          · -- $e \diamond a = d$
            have hdv : e / a = d := div_eq_iff_mul_eq.mpr hcs1
            have hik : Idempotent (e / a) := hdv ▸ hidem d
            exact absurd (eq_of_mul_eq_div hik (hcs186.trans hdv.symm)) (hae.symm)
          · -- $e \diamond a = e$
            exact absurd (mul_left_cancel (hcs186.trans (hidem e).eq.symm)) hae
          · -- $e \diamond a = f$
            have hdv1 : e / a = d := div_eq_iff_mul_eq.mpr hcs1
            have hdv2 : e / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : Idempotent (e / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs186.trans hdv2.symm)) (hae.symm)
        · -- $d \diamond a = d$
          exact absurd (mul_left_cancel (hcs167.trans (hidem d).eq.symm)) had
        · -- $d \diamond a = e$
          have hdv1 : d / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hdv2 : d / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv166
          have hik : Idempotent (d / a / a) := hdv2 ▸ hidem e
          exact absurd (eq_of_mul_eq_div_div hik (hcs167.trans hdv2.symm)) (had.symm)
        · -- $d \diamond a = f$
          have hdv : d / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hik : Idempotent (d / a) := hdv ▸ hidem f
          exact absurd (eq_of_mul_eq_div hik (hcs167.trans hdv.symm)) (had.symm)
      · -- $a \diamond c = c$
        exact absurd (mul_left_cancel (hcs165.trans hc.symm.symm)) (hbc.symm)
      · -- $a \diamond c = d$
        exact absurd (mul_left_cancel (hcs165.trans hcs99.symm)) hcf
      · -- $a \diamond c = e$
        exact absurd (mul_left_cancel (hcs165.trans hcs1.symm)) hcd
      · -- $a \diamond c = f$
        have hv202 : a * e = b := by
          rcases hspan (a * e) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (hae.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbe.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs99.symm)) hef
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hde.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs165.symm)) (hce.symm)
        rcases hspan (b * a) with hcs203 | hcs203 | hcs203 | hcs203 | hcs203 | hcs203
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs203) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs203.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv204 : e * c = d :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hv202).trans hcs203))).symm.trans
              (eq677 e a)).trans hcs1.symm)
          rcases hspan (c * a) with hcs205 | hcs205 | hcs205 | hcs205 | hcs205 | hcs205
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs205) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs205.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs205.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv206 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs205))).symm.trans
                (eq677 b a)).trans hv202.symm)
            rcases hspan (b * f) with hcs207 | hcs207 | hcs207 | hcs207 | hcs207 | hcs207
            · -- $b \diamond f = a$
              have hv208 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs203))).symm.trans
                  (eq677 a b)).trans hcs207.symm)).trans hcs165.symm)
              exact absurd (mul_left_cancel (hv208.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond f = b$
              exact absurd (mul_left_cancel (hcs207.trans (hidem b).eq.symm)) (hbf.symm)
            · -- $b \diamond f = c$
              exact absurd (mul_left_cancel (hcs207.trans hcs203.symm)) (haf.symm)
            · -- $b \diamond f = d$
              have e1 : b * f = a * f := hcs207.trans hcs99.symm
              have e2 : b * (a * f) = a * (a * f) := by
                rw [hcs99]
                exact hv206.trans hcs1.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
            · -- $b \diamond f = e$
              exact absurd (mul_left_cancel (hcs207.trans hv206.symm)) (hdf.symm)
            · -- $b \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs207) hbf
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv202
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs205.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv209 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs205))).symm.trans
                (eq677 b a)).trans hv202.symm)
            rcases hspan (b * d) with hcs210 | hcs210 | hcs210 | hcs210 | hcs210 | hcs210
            · -- $b \diamond d = a$
              have hv211 : c * b = f :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs203))).symm.trans
                  (eq677 a b)).trans hcs210.symm)).trans hcs99.symm)
              exact absurd (mul_left_cancel (hv211.trans hcs205.symm)) (hab.symm)
            · -- $b \diamond d = b$
              exact absurd (mul_left_cancel (hcs210.trans (hidem b).eq.symm)) (hbd.symm)
            · -- $b \diamond d = c$
              exact absurd (mul_left_cancel (hcs210.trans hcs203.symm)) (had.symm)
            · -- $b \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs210) hbd
            · -- $b \diamond d = e$
              exact absurd (mul_left_cancel (hcs210.trans hv209.symm)) hdf
            · -- $b \diamond d = f$
              rcases hspan (b * c) with hcs212 | hcs212 | hcs212 | hcs212 | hcs212 | hcs212
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs212
                have hik : Idempotent (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs212.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs212.trans hcs203.symm)) (hac.symm)
              · -- $b \diamond c = d$
                have hv213 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs203.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs212.symm)) (hce.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv209.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs210.symm)) (hde.symm)
                have hv214 : c * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs203))).symm.trans
                    (eq677 a b)).trans hv213.symm)).trans hcs1.symm)
                have hv215 : b * d = e :=
                  (congrArg (b * ·) ((congrArg (e * ·) ((congrArg (· * b) hv213).trans
                    hc.symm)).trans hv204)).symm.trans (eq677 e b)
                exact absurd (hv215.symm.trans hcs210) hef
              · -- $b \diamond c = e$
                exact absurd (mul_left_cancel (hcs212.trans hv209.symm)) hcf
              · -- $b \diamond c = f$
                exact absurd (mul_left_cancel (hcs212.trans hcs210.symm)) hcd
        · -- $b \diamond a = d$
          have hdv1 : b / a = e := div_eq_iff_mul_eq.mpr hv202
          have hdv2 : b / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
          have hik : Idempotent (b / a / a) := hdv2 ▸ hidem d
          exact absurd (eq_of_mul_eq_div_div hik (hcs203.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = e$
          have hdv : b / a = e := div_eq_iff_mul_eq.mpr hv202
          have hik : Idempotent (b / a) := hdv ▸ hidem e
          exact absurd (eq_of_mul_eq_div hik (hcs203.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = f$
          have hv216 : e * f = d :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hv202).trans hcs203))).symm.trans
              (eq677 e a)).trans hcs1.symm)
          rcases hspan (c * a) with hcs217 | hcs217 | hcs217 | hcs217 | hcs217 | hcs217
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs217) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs217.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs217.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv218 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs217))).symm.trans
                (eq677 b a)).trans hv202.symm)
            rcases hspan (b * c) with hcs219 | hcs219 | hcs219 | hcs219 | hcs219 | hcs219
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs219
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs219.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs219) hbc
            · -- $b \diamond c = d$
              rcases hspan (b * e) with hcs220 | hcs220 | hcs220 | hcs220 | hcs220 | hcs220
              · -- $b \diamond e = a$
                have hv221 : f * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs203))).symm.trans
                    (eq677 a b)).trans hcs220.symm)).trans hcs1.symm)
                have hv222 : e * c = d :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hcs220).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hv218.symm)
                exact absurd (mul_left_cancel (hv222.trans hv216.symm)) hcf
              · -- $b \diamond e = b$
                exact absurd (mul_left_cancel (hcs220.trans (hidem b).eq.symm)) (hbe.symm)
              · -- $b \diamond e = c$
                have hv223 : c * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (e * ·) (congrArg (· * b) hcs220))).symm.trans
                    (eq677 e b)).trans hv218.symm)).trans hv216.symm)
                have hv224 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs220.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs219.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv218.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs203.symm)) (haf.symm)
                have hv225 : f * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs203))).symm.trans
                    (eq677 a b)).trans hv224.symm)).trans hcs165.symm)
                have hv226 : f * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv224).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hcs203.symm)
                have hv227 : c * f = b :=
                  (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv223).trans
                    hv226)).trans hcs203)).symm.trans (eq677 b c)
                have hdv : c / f = b := div_eq_iff_mul_eq.mpr hv225
                have hik : Idempotent (c / f) := hdv ▸ hidem b
                exact absurd (eq_of_mul_eq_div hik (hv227.trans hdv.symm)) hcf
              · -- $b \diamond e = d$
                exact absurd (mul_left_cancel (hcs220.trans hcs219.symm)) (hce.symm)
              · -- $b \diamond e = e$
                exact absurd (mul_left_cancel (hcs220.trans hv218.symm)) (hde.symm)
              · -- $b \diamond e = f$
                exact absurd (mul_left_cancel (hcs220.trans hcs203.symm)) (hae.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs219.trans hv218.symm)) hcd
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs219.trans hcs203.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv202
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs217.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv228 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs217))).symm.trans
                (eq677 b a)).trans hv202.symm)
            rcases hspan (e * b) with hcs229 | hcs229 | hcs229 | hcs229 | hcs229 | hcs229
            · -- $e \diamond b = a$
              have hdv1 : e / b = f := div_eq_iff_mul_eq.mpr hv228
              have hdv2 : e / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs203
              have hik : Idempotent (e / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs229.trans hdv2.symm)) (hbe.symm)
            · -- $e \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs229) (hbe.symm)
            · -- $e \diamond b = c$
              have hv230 : f * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                  ((congrArg (· * b) hv228).trans hcs229))).symm.trans
                  (eq677 f b)).trans hcs203.symm)
              have hdv : f / c = a := div_eq_iff_mul_eq.mpr hcs217
              have hik : Idempotent (f / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv230.trans hdv.symm)) (hcf.symm)
            · -- $e \diamond b = d$
              exact absurd (mul_left_cancel (hcs229.trans hv216.symm)) hbf
            · -- $e \diamond b = e$
              exact absurd (mul_left_cancel (hcs229.trans (hidem e).eq.symm)) hbe
            · -- $e \diamond b = f$
              have hdv : e / b = f := div_eq_iff_mul_eq.mpr hv228
              have hik : Idempotent (e / b) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs229.trans hdv.symm)) (hbe.symm)
    · -- $a \diamond f = e$
      exact absurd (mul_left_cancel (hcs99.trans hcs1.symm)) (hdf.symm)
    · -- $a \diamond f = f$
      exact absurd (eq_of_mul_eq_self_right (hidem f) hcs99) haf
  · -- $a \diamond d = f$
    rcases hspan (a * e) with hcs231 | hcs231 | hcs231 | hcs231 | hcs231 | hcs231
    · -- $a \diamond e = a$
      exact absurd (mul_left_cancel (hcs231.trans (hidem a).eq.symm)) (hae.symm)
    · -- $a \diamond e = b$
      rcases hspan (a * c) with hcs232 | hcs232 | hcs232 | hcs232 | hcs232 | hcs232
      · -- $a \diamond c = a$
        exact absurd (mul_left_cancel (hcs232.trans (hidem a).eq.symm)) (hac.symm)
      · -- $a \diamond c = b$
        exact absurd (mul_left_cancel (hcs232.trans hcs231.symm)) hce
      · -- $a \diamond c = c$
        exact absurd (mul_left_cancel (hcs232.trans hc.symm.symm)) (hbc.symm)
      · -- $a \diamond c = d$
        have hv233 : a * f = e := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs231.symm)) (hef.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs232.symm)) (hcf.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
        rcases hspan (b * a) with hcs234 | hcs234 | hcs234 | hcs234 | hcs234 | hcs234
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs234) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs234.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv235 : e * c = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs234))).symm.trans
              (eq677 e a)).trans hv233.symm)
          rcases hspan (c * a) with hcs236 | hcs236 | hcs236 | hcs236 | hcs236 | hcs236
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs236) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs236.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs236.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv237 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs236))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (b * f) with hcs238 | hcs238 | hcs238 | hcs238 | hcs238 | hcs238
            · -- $b \diamond f = a$
              have hv239 : c * b = d :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs234))).symm.trans
                  (eq677 a b)).trans hcs238.symm)).trans hcs1.symm)
              exact absurd (mul_left_cancel (hv239.trans hcs236.symm)) (hab.symm)
            · -- $b \diamond f = b$
              exact absurd (mul_left_cancel (hcs238.trans (hidem b).eq.symm)) (hbf.symm)
            · -- $b \diamond f = c$
              exact absurd (mul_left_cancel (hcs238.trans hcs234.symm)) (haf.symm)
            · -- $b \diamond f = d$
              rcases hspan (b * c) with hcs240 | hcs240 | hcs240 | hcs240 | hcs240 | hcs240
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs240
                have hik : Idempotent (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs240.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs240.trans hcs234.symm)) (hac.symm)
              · -- $b \diamond c = d$
                exact absurd (mul_left_cancel (hcs240.trans hcs238.symm)) hcf
              · -- $b \diamond c = e$
                exact absurd (mul_left_cancel (hcs240.trans hv237.symm)) hcd
              · -- $b \diamond c = f$
                have hv241 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs234.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs238.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hv237.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs240.symm)) (hce.symm)
                have hv242 : c * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs234))).symm.trans
                    (eq677 a b)).trans hv241.symm)).trans hv233.symm)
                have hv243 : b * f = e :=
                  (congrArg (b * ·) ((congrArg (e * ·) ((congrArg (· * b) hv241).trans
                    hc.symm)).trans hv235)).symm.trans (eq677 e b)
                exact absurd (hv243.symm.trans hcs238) (hde.symm)
            · -- $b \diamond f = e$
              exact absurd (mul_left_cancel (hcs238.trans hv237.symm)) (hdf.symm)
            · -- $b \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs238) hbf
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs231
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs236.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv244 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs236))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (b * d) with hcs245 | hcs245 | hcs245 | hcs245 | hcs245 | hcs245
            · -- $b \diamond d = a$
              have hv246 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs234))).symm.trans
                  (eq677 a b)).trans hcs245.symm)).trans hcs232.symm)
              exact absurd (mul_left_cancel (hv246.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond d = b$
              exact absurd (mul_left_cancel (hcs245.trans (hidem b).eq.symm)) (hbd.symm)
            · -- $b \diamond d = c$
              exact absurd (mul_left_cancel (hcs245.trans hcs234.symm)) (had.symm)
            · -- $b \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs245) hbd
            · -- $b \diamond d = e$
              exact absurd (mul_left_cancel (hcs245.trans hv244.symm)) hdf
            · -- $b \diamond d = f$
              have e1 : b * d = a * d := hcs245.trans hcs1.symm
              have e2 : b * (a * d) = a * (a * d) := by
                rw [hcs1]
                exact hv244.trans hv233.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
        · -- $b \diamond a = d$
          have hv247 : e * d = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs234))).symm.trans
              (eq677 e a)).trans hv233.symm)
          rcases hspan (c * a) with hcs248 | hcs248 | hcs248 | hcs248 | hcs248 | hcs248
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs248) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs248.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs248.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv249 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs248))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (e * b) with hcs250 | hcs250 | hcs250 | hcs250 | hcs250 | hcs250
            · -- $e \diamond b = a$
              have hdv1 : e / b = d := div_eq_iff_mul_eq.mpr hv249
              have hdv2 : e / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs234
              have hik : Idempotent (e / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs250.trans hdv2.symm)) (hbe.symm)
            · -- $e \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs250) (hbe.symm)
            · -- $e \diamond b = c$
              have hv251 : d * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                  ((congrArg (· * b) hv249).trans hcs250))).symm.trans
                  (eq677 d b)).trans hcs234.symm)
              have hdv : d / c = a := div_eq_iff_mul_eq.mpr hcs248
              have hik : Idempotent (d / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv251.trans hdv.symm)) (hcd.symm)
            · -- $e \diamond b = d$
              have hdv : e / b = d := div_eq_iff_mul_eq.mpr hv249
              have hik : Idempotent (e / b) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hcs250.trans hdv.symm)) (hbe.symm)
            · -- $e \diamond b = e$
              exact absurd (mul_left_cancel (hcs250.trans (hidem e).eq.symm)) hbe
            · -- $e \diamond b = f$
              exact absurd (mul_left_cancel (hcs250.trans hv247.symm)) hbd
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs231
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs248.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv252 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs248))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (b * c) with hcs253 | hcs253 | hcs253 | hcs253 | hcs253 | hcs253
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs253
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs253.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs253) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs253.trans hcs234.symm)) (hac.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs253.trans hv252.symm)) hcf
            · -- $b \diamond c = f$
              rcases hspan (b * d) with hcs254 | hcs254 | hcs254 | hcs254 | hcs254 | hcs254
              · -- $b \diamond d = a$
                have hv255 : d * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs234))).symm.trans
                    (eq677 a b)).trans hcs254.symm)).trans hcs232.symm)
                have hv256 : d * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs254).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hcs234.symm)
                have hv257 : c * f = b :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (c * ·)
                    ((congrArg (· * d) hv256).trans hcs1))).symm.trans
                    (eq677 c d)).trans hv255.symm)
                have hdv : b / c = f := div_eq_iff_mul_eq.mpr hv257
                have hik : Idempotent (b / c) := hdv ▸ hidem f
                exact absurd (eq_of_mul_eq_div hik (hcs253.trans hdv.symm)) hbc
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs254.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv258 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs254.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs234.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv252.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs253.symm)) (hce.symm)
                have hv259 : d * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs234))).symm.trans
                    (eq677 a b)).trans hv258.symm)).trans hv233.symm)
                have hv260 : e * c = f :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hv258).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hv252.symm)
                exact absurd (mul_left_cancel (hv260.trans hv247.symm)) hcd
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs254.trans hcs234.symm)) (had.symm)
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs254.trans hv252.symm)) hdf
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs254.trans hcs253.symm)) (hcd.symm)
        · -- $b \diamond a = e$
          have hdv : b / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hik : Idempotent (b / a) := hdv ▸ hidem e
          exact absurd (eq_of_mul_eq_div hik (hcs234.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = f$
          have hdv1 : b / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hdv2 : b / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv233
          have hik : Idempotent (b / a / a) := hdv2 ▸ hidem f
          exact absurd (eq_of_mul_eq_div_div hik (hcs234.trans hdv2.symm)) (hab.symm)
      · -- $a \diamond c = e$
        have hv261 : a * f = d := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs231.symm)) (hef.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs232.symm)) (hcf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
        rcases hspan (b * a) with hcs262 | hcs262 | hcs262 | hcs262 | hcs262 | hcs262
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs262) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs262.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hdv1 : b / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hdv2 : b / a / a = c := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs232
          have hik : Idempotent (b / a / a) := hdv2 ▸ hidem c
          exact absurd (eq_of_mul_eq_div_div hik (hcs262.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = d$
          have hv263 : e * d = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs262))).symm.trans
              (eq677 e a)).trans hcs232.symm)
          rcases hspan (c * a) with hcs264 | hcs264 | hcs264 | hcs264 | hcs264 | hcs264
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs264) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs264.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs264.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv265 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs264))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (e * b) with hcs266 | hcs266 | hcs266 | hcs266 | hcs266 | hcs266
            · -- $e \diamond b = a$
              have hdv1 : e / b = d := div_eq_iff_mul_eq.mpr hv265
              have hdv2 : e / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs262
              have hik : Idempotent (e / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs266.trans hdv2.symm)) (hbe.symm)
            · -- $e \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs266) (hbe.symm)
            · -- $e \diamond b = c$
              exact absurd (mul_left_cancel (hcs266.trans hv263.symm)) hbd
            · -- $e \diamond b = d$
              have hdv : e / b = d := div_eq_iff_mul_eq.mpr hv265
              have hik : Idempotent (e / b) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hcs266.trans hdv.symm)) (hbe.symm)
            · -- $e \diamond b = e$
              exact absurd (mul_left_cancel (hcs266.trans (hidem e).eq.symm)) hbe
            · -- $e \diamond b = f$
              have hv267 : d * f = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                  ((congrArg (· * b) hv265).trans hcs266))).symm.trans
                  (eq677 d b)).trans hcs262.symm)
              have hdv : a / d = f := div_eq_iff_mul_eq.mpr hv267
              have hik : Idempotent (a / d) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs231
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs264.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv268 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs264))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (b * c) with hcs269 | hcs269 | hcs269 | hcs269 | hcs269 | hcs269
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs269
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs269.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs269) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs269.trans hcs262.symm)) (hac.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs269.trans hv268.symm)) hcf
            · -- $b \diamond c = f$
              rcases hspan (b * d) with hcs270 | hcs270 | hcs270 | hcs270 | hcs270 | hcs270
              · -- $b \diamond d = a$
                have hv271 : d * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs262))).symm.trans
                    (eq677 a b)).trans hcs270.symm)).trans hv261.symm)
                have hv272 : d * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs270).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hcs262.symm)
                have hv273 : b * e = c := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs270.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs262.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv268.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs269.symm)) (hce.symm)
                have hv274 : f * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (d * ·) (congrArg (· * a) hcs1))).symm.trans
                    (eq677 d a)).trans hv261.symm)).trans hv271.symm)
                have hv275 : f * b = a :=
                  (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hv274).trans
                    hv268)).trans hcs231)).symm.trans (eq677 a f)
                have hv276 : b * f = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs269).trans
                    hv275)).trans hcs264)).symm.trans (eq677 c b)
                exact absurd (hv276.symm.trans hv268) hce
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs270.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv277 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs270.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs262.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv268.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs269.symm)) (hce.symm)
                have hv278 : d * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs262))).symm.trans
                    (eq677 a b)).trans hv277.symm)).trans hcs232.symm)
                have hv279 : e * c = f :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hv277).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hv268.symm)
                have e1 : e * d = b * d := hv263.trans hcs270.symm
                have e2 : e * (b * d) = b * (b * d) := by
                  rw [hcs270]
                  exact hv279.trans hcs269.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbe.symm)
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs270.trans hcs262.symm)) (had.symm)
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs270.trans hv268.symm)) hdf
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs270.trans hcs269.symm)) (hcd.symm)
        · -- $b \diamond a = e$
          have hdv : b / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hik : Idempotent (b / a) := hdv ▸ hidem e
          exact absurd (eq_of_mul_eq_div hik (hcs262.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = f$
          have hv280 : e * f = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs262))).symm.trans
              (eq677 e a)).trans hcs232.symm)
          rcases hspan (c * a) with hcs281 | hcs281 | hcs281 | hcs281 | hcs281 | hcs281
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs281) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs281.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs281.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv282 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs281))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (b * c) with hcs283 | hcs283 | hcs283 | hcs283 | hcs283 | hcs283
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs283
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs283.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs283) hbc
            · -- $b \diamond c = d$
              rcases hspan (b * e) with hcs284 | hcs284 | hcs284 | hcs284 | hcs284 | hcs284
              · -- $b \diamond e = a$
                have hv285 : f * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs262))).symm.trans
                    (eq677 a b)).trans hcs284.symm)).trans hcs232.symm)
                have hv286 : e * c = d :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hcs284).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hv282.symm)
                have hv287 : b * f = c := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs284.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs283.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv282.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs262.symm)) (haf.symm)
                have e1 : e * f = b * f := hv280.trans hv287.symm
                have e2 : e * (b * f) = b * (b * f) := by
                  rw [hv287]
                  exact hv286.trans hcs283.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbe.symm)
              · -- $b \diamond e = b$
                exact absurd (mul_left_cancel (hcs284.trans (hidem b).eq.symm)) (hbe.symm)
              · -- $b \diamond e = c$
                have hv288 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs284.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs283.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv282.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs262.symm)) (haf.symm)
                have hv289 : f * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs262))).symm.trans
                    (eq677 a b)).trans hv288.symm)).trans hcs1.symm)
                have hv290 : f * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv288).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hcs262.symm)
                have hv291 : d * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (f * ·) (congrArg (· * a) hv261))).symm.trans
                    (eq677 f a)).trans hcs1.symm)).trans hv289.symm)
                have hv292 : d * b = a :=
                  (congrArg (d * ·) ((congrArg (a * ·) ((congrArg (· * d) hv291).trans
                    hv282)).trans hcs231)).symm.trans (eq677 a d)
                have hv293 : b * d = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs283).trans
                    hv292)).trans hcs281)).symm.trans (eq677 c b)
                exact absurd (hv293.symm.trans hv282) hce
              · -- $b \diamond e = d$
                exact absurd (mul_left_cancel (hcs284.trans hcs283.symm)) (hce.symm)
              · -- $b \diamond e = e$
                exact absurd (mul_left_cancel (hcs284.trans hv282.symm)) (hde.symm)
              · -- $b \diamond e = f$
                exact absurd (mul_left_cancel (hcs284.trans hcs262.symm)) (hae.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs283.trans hv282.symm)) hcd
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs283.trans hcs262.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs231
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs281.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv294 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs281))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (e * b) with hcs295 | hcs295 | hcs295 | hcs295 | hcs295 | hcs295
            · -- $e \diamond b = a$
              have hdv1 : e / b = f := div_eq_iff_mul_eq.mpr hv294
              have hdv2 : e / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs262
              have hik : Idempotent (e / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs295.trans hdv2.symm)) (hbe.symm)
            · -- $e \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs295) (hbe.symm)
            · -- $e \diamond b = c$
              exact absurd (mul_left_cancel (hcs295.trans hv280.symm)) hbf
            · -- $e \diamond b = d$
              have hv296 : f * d = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                  ((congrArg (· * b) hv294).trans hcs295))).symm.trans
                  (eq677 f b)).trans hcs262.symm)
              have hdv : a / f = d := div_eq_iff_mul_eq.mpr hv296
              have hik : Idempotent (a / f) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hv261.trans hdv.symm)) haf
            · -- $e \diamond b = e$
              exact absurd (mul_left_cancel (hcs295.trans (hidem e).eq.symm)) hbe
            · -- $e \diamond b = f$
              have hdv : e / b = f := div_eq_iff_mul_eq.mpr hv294
              have hik : Idempotent (e / b) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs295.trans hdv.symm)) (hbe.symm)
      · -- $a \diamond c = f$
        exact absurd (mul_left_cancel (hcs232.trans hcs1.symm)) hcd
    · -- $a \diamond e = c$
      exact absurd (mul_left_cancel (hcs231.trans hc.symm.symm)) (hbe.symm)
    · -- $a \diamond e = d$
      rcases hspan (a * c) with hcs297 | hcs297 | hcs297 | hcs297 | hcs297 | hcs297
      · -- $a \diamond c = a$
        exact absurd (mul_left_cancel (hcs297.trans (hidem a).eq.symm)) (hac.symm)
      · -- $a \diamond c = b$
        have hv298 : a * f = e := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs297.symm)) (hcf.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs231.symm)) (hef.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
        rcases hspan (d * a) with hcs299 | hcs299 | hcs299 | hcs299 | hcs299 | hcs299
        · -- $d \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs299) (had.symm)
        · -- $d \diamond a = b$
          have hv300 : e * b = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs299))).symm.trans
              (eq677 e a)).trans hv298.symm)
          rcases hspan (e * a) with hcs301 | hcs301 | hcs301 | hcs301 | hcs301 | hcs301
          · -- $e \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs301) (hae.symm)
          · -- $e \diamond a = b$
            have hv302 : f * b = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
                ((congrArg (· * a) hv298).trans hcs301))).symm.trans
                (eq677 f a)).trans hcs1.symm)
            rcases hspan (f * e) with hcs303 | hcs303 | hcs303 | hcs303 | hcs303 | hcs303
            · -- $f \diamond e = a$
              have hdv1 : f / e = b := div_eq_iff_mul_eq.mpr hv300
              have hdv2 : f / e / e = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs301
              have hik : Idempotent (f / e / e) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs303.trans hdv2.symm)) (hef.symm)
            · -- $f \diamond e = b$
              have hdv : f / e = b := div_eq_iff_mul_eq.mpr hv300
              have hik : Idempotent (f / e) := hdv ▸ hidem b
              exact absurd (eq_of_mul_eq_div hik (hcs303.trans hdv.symm)) (hef.symm)
            · -- $f \diamond e = c$
              have hv304 : b * c = a :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (b * ·)
                  ((congrArg (· * e) hv300).trans hcs303))).symm.trans
                  (eq677 b e)).trans hcs301.symm)
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hv304
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $f \diamond e = d$
              exact absurd (mul_left_cancel (hcs303.trans hv302.symm)) (hbe.symm)
            · -- $f \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs303) (hef.symm)
            · -- $f \diamond e = f$
              exact absurd (mul_left_cancel (hcs303.trans (hidem f).eq.symm)) hef
          · -- $e \diamond a = c$
            have hv305 : f * c = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
                ((congrArg (· * a) hv298).trans hcs301))).symm.trans
                (eq677 f a)).trans hcs1.symm)
            rcases hspan (d * f) with hcs306 | hcs306 | hcs306 | hcs306 | hcs306 | hcs306
            · -- $d \diamond f = a$
              have hdv : a / d = f := div_eq_iff_mul_eq.mpr hcs306
              have hik : Idempotent (a / d) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
            · -- $d \diamond f = b$
              exact absurd (mul_left_cancel (hcs306.trans hcs299.symm)) (haf.symm)
            · -- $d \diamond f = c$
              have hdv : d / f = c := div_eq_iff_mul_eq.mpr hv305
              have hik : Idempotent (d / f) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hcs306.trans hdv.symm)) hdf
            · -- $d \diamond f = d$
              exact absurd (mul_left_cancel (hcs306.trans (hidem d).eq.symm)) (hdf.symm)
            · -- $d \diamond f = e$
              have hv307 : f * a = f :=
                mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                  (congrArg (d * ·) (congrArg (· * a) hcs1))).symm.trans
                  (eq677 d a)).trans hcs231.symm)).trans hcs306.symm)
              exact absurd (mul_left_cancel (hv307.trans (hidem f).eq.symm)) haf
            · -- $d \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs306) hdf
          · -- $e \diamond a = d$
            have hdv1 : e / a = f := div_eq_iff_mul_eq.mpr hv298
            have hdv2 : e / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : Idempotent (e / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs301.trans hdv2.symm)) (hae.symm)
          · -- $e \diamond a = e$
            exact absurd (mul_left_cancel (hcs301.trans (hidem e).eq.symm)) hae
          · -- $e \diamond a = f$
            exact absurd (mul_left_cancel (hcs301.trans hv300.symm)) hab
        · -- $d \diamond a = c$
          have hv308 : e * c = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs299))).symm.trans
              (eq677 e a)).trans hv298.symm)
          rcases hspan (e * a) with hcs309 | hcs309 | hcs309 | hcs309 | hcs309 | hcs309
          · -- $e \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs309) (hae.symm)
          · -- $e \diamond a = b$
            have hv310 : f * b = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
                ((congrArg (· * a) hv298).trans hcs309))).symm.trans
                (eq677 f a)).trans hcs1.symm)
            rcases hspan (d * f) with hcs311 | hcs311 | hcs311 | hcs311 | hcs311 | hcs311
            · -- $d \diamond f = a$
              have hdv : a / d = f := div_eq_iff_mul_eq.mpr hcs311
              have hik : Idempotent (a / d) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
            · -- $d \diamond f = b$
              have hdv : d / f = b := div_eq_iff_mul_eq.mpr hv310
              have hik : Idempotent (d / f) := hdv ▸ hidem b
              exact absurd (eq_of_mul_eq_div hik (hcs311.trans hdv.symm)) hdf
            · -- $d \diamond f = c$
              exact absurd (mul_left_cancel (hcs311.trans hcs299.symm)) (haf.symm)
            · -- $d \diamond f = d$
              exact absurd (mul_left_cancel (hcs311.trans (hidem d).eq.symm)) (hdf.symm)
            · -- $d \diamond f = e$
              have hv312 : f * a = f :=
                mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                  (congrArg (d * ·) (congrArg (· * a) hcs1))).symm.trans
                  (eq677 d a)).trans hcs231.symm)).trans hcs311.symm)
              exact absurd (mul_left_cancel (hv312.trans (hidem f).eq.symm)) haf
            · -- $d \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs311) hdf
          · -- $e \diamond a = c$
            have hv313 : f * c = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
                ((congrArg (· * a) hv298).trans hcs309))).symm.trans
                (eq677 f a)).trans hcs1.symm)
            rcases hspan (f * e) with hcs314 | hcs314 | hcs314 | hcs314 | hcs314 | hcs314
            · -- $f \diamond e = a$
              have hdv1 : f / e = c := div_eq_iff_mul_eq.mpr hv308
              have hdv2 : f / e / e = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs309
              have hik : Idempotent (f / e / e) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs314.trans hdv2.symm)) (hef.symm)
            · -- $f \diamond e = b$
              have hv315 : c * b = a :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
                  ((congrArg (· * e) hv308).trans hcs314))).symm.trans
                  (eq677 c e)).trans hcs309.symm)
              have hdv : a / c = b := div_eq_iff_mul_eq.mpr hv315
              have hik : Idempotent (a / c) := hdv ▸ hidem b
              exact absurd (eq_of_mul_eq_div hik (hcs297.trans hdv.symm)) hac
            · -- $f \diamond e = c$
              have hdv : f / e = c := div_eq_iff_mul_eq.mpr hv308
              have hik : Idempotent (f / e) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hcs314.trans hdv.symm)) (hef.symm)
            · -- $f \diamond e = d$
              exact absurd (mul_left_cancel (hcs314.trans hv313.symm)) (hce.symm)
            · -- $f \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs314) (hef.symm)
            · -- $f \diamond e = f$
              exact absurd (mul_left_cancel (hcs314.trans (hidem f).eq.symm)) hef
          · -- $e \diamond a = d$
            have hdv1 : e / a = f := div_eq_iff_mul_eq.mpr hv298
            have hdv2 : e / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : Idempotent (e / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs309.trans hdv2.symm)) (hae.symm)
          · -- $e \diamond a = e$
            exact absurd (mul_left_cancel (hcs309.trans (hidem e).eq.symm)) hae
          · -- $e \diamond a = f$
            exact absurd (mul_left_cancel (hcs309.trans hv308.symm)) hac
        · -- $d \diamond a = d$
          exact absurd (mul_left_cancel (hcs299.trans (hidem d).eq.symm)) had
        · -- $d \diamond a = e$
          have hdv : d / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hik : Idempotent (d / a) := hdv ▸ hidem e
          exact absurd (eq_of_mul_eq_div hik (hcs299.trans hdv.symm)) (had.symm)
        · -- $d \diamond a = f$
          have hdv1 : d / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hdv2 : d / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv298
          have hik : Idempotent (d / a / a) := hdv2 ▸ hidem f
          exact absurd (eq_of_mul_eq_div_div hik (hcs299.trans hdv2.symm)) (had.symm)
      · -- $a \diamond c = c$
        exact absurd (mul_left_cancel (hcs297.trans hc.symm.symm)) (hbc.symm)
      · -- $a \diamond c = d$
        exact absurd (mul_left_cancel (hcs297.trans hcs231.symm)) hce
      · -- $a \diamond c = e$
        have hv316 : a * f = b := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs231.symm)) (hef.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs297.symm)) (hcf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
        rcases hspan (b * a) with hcs317 | hcs317 | hcs317 | hcs317 | hcs317 | hcs317
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs317) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs317.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv318 : f * c = d :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hv316).trans hcs317))).symm.trans
              (eq677 f a)).trans hcs1.symm)
          rcases hspan (c * a) with hcs319 | hcs319 | hcs319 | hcs319 | hcs319 | hcs319
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs319) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs319.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs319.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv320 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs319))).symm.trans
                (eq677 b a)).trans hv316.symm)
            rcases hspan (b * e) with hcs321 | hcs321 | hcs321 | hcs321 | hcs321 | hcs321
            · -- $b \diamond e = a$
              have hv322 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs317))).symm.trans
                  (eq677 a b)).trans hcs321.symm)).trans hcs297.symm)
              exact absurd (mul_left_cancel (hv322.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond e = b$
              exact absurd (mul_left_cancel (hcs321.trans (hidem b).eq.symm)) (hbe.symm)
            · -- $b \diamond e = c$
              exact absurd (mul_left_cancel (hcs321.trans hcs317.symm)) (hae.symm)
            · -- $b \diamond e = d$
              have e1 : b * e = a * e := hcs321.trans hcs231.symm
              have e2 : b * (a * e) = a * (a * e) := by
                rw [hcs231]
                exact hv320.trans hcs1.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
            · -- $b \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs321) hbe
            · -- $b \diamond e = f$
              exact absurd (mul_left_cancel (hcs321.trans hv320.symm)) (hde.symm)
          · -- $c \diamond a = e$
            have hv323 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs319))).symm.trans
                (eq677 b a)).trans hv316.symm)
            rcases hspan (b * d) with hcs324 | hcs324 | hcs324 | hcs324 | hcs324 | hcs324
            · -- $b \diamond d = a$
              have hv325 : c * b = e :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs317))).symm.trans
                  (eq677 a b)).trans hcs324.symm)).trans hcs231.symm)
              exact absurd (mul_left_cancel (hv325.trans hcs319.symm)) (hab.symm)
            · -- $b \diamond d = b$
              exact absurd (mul_left_cancel (hcs324.trans (hidem b).eq.symm)) (hbd.symm)
            · -- $b \diamond d = c$
              exact absurd (mul_left_cancel (hcs324.trans hcs317.symm)) (had.symm)
            · -- $b \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs324) hbd
            · -- $b \diamond d = e$
              rcases hspan (b * c) with hcs326 | hcs326 | hcs326 | hcs326 | hcs326 | hcs326
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs326
                have hik : Idempotent (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs326.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs326.trans hcs317.symm)) (hac.symm)
              · -- $b \diamond c = d$
                have hv327 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs317.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs326.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs324.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv323.symm)) (hef.symm)
                have hv328 : c * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs317))).symm.trans
                    (eq677 a b)).trans hv327.symm)).trans hcs1.symm)
                have hv329 : b * d = f :=
                  (congrArg (b * ·) ((congrArg (f * ·) ((congrArg (· * b) hv327).trans
                    hc.symm)).trans hv318)).symm.trans (eq677 f b)
                exact absurd (hv329.symm.trans hcs324) (hef.symm)
              · -- $b \diamond c = e$
                exact absurd (mul_left_cancel (hcs326.trans hcs324.symm)) hcd
              · -- $b \diamond c = f$
                exact absurd (mul_left_cancel (hcs326.trans hv323.symm)) hce
            · -- $b \diamond d = f$
              exact absurd (mul_left_cancel (hcs324.trans hv323.symm)) hde
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv316
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs319.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = d$
          have hdv1 : b / a = f := div_eq_iff_mul_eq.mpr hv316
          have hdv2 : b / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
          have hik : Idempotent (b / a / a) := hdv2 ▸ hidem d
          exact absurd (eq_of_mul_eq_div_div hik (hcs317.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = e$
          have hv330 : f * e = d :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hv316).trans hcs317))).symm.trans
              (eq677 f a)).trans hcs1.symm)
          rcases hspan (c * a) with hcs331 | hcs331 | hcs331 | hcs331 | hcs331 | hcs331
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs331) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : Idempotent (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs331.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs331.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv332 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs331))).symm.trans
                (eq677 b a)).trans hv316.symm)
            rcases hspan (b * c) with hcs333 | hcs333 | hcs333 | hcs333 | hcs333 | hcs333
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs333
              have hik : Idempotent (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs333.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs333) hbc
            · -- $b \diamond c = d$
              rcases hspan (b * e) with hcs334 | hcs334 | hcs334 | hcs334 | hcs334 | hcs334
              · -- $b \diamond e = a$
                have hv335 : e * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs317))).symm.trans
                    (eq677 a b)).trans hcs334.symm)).trans hcs297.symm)
                have hv336 : e * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hcs334).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hcs317.symm)
                have hv337 : c * d = b :=
                  mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
                    ((congrArg (· * e) hv336).trans hcs231))).symm.trans
                    (eq677 c e)).trans hv335.symm)
                have hdv : b / c = d := div_eq_iff_mul_eq.mpr hv337
                have hik : Idempotent (b / c) := hdv ▸ hidem d
                exact absurd (eq_of_mul_eq_div hik (hcs333.trans hdv.symm)) hbc
              · -- $b \diamond e = b$
                exact absurd (mul_left_cancel (hcs334.trans (hidem b).eq.symm)) (hbe.symm)
              · -- $b \diamond e = c$
                have hv338 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs334.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs333.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs317.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv332.symm)) (hdf.symm)
                have hv339 : e * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs317))).symm.trans
                    (eq677 a b)).trans hv338.symm)).trans hcs1.symm)
                have hv340 : f * c = d :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv338).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hv332.symm)
                exact absurd (mul_left_cancel (hv340.trans hv330.symm)) hce
              · -- $b \diamond e = d$
                exact absurd (mul_left_cancel (hcs334.trans hcs333.symm)) (hce.symm)
              · -- $b \diamond e = e$
                exact absurd (mul_left_cancel (hcs334.trans hcs317.symm)) (hae.symm)
              · -- $b \diamond e = f$
                exact absurd (mul_left_cancel (hcs334.trans hv332.symm)) (hde.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs333.trans hcs317.symm)) (hac.symm)
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs333.trans hv332.symm)) hcd
          · -- $c \diamond a = e$
            have hv341 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs331))).symm.trans
                (eq677 b a)).trans hv316.symm)
            rcases hspan (f * b) with hcs342 | hcs342 | hcs342 | hcs342 | hcs342 | hcs342
            · -- $f \diamond b = a$
              have hdv1 : f / b = e := div_eq_iff_mul_eq.mpr hv341
              have hdv2 : f / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs317
              have hik : Idempotent (f / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs342.trans hdv2.symm)) (hbf.symm)
            · -- $f \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs342) (hbf.symm)
            · -- $f \diamond b = c$
              have hv343 : e * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                  ((congrArg (· * b) hv341).trans hcs342))).symm.trans
                  (eq677 e b)).trans hcs317.symm)
              have hdv : e / c = a := div_eq_iff_mul_eq.mpr hcs331
              have hik : Idempotent (e / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv343.trans hdv.symm)) (hce.symm)
            · -- $f \diamond b = d$
              exact absurd (mul_left_cancel (hcs342.trans hv330.symm)) hbe
            · -- $f \diamond b = e$
              have hdv : f / b = e := div_eq_iff_mul_eq.mpr hv341
              have hik : Idempotent (f / b) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs342.trans hdv.symm)) (hbf.symm)
            · -- $f \diamond b = f$
              exact absurd (mul_left_cancel (hcs342.trans (hidem f).eq.symm)) hbf
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv316
            have hik : Idempotent (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs331.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = f$
          have hdv : b / a = f := div_eq_iff_mul_eq.mpr hv316
          have hik : Idempotent (b / a) := hdv ▸ hidem f
          exact absurd (eq_of_mul_eq_div hik (hcs317.trans hdv.symm)) (hab.symm)
      · -- $a \diamond c = f$
        exact absurd (mul_left_cancel (hcs297.trans hcs1.symm)) hcd
    · -- $a \diamond e = e$
      exact absurd (eq_of_mul_eq_self_right (hidem e) hcs231) hae
    · -- $a \diamond e = f$
      exact absurd (mul_left_cancel (hcs231.trans hcs1.symm)) (hde.symm)

/-- **No magma with six elements satisfies Equation 677.**

Every element of such a magma would be idempotent (`forall_isIdempotentElem_of_card_eq_six`, the
degree analysis), and no six-element magma satisfies Equation 677 together with the idempotent
law (`not_forall_isIdempotentElem_of_card_eq_six`). -/
theorem card_ne_six : Nat.card M ≠ 6 := fun hM =>
  not_forall_isIdempotentElem_of_card_eq_six hM (forall_isIdempotentElem_of_card_eq_six hM)

end Spectrum.E677.OrderSix

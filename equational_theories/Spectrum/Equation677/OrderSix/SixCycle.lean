import equational_theories.Spectrum.Equation677.OrderSix.Degree

namespace Spectrum.E677.OrderSix
universe u
open scoped Spectrum.E677.OrderSix
local infixl:70 " * " => Magma.op
/-! ## Order six -/

section OrderSix

variable {M : Type u} [Magma M] [Fact (Equation677 M)] [Finite M]

/-- **A six-element magma has no element of degree $6$.**

An element $a$ of degree $6$ would have its orbit $a, b, c, d, e, f$ under $L_a$ exhaust the
carrier, with $e = (a \diamond a) \diamond a$ two steps and $f = a / a$ one step before $a$.
Three cells are known at once: the row of $a$ is the six-cycle, $b \diamond a = e$ is the
definition of the cube, and $f \diamond b = e$ is `div_self_mul_sq`. The rest is a case analysis,
split at the top on whether Equation 255 holds at $a$, that is, on the cell $e \diamond a$.

* If $e \diamond a = a$, Equation 677 at the pairs $(d, a)$ and $(c, a)$ forces
  $d \diamond a = c$ and $c \diamond c = b$, and the analysis splits on $b \diamond b$ and
  then on further cells of the row of $b$.
* Otherwise no element is a left unit for $a$, since a left unit would be the cube $e$
  (`eq_cube_of_mul_eq`); the value $a$ is barred from the column of $a$, and the analysis
  splits first on $f \diamond a$ and then on cells of the rows of $d$ and $e$. -/
theorem not_hasDeg_six_of_card_eq_six (hM : Nat.card M = 6) (a : M) : ¬ HasDeg a 6 := by
  intro hdeg
  -- one turn of the orbit, named
  obtain ⟨b, hb⟩ : ∃ b, b = a * a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = a * b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = a * c := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = a * d := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = a * e := ⟨_, rfl⟩
  -- the turn closes up: $L_a(f) = a$
  have haf : a * f = a := by
    rw [hf, he, hd, hc, hb]
    exact hdeg.2.1
  -- the two backward names: $f = a / a$ and $e = (a \diamond a) \diamond a$
  have hFdiv : f = a / a := (div_eq_iff_mul_eq.mpr haf).symm
  have hEcube : e = a * a * a :=
    (div_eq_iff_mul_eq.mpr (hf.symm.trans hFdiv)).symm.trans div_div_eq_mul_mul
  -- the two seeded cells: the cube is $b \diamond a$, and `div_self_mul_sq`
  have hba : b * a = e := by rw [hEcube, hb]
  have hfb : f * b = e := by rw [hFdiv, hb, hEcube]; exact div_self_mul_sq a
  -- distinctness of one turn
  have hNE : ∀ m n : Nat, m < 6 → n < 6 → m ≠ n →
      leftApplyMul a a m ≠ leftApplyMul a a n := fun _ _ hm hn hmn => hdeg.ne hm hn hmn
  have hab : a ≠ b := by rw [hb]; exact hNE 0 1 (by omega) (by omega) (by omega)
  have hac : a ≠ c := by rw [hc, hb]; exact hNE 0 2 (by omega) (by omega) (by omega)
  have had : a ≠ d := by rw [hd, hc, hb]; exact hNE 0 3 (by omega) (by omega) (by omega)
  have hae : a ≠ e := by rw [he, hd, hc, hb]; exact hNE 0 4 (by omega) (by omega) (by omega)
  have haf' : a ≠ f := by
    rw [hf, he, hd, hc, hb]; exact hNE 0 5 (by omega) (by omega) (by omega)
  have hbc : b ≠ c := by rw [hc, hb]; exact hNE 1 2 (by omega) (by omega) (by omega)
  have hbd : b ≠ d := by rw [hd, hc, hb]; exact hNE 1 3 (by omega) (by omega) (by omega)
  have hbe : b ≠ e := by rw [he, hd, hc, hb]; exact hNE 1 4 (by omega) (by omega) (by omega)
  have hbf : b ≠ f := by
    rw [hf, he, hd, hc, hb]; exact hNE 1 5 (by omega) (by omega) (by omega)
  have hcd : c ≠ d := by rw [hd, hc, hb]; exact hNE 2 3 (by omega) (by omega) (by omega)
  have hce : c ≠ e := by rw [he, hd, hc, hb]; exact hNE 2 4 (by omega) (by omega) (by omega)
  have hcf : c ≠ f := by
    rw [hf, he, hd, hc, hb]; exact hNE 2 5 (by omega) (by omega) (by omega)
  have hde : d ≠ e := by rw [he, hd, hc, hb]; exact hNE 3 4 (by omega) (by omega) (by omega)
  have hdf : d ≠ f := by
    rw [hf, he, hd, hc, hb]; exact hNE 3 5 (by omega) (by omega) (by omega)
  have hef : e ≠ f := by
    rw [hf, he, hd, hc, hb]; exact hNE 4 5 (by omega) (by omega) (by omega)
  -- one turn of the orbit is the whole carrier
  have hspan : ∀ z : M, z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f :=
    span_six hM hab hac had hae haf' hbc hbd hbe hbf hcd hce hcf hde hdf hef
  by_cases h255c : e * a = a
  · -- Equation 255 holds at $a$
    have hv1 : d * a = c :=
      mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
        ((congrArg (· * a) he.symm).trans h255c))).symm.trans
        (eq677 d a)).trans hd.symm.symm)
    have hv2 : c * c = b :=
      mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
        ((congrArg (· * a) hd.symm).trans hv1))).symm.trans
        (eq677 c a)).trans hc.symm.symm)
    rcases hspan (b * b) with hcs3 | hcs3 | hcs3 | hcs3 | hcs3 | hcs3
    · -- $b \diamond b = a$
      have e : a * a * (a * a) = a := by rw [hb.symm]; exact hcs3
      exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
    · -- $b \diamond b = b$
      rcases hspan (b * e) with hcs4 | hcs4 | hcs4 | hcs4 | hcs4 | hcs4
      · -- $b \diamond e = a$
        have hv5 : c * a = e :=
          mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
            (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
            (eq677 b a)).trans hb.symm.symm)).trans hcs4.symm)
        have hv6 : e * b = d :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
            (eq677 a b)).trans hcs4.symm)).trans he.symm.symm)
        have hv7 : e * c = a :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
            ((congrArg (· * b) hcs4).trans hc.symm))).symm.trans
            (eq677 e b)).trans hba.symm)
        exact absurd (mul_left_cancel (hv7.trans h255c.symm)) (hac.symm)
      · -- $b \diamond e = b$
        exact absurd (mul_left_cancel (hcs4.trans hcs3.symm)) (hbe.symm)
      · -- $b \diamond e = c$
        have hv8 : c * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (e * ·) (congrArg (· * b) hcs4))).symm.trans
            (eq677 e b)).trans hba.symm)).trans h255c.symm)
        have hv9 : b * d = c :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv8).trans hd.symm))).symm.trans
            (eq677 b c)).trans hv2.symm)
        exact absurd (mul_left_cancel (hv9.trans hcs4.symm)) hde
      · -- $b \diamond e = d$
        have hv10 : d * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (e * ·) (congrArg (· * b) hcs4))).symm.trans
            (eq677 e b)).trans hba.symm)).trans h255c.symm)
        have hv11 : c * d = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
            (congrArg (a * ·) (congrArg (· * d) hv1))).symm.trans
            (eq677 a d)).trans hv10.symm)).trans hb.symm.symm)
        have hv12 : d * d = b :=
          (congrArg (d * ·) ((congrArg (b * ·) ((congrArg (· * d) hv10).trans
            he.symm)).trans hcs4)).symm.trans (eq677 b d)
        have hv13 : c * b = d :=
          (congrArg (c * ·) ((congrArg (d * ·) ((congrArg (· * c) hv11).trans
            hd.symm)).trans hv12)).symm.trans (eq677 d c)
        rcases hspan (b * f) with hcs14 | hcs14 | hcs14 | hcs14 | hcs14 | hcs14
        · -- $b \diamond f = a$
          have hv15 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hcs14.symm)
          have hv16 : e * b = e :=
            mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
              (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
              (eq677 a b)).trans hcs14.symm)).trans hf.symm.symm)
          have hv17 : f * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hv15))).symm.trans
              (eq677 a c)).trans hv11.symm)).trans hd.symm.symm)
          have hv18 : b * c = f := by
            have e := eq_cube_of_mul_eq hv17
            rw [hv2] at e
            exact e.symm
          have hv19 : b * d = c := by
            rcases hspan (b * d) with hz | hz | hz | hz | hz | hz
            · exact absurd (mul_left_cancel (hz.trans hcs14.symm)) hdf
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hbd.symm)
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hcs4.symm)) hde
            · exact absurd (mul_left_cancel (hz.trans hba.symm)) (had.symm)
            · exact absurd (mul_left_cancel (hz.trans hv18.symm)) (hcd.symm)
          have hv20 : c * e = d :=
            mul_left_cancel (((congrArg (b * ·) (congrArg (c * ·)
              ((congrArg (· * b) hv18).trans hfb))).symm.trans
              (eq677 c b)).trans hv19.symm)
          exact absurd (mul_left_cancel (hv20.trans hv13.symm)) (hbe.symm)
        · -- $b \diamond f = b$
          exact absurd (mul_left_cancel (hcs14.trans hcs3.symm)) (hbf.symm)
        · -- $b \diamond f = c$
          have hv21 : d * c = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (b * ·) (congrArg (· * c) hv13))).symm.trans
              (eq677 b c)).trans hv2.symm)).trans hcs14.symm)
          have hv22 : f * d = d :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (c * ·) (congrArg (· * d) hv21))).symm.trans
              (eq677 c d)).trans hv1.symm)).trans hv11.symm)
          have hv23 : b * d = f := by
            have e := eq_cube_of_mul_eq hv22
            rw [hv12] at e
            exact e.symm
          have hv24 : b * c = a := by
            rcases hspan (b * c) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hbc.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs14.symm)) hcf
            · exact absurd (mul_left_cancel (hz.trans hcs4.symm)) hce
            · exact absurd (mul_left_cancel (hz.trans hba.symm)) (hac.symm)
            · exact absurd (mul_left_cancel (hz.trans hv23.symm)) hcd
          have hv25 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv24.symm)
          have hv26 : e * b = b :=
            mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
              (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
              (eq677 a b)).trans hv24.symm)).trans hc.symm.symm)
          exact absurd ((eq_cube_of_mul_eq hcs3).trans (eq_cube_of_mul_eq hv26).symm) hbe
        · -- $b \diamond f = d$
          exact absurd (mul_left_cancel (hcs14.trans hcs4.symm)) (hef.symm)
        · -- $b \diamond f = e$
          exact absurd (mul_left_cancel (hcs14.trans hba.symm)) (haf'.symm)
        · -- $b \diamond f = f$
          have hv27 : f * e = f := by
            have e := mul_mul_eq_self_of_mul_eq hcs14
            rw [hfb] at e
            exact e
          rcases hspan (b * c) with hcs28 | hcs28 | hcs28 | hcs28 | hcs28 | hcs28
          · -- $b \diamond c = a$
            have hv29 : c * a = c :=
              mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
                (eq677 b a)).trans hb.symm.symm)).trans hcs28.symm)
            have hv30 : e * b = b :=
              mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
                (eq677 a b)).trans hcs28.symm)).trans hc.symm.symm)
            exact absurd ((eq_cube_of_mul_eq hcs3).trans (eq_cube_of_mul_eq hv30).symm) hbe
          · -- $b \diamond c = b$
            exact absurd (mul_left_cancel (hcs28.trans hcs3.symm)) (hbc.symm)
          · -- $b \diamond c = c$
            have e : c * c * c = c := by rw [hv2]; exact hcs28
            exact absurd ((isIdempotentElem_of_cube_eq_self e).eq.symm.trans hv2) (hbc.symm)
          · -- $b \diamond c = d$
            exact absurd (mul_left_cancel (hcs28.trans hcs4.symm)) hce
          · -- $b \diamond c = e$
            exact absurd (mul_left_cancel (hcs28.trans hba.symm)) (hac.symm)
          · -- $b \diamond c = f$
            exact absurd (mul_left_cancel (hcs28.trans hcs14.symm)) hcf
      · -- $b \diamond e = e$
        exact absurd (mul_left_cancel (hcs4.trans hba.symm)) (hae.symm)
      · -- $b \diamond e = f$
        have hv31 : e * e = a :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
            ((congrArg (· * b) hcs4).trans hfb))).symm.trans
            (eq677 e b)).trans hba.symm)
        exact absurd (mul_left_cancel (hv31.trans h255c.symm)) (hae.symm)
    · -- $b \diamond b = c$
      have e : b * b * (b * b) = b := by rw [hcs3]; exact hv2
      exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hcs3) hbc
    · -- $b \diamond b = d$
      rcases hspan (b * e) with hcs32 | hcs32 | hcs32 | hcs32 | hcs32 | hcs32
      · -- $b \diamond e = a$
        have hv33 : c * a = e :=
          mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
            (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
            (eq677 b a)).trans hb.symm.symm)).trans hcs32.symm)
        have hv34 : e * b = d :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
            (eq677 a b)).trans hcs32.symm)).trans he.symm.symm)
        have hv35 : e * c = a :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
            ((congrArg (· * b) hcs32).trans hc.symm))).symm.trans
            (eq677 e b)).trans hba.symm)
        exact absurd (mul_left_cancel (hv35.trans h255c.symm)) (hac.symm)
      · -- $b \diamond e = b$
        have hv36 : d * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (b * ·) (congrArg (· * b) hcs3))).symm.trans
            (eq677 b b)).trans hcs32.symm)).trans hba.symm)
        have hv37 : e * d = a :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
            ((congrArg (· * b) hcs32).trans hcs3))).symm.trans
            (eq677 e b)).trans hba.symm)
        exact absurd (mul_left_cancel (hv37.trans h255c.symm)) (had.symm)
      · -- $b \diamond e = c$
        have hv38 : c * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (e * ·) (congrArg (· * b) hcs32))).symm.trans
            (eq677 e b)).trans hba.symm)).trans h255c.symm)
        have hv39 : b * d = c :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv38).trans hd.symm))).symm.trans
            (eq677 b c)).trans hv2.symm)
        exact absurd (mul_left_cancel (hv39.trans hcs32.symm)) hde
      · -- $b \diamond e = d$
        exact absurd (mul_left_cancel (hcs32.trans hcs3.symm)) (hbe.symm)
      · -- $b \diamond e = e$
        exact absurd (mul_left_cancel (hcs32.trans hba.symm)) (hae.symm)
      · -- $b \diamond e = f$
        have hv40 : e * e = a :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
            ((congrArg (· * b) hcs32).trans hfb))).symm.trans
            (eq677 e b)).trans hba.symm)
        exact absurd (mul_left_cancel (hv40.trans h255c.symm)) (hae.symm)
    · -- $b \diamond b = e$
      exact absurd (mul_left_cancel (hcs3.trans hba.symm)) (hab.symm)
    · -- $b \diamond b = f$
      rcases hspan (b * e) with hcs41 | hcs41 | hcs41 | hcs41 | hcs41 | hcs41
      · -- $b \diamond e = a$
        have hv42 : c * a = e :=
          mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
            (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
            (eq677 b a)).trans hb.symm.symm)).trans hcs41.symm)
        have hv43 : e * b = d :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
            (eq677 a b)).trans hcs41.symm)).trans he.symm.symm)
        have hv44 : b * a = b :=
          (congrArg (b * ·) ((congrArg (b * ·) ((congrArg (· * b) hcs3).trans
            hfb)).trans hcs41)).symm.trans (eq677 b b)
        exact absurd (hv44.symm.trans hba) hbe
      · -- $b \diamond e = b$
        have hv45 : b * b = b :=
          (congrArg (b * ·) ((congrArg (b * ·) ((congrArg (· * b) hcs3).trans
            hfb)).trans hcs41)).symm.trans (eq677 b b)
        exact absurd (hv45.symm.trans hcs3) hbf
      · -- $b \diamond e = c$
        have hv46 : b * c = b :=
          (congrArg (b * ·) ((congrArg (b * ·) ((congrArg (· * b) hcs3).trans
            hfb)).trans hcs41)).symm.trans (eq677 b b)
        have hv47 : c * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (e * ·) (congrArg (· * b) hcs41))).symm.trans
            (eq677 e b)).trans hba.symm)).trans h255c.symm)
        have hv48 : c * f = e :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (c * ·)
            ((congrArg (· * b) hv46).trans hcs3))).symm.trans
            (eq677 c b)).trans hcs41.symm)
        have hv49 : b * d = c :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv47).trans hd.symm))).symm.trans
            (eq677 b c)).trans hv2.symm)
        exact absurd (mul_left_cancel (hv49.trans hcs41.symm)) hde
      · -- $b \diamond e = d$
        have hv50 : b * d = b :=
          (congrArg (b * ·) ((congrArg (b * ·) ((congrArg (· * b) hcs3).trans
            hfb)).trans hcs41)).symm.trans (eq677 b b)
        have hv51 : d * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (e * ·) (congrArg (· * b) hcs41))).symm.trans
            (eq677 e b)).trans hba.symm)).trans h255c.symm)
        have hv52 : d * f = e :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
            ((congrArg (· * b) hv50).trans hcs3))).symm.trans
            (eq677 d b)).trans hcs41.symm)
        have hv53 : c * d = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
            (congrArg (a * ·) (congrArg (· * d) hv1))).symm.trans
            (eq677 a d)).trans hv51.symm)).trans hb.symm.symm)
        have hv54 : d * d = b :=
          (congrArg (d * ·) ((congrArg (b * ·) ((congrArg (· * d) hv51).trans
            he.symm)).trans hcs41)).symm.trans (eq677 b d)
        have hv55 : d * a = d :=
          (congrArg (d * ·) ((congrArg (d * ·) ((congrArg (· * d) hv54).trans
            hv50)).trans hv51)).symm.trans (eq677 d d)
        exact absurd (hv55.symm.trans hv1) (hcd.symm)
      · -- $b \diamond e = e$
        exact absurd (mul_left_cancel (hcs41.trans hba.symm)) (hae.symm)
      · -- $b \diamond e = f$
        exact absurd (mul_left_cancel (hcs41.trans hcs3.symm)) (hbe.symm)
  · -- no element is a left unit for $a$
    have hno : ∀ x : M, x * a ≠ a := by
      intro x hx
      have h' := eq_cube_of_mul_eq hx
      rw [← hb, hba] at h'
      exact h255c (h' ▸ hx)
    rcases hspan (f * a) with hcs1 | hcs1 | hcs1 | hcs1 | hcs1 | hcs1
    · -- $f \diamond a = a$
      exact absurd hcs1 (hno _)
    · -- $f \diamond a = b$
      have hv2 : e * b = d :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
          ((congrArg (· * a) hf.symm).trans hcs1))).symm.trans
          (eq677 e a)).trans he.symm.symm)
      have hv3 : b * e = a :=
        (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
          hv2)).trans he.symm)).symm.trans (eq677 a b)
      have hv4 : e * c = a :=
        mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
          ((congrArg (· * b) hv3).trans hc.symm))).symm.trans
          (eq677 e b)).trans hba.symm)
      have hv5 : e * f = e :=
        mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
          (congrArg (b * ·) (congrArg (· * f) hfb))).symm.trans
          (eq677 b f)).trans hcs1.symm)).trans hv3.symm)
      have hv6 : c * a = e :=
        mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
          (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
          (eq677 b a)).trans hb.symm.symm)).trans hv3.symm)
      have hv7 : c * b = a :=
        (congrArg (c * ·) ((congrArg (a * ·) ((congrArg (· * c) hv6).trans
          hv4)).trans hb.symm)).symm.trans (eq677 a c)
      rcases hspan (e * a) with hcs8 | hcs8 | hcs8 | hcs8 | hcs8 | hcs8
      · -- $e \diamond a = a$
        exact absurd (mul_left_cancel (hcs8.trans hv4.symm)) hac
      · -- $e \diamond a = b$
        have hv9 : d * b = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs8))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        have hv10 : e * b = a :=
          (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hcs8).trans
            hv3)).trans hb.symm)).symm.trans (eq677 a e)
        exact absurd (hv10.symm.trans hv2) had
      · -- $e \diamond a = c$
        have hv11 : d * c = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs8))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        have hv12 : c * e = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
            (congrArg (a * ·) (congrArg (· * e) hcs8))).symm.trans
            (eq677 a e)).trans hv4.symm)).trans hc.symm.symm)
        have hv13 : c * f = a :=
          mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
            ((congrArg (· * e) hv4).trans hf.symm))).symm.trans
            (eq677 c e)).trans hcs8.symm)
        exact absurd (mul_left_cancel (hv13.trans hv7.symm)) (hbf.symm)
      · -- $e \diamond a = d$
        exact absurd (mul_left_cancel (hcs8.trans hv2.symm)) hab
      · -- $e \diamond a = e$
        exact absurd (mul_left_cancel (hcs8.trans hv5.symm)) haf'
      · -- $e \diamond a = f$
        have hv14 : d * f = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs8))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        have hv15 : f * e = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
            (congrArg (a * ·) (congrArg (· * e) hcs8))).symm.trans
            (eq677 a e)).trans hv4.symm)).trans hc.symm.symm)
        exact absurd (mul_left_cancel (hv15.trans hcs1.symm)) (hae.symm)
    · -- $f \diamond a = c$
      have hv16 : e * c = d :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
          ((congrArg (· * a) hf.symm).trans hcs1))).symm.trans
          (eq677 e a)).trans he.symm.symm)
      rcases hspan (e * a) with hcs17 | hcs17 | hcs17 | hcs17 | hcs17 | hcs17
      · -- $e \diamond a = a$
        exact absurd hcs17 (hno _)
      · -- $e \diamond a = b$
        have hv18 : d * b = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs17))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs19 | hcs19 | hcs19 | hcs19 | hcs19 | hcs19
        · -- $e \diamond b = a$
          have hv20 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs19)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv20
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          exact absurd (mul_left_cancel (hcs19.trans hcs17.symm)) (hab.symm)
        · -- $e \diamond b = c$
          have e1 : e * a = a * a := hcs17.trans hb.symm.symm
          have e2 : e * (a * a) = a * (a * a) := by
            rw [hb.symm]
            exact hcs19.trans hc.symm.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs19.trans hv16.symm)) hbc
        · -- $e \diamond b = e$
          have hv21 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs19)).trans hf.symm)).symm.trans (eq677 a b)
          have hv22 : e * e = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (b * ·) (congrArg (· * e) hcs19))).symm.trans
              (eq677 b e)).trans hcs17.symm)).trans hv21.symm)
          have hv23 : f * e = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (e * ·) (congrArg (· * e) hv22))).symm.trans
              (eq677 e e)).trans hcs19.symm)).trans hcs17.symm)
          have hv24 : c * f = d :=
            mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
              (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
              (eq677 a f)).trans hv23.symm)).trans he.symm.symm)
          have hv25 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv21.symm)
          have hv26 : d * c = e :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (f * ·) (congrArg (· * c) hv24))).symm.trans
              (eq677 f c)).trans hv25.symm)).trans hv23.symm)
          rcases hspan (e * f) with hcs27 | hcs27 | hcs27 | hcs27 | hcs27 | hcs27
          · -- $e \diamond f = a$
            have e1 : e * e = a * e := hv22.trans hf.symm.symm
            have e2 : e * (a * e) = a * (a * e) := by
              rw [hf.symm]
              exact hcs27.trans haf.symm
            exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
          · -- $e \diamond f = b$
            exact absurd (mul_left_cancel (hcs27.trans hcs17.symm)) (haf'.symm)
          · -- $e \diamond f = c$
            have hv28 : c * e = b :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (f * ·) (congrArg (· * e) hcs27))).symm.trans
                (eq677 f e)).trans hv22.symm)).trans hfb.symm)
            have hv29 : d * e = a :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (c * ·) (congrArg (· * e) hv16))).symm.trans
                (eq677 c e)).trans hcs27.symm)).trans hv25.symm)
            have hv30 : d * f = e :=
              (congrArg (d * ·) ((congrArg (e * ·) ((congrArg (· * d) hv29).trans
                he.symm)).trans hv22)).symm.trans (eq677 e d)
            exact absurd (mul_left_cancel (hv30.trans hv26.symm)) (hcf.symm)
          · -- $e \diamond f = d$
            exact absurd (mul_left_cancel (hcs27.trans hv16.symm)) (hcf.symm)
          · -- $e \diamond f = e$
            exact absurd (mul_left_cancel (hcs27.trans hcs19.symm)) (hbf.symm)
          · -- $e \diamond f = f$
            exact absurd (mul_left_cancel (hcs27.trans hv22.symm)) (hef.symm)
        · -- $e \diamond b = f$
          have hv31 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs19)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv31.symm.trans hba) hae
      · -- $e \diamond a = c$
        have hv32 : d * c = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs17))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs33 | hcs33 | hcs33 | hcs33 | hcs33 | hcs33
        · -- $e \diamond b = a$
          have hv34 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs33)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv34
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv35 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs33)).trans hc.symm)).symm.trans (eq677 a b)
          have hv36 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv35.symm)
          have hv37 : c * d = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (c * ·) (congrArg (· * d) hv32))).symm.trans
              (eq677 c d)).trans hv32.symm)).trans hv36.symm)
          have hv38 : d * e = d :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (c * ·) (congrArg (· * e) hv16))).symm.trans
              (eq677 c e)).trans hcs17.symm)).trans hv37.symm)
          have hv39 : c * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hv36))).symm.trans
              (eq677 a c)).trans hv37.symm)).trans hd.symm.symm)
          exact absurd (mul_left_cancel (hv39.trans hv36.symm)) (hac.symm)
        · -- $e \diamond b = c$
          exact absurd (mul_left_cancel (hcs33.trans hcs17.symm)) (hab.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs33.trans hv16.symm)) hbc
        · -- $e \diamond b = e$
          have hv40 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs33)).trans hf.symm)).symm.trans (eq677 a b)
          have hv41 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv40.symm)
          rcases hspan (e * e) with hcs42 | hcs42 | hcs42 | hcs42 | hcs42 | hcs42
          · -- $e \diamond e = a$
            have hv43 : c * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                (eq677 a e)).trans hcs42.symm)).trans he.symm.symm)
            have hv44 : e * e = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs33).trans
                hcs42)).trans hba)).symm.trans (eq677 b e)
            exact absurd (hv44.symm.trans hcs42) (hab.symm)
          · -- $e \diamond e = b$
            have e : e * (e * e) = e := by rw [hcs42]; exact hcs33
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs42) (hbe.symm)
          · -- $e \diamond e = c$
            exact absurd (mul_left_cancel (hcs42.trans hcs17.symm)) (hae.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs42.trans hv16.symm)) (hce.symm)
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs42.trans hcs33.symm)) (hbe.symm)
          · -- $e \diamond e = f$
            have hv45 : e * a = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs33).trans
                hcs42)).trans hv40)).symm.trans (eq677 b e)
            exact absurd (hv45.symm.trans hcs17) hbc
        · -- $e \diamond b = f$
          have hv46 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs33)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv46.symm.trans hba) hae
      · -- $e \diamond a = d$
        exact absurd (mul_left_cancel (hcs17.trans hv16.symm)) hac
      · -- $e \diamond a = e$
        have hv47 : d * e = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs17))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs48 | hcs48 | hcs48 | hcs48 | hcs48 | hcs48
        · -- $e \diamond b = a$
          have hv49 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs48)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv49
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv50 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs48)).trans hc.symm)).symm.trans (eq677 a b)
          have hv51 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv50.symm)
          rcases hspan (e * e) with hcs52 | hcs52 | hcs52 | hcs52 | hcs52 | hcs52
          · -- $e \diamond e = a$
            have e : e * (e * e) = e := by rw [hcs52]; exact hcs17
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs52) (hae.symm)
          · -- $e \diamond e = b$
            exact absurd (mul_left_cancel (hcs52.trans hcs48.symm)) (hbe.symm)
          · -- $e \diamond e = c$
            have hv53 : e * d = a :=
              (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hcs17).trans
                hcs52)).trans hd.symm)).symm.trans (eq677 a e)
            have hv54 : c * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (e * ·) (congrArg (· * e) hcs52))).symm.trans
                (eq677 e e)).trans hcs17.symm)).trans hv53.symm)
            have hv55 : c * c = e :=
              mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
                ((congrArg (· * e) hv16).trans hv47))).symm.trans
                (eq677 c e)).trans hcs52.symm)
            have e : e * e * (e * e) = e := by rw [hcs52]; exact hv55
            exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hcs52) (hce.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs52.trans hv16.symm)) (hce.symm)
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs52.trans hcs17.symm)) (hae.symm)
          · -- $e \diamond e = f$
            have hv56 : e * a = a :=
              (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hcs17).trans
                hcs52)).trans haf)).symm.trans (eq677 a e)
            exact absurd (hv56.symm.trans hcs17) hae
        · -- $e \diamond b = c$
          have e1 : e * b = a * b := hcs48.trans hc.symm.symm
          have e2 : e * (a * b) = a * (a * b) := by
            rw [hc.symm]
            exact hv16.trans hd.symm.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs48.trans hv16.symm)) hbc
        · -- $e \diamond b = e$
          exact absurd (mul_left_cancel (hcs48.trans hcs17.symm)) (hab.symm)
        · -- $e \diamond b = f$
          have hv57 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs48)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv57.symm.trans hba) hae
      · -- $e \diamond a = f$
        have hv58 : d * f = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs17))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs59 | hcs59 | hcs59 | hcs59 | hcs59 | hcs59
        · -- $e \diamond b = a$
          have hv60 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs59)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv60
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv61 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs59)).trans hc.symm)).symm.trans (eq677 a b)
          have hv62 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv61.symm)
          rcases hspan (e * e) with hcs63 | hcs63 | hcs63 | hcs63 | hcs63 | hcs63
          · -- $e \diamond e = a$
            have hv64 : f * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                (eq677 a e)).trans hcs63.symm)).trans he.symm.symm)
            have hv65 : f * d = e :=
              (congrArg (f * ·) ((congrArg (e * ·) ((congrArg (· * f) hv64).trans
                hv58)).trans hv16)).symm.trans (eq677 e f)
            exact absurd (mul_left_cancel (hv65.trans hfb.symm)) (hbd.symm)
          · -- $e \diamond e = b$
            exact absurd (mul_left_cancel (hcs63.trans hcs59.symm)) (hbe.symm)
          · -- $e \diamond e = c$
            rcases hspan (e * f) with hcs66 | hcs66 | hcs66 | hcs66 | hcs66 | hcs66
            · -- $e \diamond f = a$
              have hv67 : f * e = e :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                  (eq677 a e)).trans hcs66.symm)).trans hf.symm.symm)
              exact absurd (mul_left_cancel (hv67.trans hfb.symm)) (hbe.symm)
            · -- $e \diamond f = b$
              exact absurd (mul_left_cancel (hcs66.trans hcs59.symm)) (hbf.symm)
            · -- $e \diamond f = c$
              exact absurd (mul_left_cancel (hcs66.trans hcs63.symm)) (hef.symm)
            · -- $e \diamond f = d$
              exact absurd (mul_left_cancel (hcs66.trans hv16.symm)) (hcf.symm)
            · -- $e \diamond f = e$
              have hv68 : c * e = a :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (e * ·) (congrArg (· * e) hcs63))).symm.trans
                  (eq677 e e)).trans hcs66.symm)).trans hcs17.symm)
              have hv69 : f * c = a :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (f * ·)
                  ((congrArg (· * e) hcs66).trans hcs63))).symm.trans
                  (eq677 f e)).trans hcs17.symm)
              have hv70 : c * f = b :=
                mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
                  (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
                  (eq677 a f)).trans hv69.symm)).trans hc.symm.symm)
              have hv71 : f * c = c :=
                (congrArg (f * ·) ((congrArg (c * ·) ((congrArg (· * f) hv69).trans
                  haf)).trans hv62)).symm.trans (eq677 c f)
              exact absurd (hv71.symm.trans hv69) (hac.symm)
            · -- $e \diamond f = f$
              exact absurd (mul_left_cancel (hcs66.trans hcs17.symm)) (haf'.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs63.trans hv16.symm)) (hce.symm)
          · -- $e \diamond e = e$
            rcases hspan (e * f) with hcs72 | hcs72 | hcs72 | hcs72 | hcs72 | hcs72
            · -- $e \diamond f = a$
              have hv73 : f * e = e :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                  (eq677 a e)).trans hcs72.symm)).trans hf.symm.symm)
              exact absurd (mul_left_cancel (hv73.trans hfb.symm)) (hbe.symm)
            · -- $e \diamond f = b$
              exact absurd (mul_left_cancel (hcs72.trans hcs59.symm)) (hbf.symm)
            · -- $e \diamond f = c$
              have hv74 : f * a = b :=
                (congrArg (f * ·) ((congrArg (b * ·) ((congrArg (· * f) hfb).trans
                  hcs72)).trans hv61)).symm.trans (eq677 b f)
              exact absurd (hv74.symm.trans hcs1) hbc
            · -- $e \diamond f = d$
              exact absurd (mul_left_cancel (hcs72.trans hv16.symm)) (hcf.symm)
            · -- $e \diamond f = e$
              exact absurd (mul_left_cancel (hcs72.trans hcs63.symm)) (hef.symm)
            · -- $e \diamond f = f$
              exact absurd (mul_left_cancel (hcs72.trans hcs17.symm)) (haf'.symm)
          · -- $e \diamond e = f$
            exact absurd (mul_left_cancel (hcs63.trans hcs17.symm)) (hae.symm)
        · -- $e \diamond b = c$
          have e1 : e * b = a * b := hcs59.trans hc.symm.symm
          have e2 : e * (a * b) = a * (a * b) := by
            rw [hc.symm]
            exact hv16.trans hd.symm.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs59.trans hv16.symm)) hbc
        · -- $e \diamond b = e$
          have hv75 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs59)).trans hf.symm)).symm.trans (eq677 a b)
          have hv76 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv75.symm)
          rcases hspan (e * e) with hcs77 | hcs77 | hcs77 | hcs77 | hcs77 | hcs77
          · -- $e \diamond e = a$
            have hv78 : f * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                (eq677 a e)).trans hcs77.symm)).trans he.symm.symm)
            have hv79 : e * e = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs59).trans
                hcs77)).trans hba)).symm.trans (eq677 b e)
            exact absurd (hv79.symm.trans hcs77) (hab.symm)
          · -- $e \diamond e = b$
            have e : e * (e * e) = e := by rw [hcs77]; exact hcs59
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs77) (hbe.symm)
          · -- $e \diamond e = c$
            rcases hspan (e * f) with hcs80 | hcs80 | hcs80 | hcs80 | hcs80 | hcs80
            · -- $e \diamond f = a$
              have hv81 : f * e = e :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                  (eq677 a e)).trans hcs80.symm)).trans hf.symm.symm)
              exact absurd (mul_left_cancel (hv81.trans hfb.symm)) (hbe.symm)
            · -- $e \diamond f = b$
              have hv82 : b * c = f :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (b * ·)
                  ((congrArg (· * e) hcs59).trans hcs77))).symm.trans
                  (eq677 b e)).trans hcs80.symm)
              have hv83 : c * e = f :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (e * ·) (congrArg (· * e) hcs77))).symm.trans
                  (eq677 e e)).trans hcs59.symm)).trans hcs80.symm)
              exact absurd (mul_left_cancel (hv83.trans hv76.symm)) (hae.symm)
            · -- $e \diamond f = c$
              exact absurd (mul_left_cancel (hcs80.trans hcs77.symm)) (hef.symm)
            · -- $e \diamond f = d$
              exact absurd (mul_left_cancel (hcs80.trans hv16.symm)) (hcf.symm)
            · -- $e \diamond f = e$
              exact absurd (mul_left_cancel (hcs80.trans hcs59.symm)) (hbf.symm)
            · -- $e \diamond f = f$
              exact absurd (mul_left_cancel (hcs80.trans hcs17.symm)) (haf'.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs77.trans hv16.symm)) (hce.symm)
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs77.trans hcs59.symm)) (hbe.symm)
          · -- $e \diamond e = f$
            exact absurd (mul_left_cancel (hcs77.trans hcs17.symm)) (hae.symm)
        · -- $e \diamond b = f$
          exact absurd (mul_left_cancel (hcs59.trans hcs17.symm)) (hab.symm)
    · -- $f \diamond a = d$
      have hv84 : e * d = d :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
          ((congrArg (· * a) hf.symm).trans hcs1))).symm.trans
          (eq677 e a)).trans he.symm.symm)
      rcases hspan (e * a) with hcs85 | hcs85 | hcs85 | hcs85 | hcs85 | hcs85
      · -- $e \diamond a = a$
        exact absurd hcs85 (hno _)
      · -- $e \diamond a = b$
        have hv86 : d * b = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs85))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs87 | hcs87 | hcs87 | hcs87 | hcs87 | hcs87
        · -- $e \diamond b = a$
          have hv88 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs87)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv88
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          exact absurd (mul_left_cancel (hcs87.trans hcs85.symm)) (hab.symm)
        · -- $e \diamond b = c$
          have e1 : e * a = a * a := hcs85.trans hb.symm.symm
          have e2 : e * (a * a) = a * (a * a) := by
            rw [hb.symm]
            exact hcs87.trans hc.symm.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs87.trans hv84.symm)) hbd
        · -- $e \diamond b = e$
          have hv89 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs87)).trans hf.symm)).symm.trans (eq677 a b)
          have hv90 : e * e = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (b * ·) (congrArg (· * e) hcs87))).symm.trans
              (eq677 b e)).trans hcs85.symm)).trans hv89.symm)
          have hv91 : f * e = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (e * ·) (congrArg (· * e) hv90))).symm.trans
              (eq677 e e)).trans hcs87.symm)).trans hcs85.symm)
          have hv92 : d * f = d :=
            mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
              (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
              (eq677 a f)).trans hv91.symm)).trans he.symm.symm)
          have hv93 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv89.symm)
          have hv94 : d * e = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (d * ·) (congrArg (· * e) hv84))).symm.trans
              (eq677 d e)).trans hv84.symm)).trans hv92.symm)
          have hv95 : d * d = b :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (f * ·) (congrArg (· * d) hv92))).symm.trans
              (eq677 f d)).trans hv94.symm)).trans hfb.symm)
          have hv96 : b * d = e := by
            have e := eq_cube_of_mul_eq hv84
            rw [hv95] at e
            exact e.symm
          exact absurd (mul_left_cancel (hv96.trans hba.symm)) (had.symm)
        · -- $e \diamond b = f$
          have hv97 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs87)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv97.symm.trans hba) hae
      · -- $e \diamond a = c$
        have hv98 : d * c = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs85))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs99 | hcs99 | hcs99 | hcs99 | hcs99 | hcs99
        · -- $e \diamond b = a$
          have hv100 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs99)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv100
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv101 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs99)).trans hc.symm)).symm.trans (eq677 a b)
          have hv102 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv101.symm)
          have hv103 : c * d = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (c * ·) (congrArg (· * d) hv98))).symm.trans
              (eq677 c d)).trans hv98.symm)).trans hv102.symm)
          have hv104 : c * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hv102))).symm.trans
              (eq677 a c)).trans hv103.symm)).trans hd.symm.symm)
          exact absurd (mul_left_cancel (hv104.trans hv102.symm)) (hac.symm)
        · -- $e \diamond b = c$
          exact absurd (mul_left_cancel (hcs99.trans hcs85.symm)) (hab.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs99.trans hv84.symm)) hbd
        · -- $e \diamond b = e$
          have hv105 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs99)).trans hf.symm)).symm.trans (eq677 a b)
          have hv106 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv105.symm)
          rcases hspan (e * e) with hcs107 | hcs107 | hcs107 | hcs107 | hcs107 | hcs107
          · -- $e \diamond e = a$
            have hv108 : c * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs85))).symm.trans
                (eq677 a e)).trans hcs107.symm)).trans he.symm.symm)
            have hv109 : e * e = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs99).trans
                hcs107)).trans hba)).symm.trans (eq677 b e)
            exact absurd (hv109.symm.trans hcs107) (hab.symm)
          · -- $e \diamond e = b$
            have e : e * (e * e) = e := by rw [hcs107]; exact hcs99
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs107) (hbe.symm)
          · -- $e \diamond e = c$
            exact absurd (mul_left_cancel (hcs107.trans hcs85.symm)) (hae.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs107.trans hv84.symm)) (hde.symm)
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs107.trans hcs99.symm)) (hbe.symm)
          · -- $e \diamond e = f$
            have hv110 : e * a = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs99).trans
                hcs107)).trans hv105)).symm.trans (eq677 b e)
            exact absurd (hv110.symm.trans hcs85) hbc
        · -- $e \diamond b = f$
          have hv111 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs99)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv111.symm.trans hba) hae
      · -- $e \diamond a = d$
        exact absurd (mul_left_cancel (hcs85.trans hv84.symm)) had
      · -- $e \diamond a = e$
        have hv112 : d * e = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs85))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        have hv113 : d * c = d := by
          have e := mul_mul_eq_self_of_mul_eq hv84
          rw [hv112] at e
          exact e
        rcases hspan (d * a) with hcs114 | hcs114 | hcs114 | hcs114 | hcs114 | hcs114
        · -- $d \diamond a = a$
          exact absurd hcs114 (hno _)
        · -- $d \diamond a = b$
          have hv115 : c * b = b :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
              ((congrArg (· * a) hd.symm).trans hcs114))).symm.trans
              (eq677 c a)).trans hc.symm.symm)
          rcases hspan (d * b) with hcs116 | hcs116 | hcs116 | hcs116 | hcs116 | hcs116
          · -- $d \diamond b = a$
            have hv117 : b * d = a :=
              mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                (congrArg (a * ·) (congrArg (· * d) hcs114))).symm.trans
                (eq677 a d)).trans hcs116.symm)).trans hb.symm.symm)
            have hv118 : b * e = a :=
              mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
                ((congrArg (· * d) hcs116).trans he.symm))).symm.trans
                (eq677 b d)).trans hcs114.symm)
            exact absurd (mul_left_cancel (hv118.trans hv117.symm)) (hde.symm)
          · -- $d \diamond b = b$
            exact absurd (mul_left_cancel (hcs116.trans hcs114.symm)) (hab.symm)
          · -- $d \diamond b = c$
            exact absurd (mul_left_cancel (hcs116.trans hv112.symm)) hbe
          · -- $d \diamond b = d$
            exact absurd (mul_left_cancel (hcs116.trans hv113.symm)) hbc
          · -- $d \diamond b = e$
            have hv119 : b * d = a :=
              mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
                ((congrArg (· * d) hcs116).trans hv84))).symm.trans
                (eq677 b d)).trans hcs114.symm)
            have hv120 : c * a = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
                (eq677 b a)).trans hb.symm.symm)).trans hv119.symm)
            have hv121 : e * b = c :=
              mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
                (eq677 a b)).trans hv119.symm)).trans hd.symm.symm)
            have hv122 : b * d = d :=
              (congrArg (b * ·) ((congrArg (d * ·) ((congrArg (· * b) hv119).trans
                hc.symm)).trans hv113)).symm.trans (eq677 d b)
            exact absurd (hv122.symm.trans hv119) (had.symm)
          · -- $d \diamond b = f$
            rcases hspan (d * f) with hcs123 | hcs123 | hcs123 | hcs123 | hcs123 | hcs123
            · -- $d \diamond f = a$
              have e1 : d * f = a * f := hcs123.trans haf.symm
              have e2 : d * (a * f) = a * (a * f) := by
                rw [haf]
                exact hcs114.trans hb.symm.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (had.symm)
            · -- $d \diamond f = b$
              exact absurd (mul_left_cancel (hcs123.trans hcs114.symm)) (haf'.symm)
            · -- $d \diamond f = c$
              exact absurd (mul_left_cancel (hcs123.trans hv112.symm)) (hef.symm)
            · -- $d \diamond f = d$
              exact absurd (mul_left_cancel (hcs123.trans hv113.symm)) (hcf.symm)
            · -- $d \diamond f = e$
              have hv124 : f * f = a :=
                (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
                  hcs123)).trans hf.symm)).symm.trans (eq677 a f)
              have hv125 : f * d = f :=
                (congrArg (f * ·) ((congrArg (f * ·) ((congrArg (· * f) hv124).trans
                  haf)).trans hcs1)).symm.trans (eq677 f f)
              have e : f * (f * (f * f)) = f := by rw [hv124, hcs1]; exact hv125
              exact absurd ((isIdempotentElem_of_mul_mul_sq e).eq.symm.trans hv124) (haf'.symm)
            · -- $d \diamond f = f$
              exact absurd (mul_left_cancel (hcs123.trans hcs116.symm)) (hbf.symm)
        · -- $d \diamond a = c$
          exact absurd (mul_left_cancel (hcs114.trans hv112.symm)) hae
        · -- $d \diamond a = d$
          exact absurd (mul_left_cancel (hcs114.trans hv113.symm)) hac
        · -- $d \diamond a = e$
          have hv126 : c * e = b :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
              ((congrArg (· * a) hd.symm).trans hcs114))).symm.trans
              (eq677 c a)).trans hc.symm.symm)
          have hv127 : d * e = a :=
            (congrArg (d * ·) ((congrArg (a * ·) ((congrArg (· * d) hcs114).trans
              hv84)).trans he.symm)).symm.trans (eq677 a d)
          exact absurd (hv127.symm.trans hv112) hac
        · -- $d \diamond a = f$
          have hv128 : c * f = b :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
              ((congrArg (· * a) hd.symm).trans hcs114))).symm.trans
              (eq677 c a)).trans hc.symm.symm)
          rcases hspan (d * b) with hcs129 | hcs129 | hcs129 | hcs129 | hcs129 | hcs129
          · -- $d \diamond b = a$
            have hv130 : f * d = a :=
              mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                (congrArg (a * ·) (congrArg (· * d) hcs114))).symm.trans
                (eq677 a d)).trans hcs129.symm)).trans hb.symm.symm)
            have hv131 : d * f = c :=
              mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
                (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
                (eq677 a f)).trans hv130.symm)).trans hd.symm.symm)
            exact absurd (mul_left_cancel (hv131.trans hv112.symm)) (hef.symm)
          · -- $d \diamond b = b$
            rcases hspan (d * f) with hcs132 | hcs132 | hcs132 | hcs132 | hcs132 | hcs132
            · -- $d \diamond f = a$
              have hv133 : f * b = a :=
                (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
                  hcs132)).trans hb.symm)).symm.trans (eq677 a f)
              exact absurd (hv133.symm.trans hfb) hae
            · -- $d \diamond f = b$
              exact absurd (mul_left_cancel (hcs132.trans hcs129.symm)) (hbf.symm)
            · -- $d \diamond f = c$
              exact absurd (mul_left_cancel (hcs132.trans hv112.symm)) (hef.symm)
            · -- $d \diamond f = d$
              exact absurd (mul_left_cancel (hcs132.trans hv113.symm)) (hcf.symm)
            · -- $d \diamond f = e$
              have hv134 : f * f = a :=
                (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
                  hcs132)).trans hf.symm)).symm.trans (eq677 a f)
              have hv135 : f * d = f :=
                (congrArg (f * ·) ((congrArg (f * ·) ((congrArg (· * f) hv134).trans
                  haf)).trans hcs1)).symm.trans (eq677 f f)
              have e : f * (f * (f * f)) = f := by rw [hv134, hcs1]; exact hv135
              exact absurd ((isIdempotentElem_of_mul_mul_sq e).eq.symm.trans hv134) (haf'.symm)
            · -- $d \diamond f = f$
              exact absurd (mul_left_cancel (hcs132.trans hcs114.symm)) (haf'.symm)
          · -- $d \diamond b = c$
            exact absurd (mul_left_cancel (hcs129.trans hv112.symm)) hbe
          · -- $d \diamond b = d$
            exact absurd (mul_left_cancel (hcs129.trans hv113.symm)) hbc
          · -- $d \diamond b = e$
            rcases hspan (d * f) with hcs136 | hcs136 | hcs136 | hcs136 | hcs136 | hcs136
            · -- $d \diamond f = a$
              have hv137 : f * b = a :=
                (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
                  hcs136)).trans hb.symm)).symm.trans (eq677 a f)
              exact absurd (hv137.symm.trans hfb) hae
            · -- $d \diamond f = b$
              have hv138 : f * c = a :=
                (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
                  hcs136)).trans hc.symm)).symm.trans (eq677 a f)
              have hv139 : b * d = f :=
                mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
                  ((congrArg (· * d) hcs129).trans hv84))).symm.trans
                  (eq677 b d)).trans hcs136.symm)
              have hv140 : f * f = a :=
                mul_left_cancel (((congrArg (d * ·) (congrArg (f * ·)
                  ((congrArg (· * d) hcs136).trans hv139))).symm.trans
                  (eq677 f d)).trans hcs114.symm)
              exact absurd (mul_left_cancel (hv140.trans hv138.symm)) (hcf.symm)
            · -- $d \diamond f = c$
              exact absurd (mul_left_cancel (hcs136.trans hv112.symm)) (hef.symm)
            · -- $d \diamond f = d$
              exact absurd (mul_left_cancel (hcs136.trans hv113.symm)) (hcf.symm)
            · -- $d \diamond f = e$
              exact absurd (mul_left_cancel (hcs136.trans hcs129.symm)) (hbf.symm)
            · -- $d \diamond f = f$
              exact absurd (mul_left_cancel (hcs136.trans hcs114.symm)) (haf'.symm)
          · -- $d \diamond b = f$
            exact absurd (mul_left_cancel (hcs129.trans hcs114.symm)) (hab.symm)
      · -- $e \diamond a = f$
        have hv141 : d * f = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs85))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        have hv142 : f * d = a :=
          (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
            hv141)).trans hd.symm)).symm.trans (eq677 a f)
        have hv143 : d * a = a :=
          mul_left_cancel (((congrArg (f * ·) (congrArg (d * ·)
            ((congrArg (· * f) hv142).trans haf))).symm.trans
            (eq677 d f)).trans hcs1.symm)
        exact absurd hv143 (hno _)
    · -- $f \diamond a = e$
      exact absurd (mul_left_cancel (hcs1.trans hfb.symm)) hab
    · -- $f \diamond a = f$
      have hv144 : e * f = d :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
          ((congrArg (· * a) hf.symm).trans hcs1))).symm.trans
          (eq677 e a)).trans he.symm.symm)
      rcases hspan (e * a) with hcs145 | hcs145 | hcs145 | hcs145 | hcs145 | hcs145
      · -- $e \diamond a = a$
        exact absurd hcs145 (hno _)
      · -- $e \diamond a = b$
        have hv146 : d * b = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs145))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs147 | hcs147 | hcs147 | hcs147 | hcs147 | hcs147
        · -- $e \diamond b = a$
          have hv148 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs147)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv148
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          exact absurd (mul_left_cancel (hcs147.trans hcs145.symm)) (hab.symm)
        · -- $e \diamond b = c$
          have e1 : e * a = a * a := hcs145.trans hb.symm.symm
          have e2 : e * (a * a) = a * (a * a) := by
            rw [hb.symm]
            exact hcs147.trans hc.symm.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs147.trans hv144.symm)) hbf
        · -- $e \diamond b = e$
          have hv149 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs147)).trans hf.symm)).symm.trans (eq677 a b)
          have hv150 : e * e = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (b * ·) (congrArg (· * e) hcs147))).symm.trans
              (eq677 b e)).trans hcs145.symm)).trans hv149.symm)
          have hv151 : f * e = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (e * ·) (congrArg (· * e) hv150))).symm.trans
              (eq677 e e)).trans hcs147.symm)).trans hcs145.symm)
          have hv152 : d * e = b :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (f * ·) (congrArg (· * e) hv144))).symm.trans
              (eq677 f e)).trans hv150.symm)).trans hfb.symm)
          have hv153 : f * f = d :=
            mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
              (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
              (eq677 a f)).trans hv151.symm)).trans he.symm.symm)
          have hv154 : d * f = e :=
            mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
              (congrArg (f * ·) (congrArg (· * f) hv153))).symm.trans
              (eq677 f f)).trans hcs1.symm)).trans hv151.symm)
          have hv155 : c * d = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (b * ·) (congrArg (· * d) hv146))).symm.trans
              (eq677 b d)).trans hv152.symm)).trans hba.symm)
          have hv156 : b * d = e :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (e * ·) (congrArg (· * d) hv152))).symm.trans
              (eq677 e d)).trans hv154.symm)).trans hv150.symm)
          exact absurd (mul_left_cancel (hv156.trans hba.symm)) (had.symm)
        · -- $e \diamond b = f$
          have hv157 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs147)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv157.symm.trans hba) hae
      · -- $e \diamond a = c$
        have hv158 : d * c = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs145))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs159 | hcs159 | hcs159 | hcs159 | hcs159 | hcs159
        · -- $e \diamond b = a$
          have hv160 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs159)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv160
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv161 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs159)).trans hc.symm)).symm.trans (eq677 a b)
          have hv162 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv161.symm)
          have hv163 : c * d = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (c * ·) (congrArg (· * d) hv158))).symm.trans
              (eq677 c d)).trans hv158.symm)).trans hv162.symm)
          have hv164 : c * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hv162))).symm.trans
              (eq677 a c)).trans hv163.symm)).trans hd.symm.symm)
          exact absurd (mul_left_cancel (hv164.trans hv162.symm)) (hac.symm)
        · -- $e \diamond b = c$
          exact absurd (mul_left_cancel (hcs159.trans hcs145.symm)) (hab.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs159.trans hv144.symm)) hbf
        · -- $e \diamond b = e$
          have hv165 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs159)).trans hf.symm)).symm.trans (eq677 a b)
          have hv166 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv165.symm)
          rcases hspan (e * e) with hcs167 | hcs167 | hcs167 | hcs167 | hcs167 | hcs167
          · -- $e \diamond e = a$
            have hv168 : c * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                (eq677 a e)).trans hcs167.symm)).trans he.symm.symm)
            have hv169 : e * e = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs159).trans
                hcs167)).trans hba)).symm.trans (eq677 b e)
            exact absurd (hv169.symm.trans hcs167) (hab.symm)
          · -- $e \diamond e = b$
            have e : e * (e * e) = e := by rw [hcs167]; exact hcs159
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs167) (hbe.symm)
          · -- $e \diamond e = c$
            exact absurd (mul_left_cancel (hcs167.trans hcs145.symm)) (hae.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs167.trans hv144.symm)) hef
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs167.trans hcs159.symm)) (hbe.symm)
          · -- $e \diamond e = f$
            have hv170 : e * a = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs159).trans
                hcs167)).trans hv165)).symm.trans (eq677 b e)
            exact absurd (hv170.symm.trans hcs145) hbc
        · -- $e \diamond b = f$
          have hv171 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs159)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv171.symm.trans hba) hae
      · -- $e \diamond a = d$
        exact absurd (mul_left_cancel (hcs145.trans hv144.symm)) haf'
      · -- $e \diamond a = e$
        have hv172 : d * e = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs145))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs173 | hcs173 | hcs173 | hcs173 | hcs173 | hcs173
        · -- $e \diamond b = a$
          have hv174 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs173)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv174
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv175 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs173)).trans hc.symm)).symm.trans (eq677 a b)
          have hv176 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv175.symm)
          rcases hspan (e * e) with hcs177 | hcs177 | hcs177 | hcs177 | hcs177 | hcs177
          · -- $e \diamond e = a$
            have e : e * (e * e) = e := by rw [hcs177]; exact hcs145
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs177) (hae.symm)
          · -- $e \diamond e = b$
            exact absurd (mul_left_cancel (hcs177.trans hcs173.symm)) (hbe.symm)
          · -- $e \diamond e = c$
            have hv178 : e * d = a :=
              (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hcs145).trans
                hcs177)).trans hd.symm)).symm.trans (eq677 a e)
            have hv179 : c * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (e * ·) (congrArg (· * e) hcs177))).symm.trans
                (eq677 e e)).trans hcs145.symm)).trans hv178.symm)
            have hv180 : d * f = f :=
              mul_left_cancel (((congrArg (e * ·) (congrArg (d * ·)
                ((congrArg (· * e) hv178).trans hf.symm))).symm.trans
                (eq677 d e)).trans hv144.symm)
            have hv181 : f * d = a :=
              mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                (congrArg (f * ·) (congrArg (· * d) hv180))).symm.trans
                (eq677 f d)).trans hv180.symm)).trans hcs1.symm)
            have hv182 : e * c = f := by
              rcases hspan (e * c) with hz | hz | hz | hz | hz | hz
              · exact absurd (mul_left_cancel (hz.trans hv178.symm)) hcd
              · exact absurd (mul_left_cancel (hz.trans hcs173.symm)) (hbc.symm)
              · exact absurd (mul_left_cancel (hz.trans hcs177.symm)) hce
              · exact absurd (mul_left_cancel (hz.trans hv144.symm)) hcf
              · exact absurd (mul_left_cancel (hz.trans hcs145.symm)) (hac.symm)
              · exact hz
            have hv183 : f * c = c :=
              mul_left_cancel (((congrArg (e * ·) (congrArg (f * ·)
                ((congrArg (· * e) hv144).trans hv172))).symm.trans
                (eq677 f e)).trans hv182.symm)
            have hv184 : f * f = c :=
              mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
                (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
                (eq677 a f)).trans hv181.symm)).trans hd.symm.symm)
            exact absurd (mul_left_cancel (hv184.trans hv183.symm)) (hcf.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs177.trans hv144.symm)) hef
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs177.trans hcs145.symm)) (hae.symm)
          · -- $e \diamond e = f$
            have hv185 : e * a = a :=
              (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hcs145).trans
                hcs177)).trans haf)).symm.trans (eq677 a e)
            exact absurd (hv185.symm.trans hcs145) hae
        · -- $e \diamond b = c$
          have hv186 : b * d = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs173)).trans hd.symm)).symm.trans (eq677 a b)
          have hv187 : f * a = b :=
            (congrArg (f * ·) ((congrArg (b * ·) ((congrArg (· * f) hfb).trans
              hv144)).trans hv186)).symm.trans (eq677 b f)
          exact absurd (hv187.symm.trans hcs1) hbf
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs173.trans hv144.symm)) hbf
        · -- $e \diamond b = e$
          exact absurd (mul_left_cancel (hcs173.trans hcs145.symm)) (hab.symm)
        · -- $e \diamond b = f$
          have hv188 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs173)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv188.symm.trans hba) hae
      · -- $e \diamond a = f$
        have hv189 : d * f = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs145))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs190 | hcs190 | hcs190 | hcs190 | hcs190 | hcs190
        · -- $e \diamond b = a$
          have hv191 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs190)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv191
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv192 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs190)).trans hc.symm)).symm.trans (eq677 a b)
          have hv193 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv192.symm)
          rcases hspan (e * e) with hcs194 | hcs194 | hcs194 | hcs194 | hcs194 | hcs194
          · -- $e \diamond e = a$
            have hv195 : f * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                (eq677 a e)).trans hcs194.symm)).trans he.symm.symm)
            have hv196 : e * d = e :=
              (congrArg (e * ·) ((congrArg (e * ·) ((congrArg (· * e) hcs194).trans
                hf.symm)).trans hv144)).symm.trans (eq677 e e)
            have hv197 : d * a = f :=
              mul_left_cancel (((congrArg (e * ·) (congrArg (d * ·)
                ((congrArg (· * e) hv196).trans hcs194))).symm.trans
                (eq677 d e)).trans hv144.symm)
            have hv198 : e * c = b :=
              mul_left_cancel (((congrArg (f * ·) (congrArg (e * ·)
                ((congrArg (· * f) hv195).trans hv189))).symm.trans
                (eq677 e f)).trans hfb.symm)
            exact absurd (mul_left_cancel (hv198.trans hcs190.symm)) (hbc.symm)
          · -- $e \diamond e = b$
            exact absurd (mul_left_cancel (hcs194.trans hcs190.symm)) (hbe.symm)
          · -- $e \diamond e = c$
            rcases hspan (e * c) with hcs199 | hcs199 | hcs199 | hcs199 | hcs199 | hcs199
            · -- $e \diamond c = a$
              have hv200 : f * e = b :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                  (eq677 a e)).trans hcs199.symm)).trans hc.symm.symm)
              have hv201 : c * f = e :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
                  ((congrArg (· * e) hcs199).trans hf.symm))).symm.trans
                  (eq677 c e)).trans hcs194.symm)
              have hv202 : b * d = e :=
                mul_left_cancel (((congrArg (f * ·) (congrArg (b * ·)
                  ((congrArg (· * f) hfb).trans hv144))).symm.trans
                  (eq677 b f)).trans hv200.symm)
              exact absurd (mul_left_cancel (hv202.trans hba.symm)) (had.symm)
            · -- $e \diamond c = b$
              exact absurd (mul_left_cancel (hcs199.trans hcs190.symm)) (hbc.symm)
            · -- $e \diamond c = c$
              exact absurd (mul_left_cancel (hcs199.trans hcs194.symm)) hce
            · -- $e \diamond c = d$
              exact absurd (mul_left_cancel (hcs199.trans hv144.symm)) hcf
            · -- $e \diamond c = e$
              have e : e * (e * e) = e := by rw [hcs194]; exact hcs199
              exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs194) (hce.symm)
            · -- $e \diamond c = f$
              exact absurd (mul_left_cancel (hcs199.trans hcs145.symm)) (hac.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs194.trans hv144.symm)) hef
          · -- $e \diamond e = e$
            rcases hspan (e * c) with hcs203 | hcs203 | hcs203 | hcs203 | hcs203 | hcs203
            · -- $e \diamond c = a$
              have hv204 : f * e = b :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                  (eq677 a e)).trans hcs203.symm)).trans hc.symm.symm)
              have hv205 : b * d = e :=
                mul_left_cancel (((congrArg (f * ·) (congrArg (b * ·)
                  ((congrArg (· * f) hfb).trans hv144))).symm.trans
                  (eq677 b f)).trans hv204.symm)
              exact absurd (mul_left_cancel (hv205.trans hba.symm)) (had.symm)
            · -- $e \diamond c = b$
              exact absurd (mul_left_cancel (hcs203.trans hcs190.symm)) (hbc.symm)
            · -- $e \diamond c = c$
              have hv206 : c * e = a :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (c * ·) (congrArg (· * e) hcs203))).symm.trans
                  (eq677 c e)).trans hcs203.symm)).trans hv193.symm)
              have hv207 : c * c = d :=
                mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
                  (congrArg (a * ·) (congrArg (· * c) hv193))).symm.trans
                  (eq677 a c)).trans hv206.symm)).trans he.symm.symm)
              have hv208 : d * c = e := by
                have e := eq_cube_of_mul_eq hcs203
                rw [hv207] at e
                exact e.symm
              have hv209 : e * d = a := by
                rcases hspan (e * d) with hz | hz | hz | hz | hz | hz
                · exact hz
                · exact absurd (mul_left_cancel (hz.trans hcs190.symm)) (hbd.symm)
                · exact absurd (mul_left_cancel (hz.trans hcs203.symm)) (hcd.symm)
                · exact absurd (mul_left_cancel (hz.trans hv144.symm)) hdf
                · exact absurd (mul_left_cancel (hz.trans hcs194.symm)) hde
                · exact absurd (mul_left_cancel (hz.trans hcs145.symm)) (had.symm)
              have hv210 : b * d = c :=
                (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hv192).trans
                  hc.symm)).trans hv207)).symm.trans (eq677 c b)
              have hv211 : f * e = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                  (eq677 a e)).trans hv209.symm)).trans hd.symm.symm)
              have hv212 : e * c = d :=
                (congrArg (e * ·) ((congrArg (d * ·) ((congrArg (· * e) hv209).trans
                  hf.symm)).trans hv189)).symm.trans (eq677 d e)
              exact absurd (hv212.symm.trans hcs203) (hcd.symm)
            · -- $e \diamond c = d$
              exact absurd (mul_left_cancel (hcs203.trans hv144.symm)) hcf
            · -- $e \diamond c = e$
              exact absurd (mul_left_cancel (hcs203.trans hcs194.symm)) hce
            · -- $e \diamond c = f$
              exact absurd (mul_left_cancel (hcs203.trans hcs145.symm)) (hac.symm)
          · -- $e \diamond e = f$
            exact absurd (mul_left_cancel (hcs194.trans hcs145.symm)) (hae.symm)
        · -- $e \diamond b = c$
          have hv213 : b * d = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs190)).trans hd.symm)).symm.trans (eq677 a b)
          have hv214 : f * a = b :=
            (congrArg (f * ·) ((congrArg (b * ·) ((congrArg (· * f) hfb).trans
              hv144)).trans hv213)).symm.trans (eq677 b f)
          exact absurd (hv214.symm.trans hcs1) hbf
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs190.trans hv144.symm)) hbf
        · -- $e \diamond b = e$
          have hv215 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs190)).trans hf.symm)).symm.trans (eq677 a b)
          have hv216 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv215.symm)
          rcases hspan (e * e) with hcs217 | hcs217 | hcs217 | hcs217 | hcs217 | hcs217
          · -- $e \diamond e = a$
            have hv218 : f * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                (eq677 a e)).trans hcs217.symm)).trans he.symm.symm)
            have hv219 : e * e = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs190).trans
                hcs217)).trans hba)).symm.trans (eq677 b e)
            exact absurd (hv219.symm.trans hcs217) (hab.symm)
          · -- $e \diamond e = b$
            have e : e * (e * e) = e := by rw [hcs217]; exact hcs190
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs217) (hbe.symm)
          · -- $e \diamond e = c$
            rcases hspan (e * c) with hcs220 | hcs220 | hcs220 | hcs220 | hcs220 | hcs220
            · -- $e \diamond c = a$
              have hv221 : f * e = b :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                  (eq677 a e)).trans hcs220.symm)).trans hc.symm.symm)
              have hv222 : c * f = e :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
                  ((congrArg (· * e) hcs220).trans hf.symm))).symm.trans
                  (eq677 c e)).trans hcs217.symm)
              have hv223 : b * d = e :=
                mul_left_cancel (((congrArg (f * ·) (congrArg (b * ·)
                  ((congrArg (· * f) hfb).trans hv144))).symm.trans
                  (eq677 b f)).trans hv221.symm)
              exact absurd (mul_left_cancel (hv223.trans hba.symm)) (had.symm)
            · -- $e \diamond c = b$
              have e : e * (e * (e * e)) = e := by rw [hcs217, hcs220]; exact hcs190
              exact absurd ((isIdempotentElem_of_mul_mul_sq e).eq.symm.trans hcs217) (hce.symm)
            · -- $e \diamond c = c$
              exact absurd (mul_left_cancel (hcs220.trans hcs217.symm)) hce
            · -- $e \diamond c = d$
              exact absurd (mul_left_cancel (hcs220.trans hv144.symm)) hcf
            · -- $e \diamond c = e$
              exact absurd (mul_left_cancel (hcs220.trans hcs190.symm)) (hbc.symm)
            · -- $e \diamond c = f$
              exact absurd (mul_left_cancel (hcs220.trans hcs145.symm)) (hac.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs217.trans hv144.symm)) hef
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs217.trans hcs190.symm)) (hbe.symm)
          · -- $e \diamond e = f$
            exact absurd (mul_left_cancel (hcs217.trans hcs145.symm)) (hae.symm)
        · -- $e \diamond b = f$
          exact absurd (mul_left_cancel (hcs190.trans hcs145.symm)) (hab.symm)


end OrderSix
end Spectrum.E677.OrderSix

import equational_theories.Spectrum.Equation677.OrderSix.SixCycle

namespace Spectrum.E677.OrderSix
universe u
open scoped Spectrum.E677.OrderSix
local infixl:70 " * " => Magma.op
variable {M : Type u} [Magma M] [Fact (Equation677 M)] [Finite M]

/-- **At order six, $L_a$ fixes no point but $a$.**

If $a \diamond m = m$ then $a$ is a left unit of $m$, hence its cube $a = (m \diamond m) \diamond m$
(`eq_cube_of_mul_eq`), and $m$ satisfies Equation 255. An idempotent $m$ is its own cube, so then
$a = m$. Otherwise the degree of $m$ is at most $6$; it is not $1$, $2$ or $3$, it is not $4$ or
$5$ because $m$ satisfies Equation 255, and it is not $6$ by
`not_hasDeg_six_of_card_eq_six`. -/
theorem eq_of_mul_eq_self_of_card_eq_six (hM : Nat.card M = 6) {a m : M} (h : a * m = m) :
    a = m := by
  have hcube : a = m * m * m := eq_cube_of_mul_eq h
  have h255 : Eq255At m := eq255At_of_exists_mul_eq ⟨a, h⟩
  by_cases hid : Idempotent m
  · rw [hcube, hid.eq, hid.eq]
  · obtain ⟨n, hn, hdeg⟩ := exists_hasDeg m
    rw [hM] at hn
    have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
      have := hdeg.1
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hid hdeg.2.1).elim
    · exact absurd hdeg (not_hasDeg_two m)
    · exact absurd hdeg (not_hasDeg_three m)
    · exact absurd hdeg (not_hasDeg_four_of_eq255At h255)
    · exact absurd hdeg (not_hasDeg_five_of_eq255At h255)
    · exact absurd hdeg (not_hasDeg_six_of_card_eq_six hM m)

/-- **A six-element magma has no element of degree $5$.**

The orbit $a, b, c, d, e$ of $a$ under $L_a$ misses exactly one point $m$. Since $L_a$ is a
bijection mapping the orbit onto itself, it maps $m$ to $m$; and
`eq_of_mul_eq_self_of_card_eq_six` forbids a fixed point $m \neq a$. -/
theorem not_hasDeg_five_of_card_eq_six (hM : Nat.card M = 6) (a : M) : ¬ HasDeg a 5 := by
  intro hdeg
  -- one turn of the orbit, named
  obtain ⟨b, hb⟩ : ∃ b, b = a * a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = a * b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = a * c := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = a * d := ⟨_, rfl⟩
  -- the turn closes up: $L_a(e) = a$
  have hae0 : a * e = a := by
    rw [he, hd, hc, hb]
    exact hdeg.2.1
  -- distinctness of one turn
  have hNE : ∀ m n : Nat, m < 5 → n < 5 → m ≠ n →
      leftApplyMul a a m ≠ leftApplyMul a a n := fun _ _ hm hn hmn => hdeg.ne hm hn hmn
  have hab : a ≠ b := by rw [hb]; exact hNE 0 1 (by omega) (by omega) (by omega)
  have hac : a ≠ c := by rw [hc, hb]; exact hNE 0 2 (by omega) (by omega) (by omega)
  have had : a ≠ d := by rw [hd, hc, hb]; exact hNE 0 3 (by omega) (by omega) (by omega)
  have hae : a ≠ e := by rw [he, hd, hc, hb]; exact hNE 0 4 (by omega) (by omega) (by omega)
  have hbc : b ≠ c := by rw [hc, hb]; exact hNE 1 2 (by omega) (by omega) (by omega)
  have hbd : b ≠ d := by rw [hd, hc, hb]; exact hNE 1 3 (by omega) (by omega) (by omega)
  have hbe : b ≠ e := by rw [he, hd, hc, hb]; exact hNE 1 4 (by omega) (by omega) (by omega)
  have hcd : c ≠ d := by rw [hd, hc, hb]; exact hNE 2 3 (by omega) (by omega) (by omega)
  have hce : c ≠ e := by rw [he, hd, hc, hb]; exact hNE 2 4 (by omega) (by omega) (by omega)
  have hde : d ≠ e := by rw [he, hd, hc, hb]; exact hNE 3 4 (by omega) (by omega) (by omega)
  -- the one point the orbit misses
  obtain ⟨m, hm⟩ := exists_notMem (l := [a, b, c, d, e])
    (by simp [hM])
  have ham : a ≠ m := fun h => hm (by rw [h]; simp)
  have hbm : b ≠ m := fun h => hm (by rw [h]; simp)
  have hcm : c ≠ m := fun h => hm (by rw [h]; simp)
  have hdm : d ≠ m := fun h => hm (by rw [h]; simp)
  have hem : e ≠ m := fun h => hm (by rw [h]; simp)
  have hspan : ∀ z : M, z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = m :=
    span_six hM hab hac had hae ham hbc hbd hbe hbm hcd hce hcm hde hdm hem
  -- $L_a$ maps the orbit onto itself, so it fixes $m$
  rcases hspan (a * m) with h | h | h | h | h | h
  · -- $a \diamond m = a = a \diamond e$
    exact hem (mul_left_cancel (hae0.trans h.symm))
  · -- $a \diamond m = b = a \diamond a$
    exact ham (mul_left_cancel (h.trans hb)).symm
  · -- $a \diamond m = c = a \diamond b$
    exact hbm (mul_left_cancel (h.trans hc)).symm
  · -- $a \diamond m = d = a \diamond c$
    exact hcm (mul_left_cancel (h.trans hd)).symm
  · -- $a \diamond m = e = a \diamond d$
    exact hdm (mul_left_cancel (h.trans he)).symm
  · -- $a \diamond m = m$
    exact ham (eq_of_mul_eq_self_of_card_eq_six hM h)

/-- **A six-element magma has no element of degree $4$.**

The orbit $a, b, c, d$ of $a$ under $L_a$ misses two points $u, v$, which $L_a$ permutes. A fixed
one is forbidden by `eq_of_mul_eq_self_of_card_eq_six`, so $L_a$ swaps them. In that
configuration Equation 255 fails at $a$ — it would make $a$ idempotent through
`isIdempotentElem_of_mul_sq_eq_sq_mul`, as $L_a^4(a) = a$ — so no element is a left unit for $a$,
and a case analysis over the cell $d \diamond a$ and the row of $c$ refutes the table. -/
theorem not_hasDeg_four_of_card_eq_six (hM : Nat.card M = 6) (a : M) : ¬ HasDeg a 4 := by
  intro hdeg
  have hnid : ¬ Idempotent a := fun h => hdeg.2.2 1 (by decide) (by decide) h
  -- one turn of the orbit, named
  obtain ⟨b, hb⟩ : ∃ b, b = a * a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = a * b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = a * c := ⟨_, rfl⟩
  -- the turn closes up: $L_a(d) = a$
  have had0 : a * d = a := by
    rw [hd, hc, hb]
    exact hdeg.2.1
  -- the two backward names: $d = a / a$ and $c = (a \diamond a) \diamond a$
  have hDdiv : d = a / a := (div_eq_iff_mul_eq.mpr had0).symm
  have hCcube : c = a * a * a :=
    (div_eq_iff_mul_eq.mpr (hd.symm.trans hDdiv)).symm.trans div_div_eq_mul_mul
  -- the two seeded cells: the cube is $b \diamond a$, and `div_self_mul_sq`
  have hba : b * a = c := by rw [hCcube, hb]
  have hdb : d * b = c := by rw [hDdiv, hb, hCcube]; exact div_self_mul_sq a
  -- distinctness of one turn
  have hNE : ∀ m n : Nat, m < 4 → n < 4 → m ≠ n →
      leftApplyMul a a m ≠ leftApplyMul a a n := fun _ _ hm hn hmn => hdeg.ne hm hn hmn
  have hab : a ≠ b := by rw [hb]; exact hNE 0 1 (by omega) (by omega) (by omega)
  have hac : a ≠ c := by rw [hc, hb]; exact hNE 0 2 (by omega) (by omega) (by omega)
  have had : a ≠ d := by rw [hd, hc, hb]; exact hNE 0 3 (by omega) (by omega) (by omega)
  have hbc : b ≠ c := by rw [hc, hb]; exact hNE 1 2 (by omega) (by omega) (by omega)
  have hbd : b ≠ d := by rw [hd, hc, hb]; exact hNE 1 3 (by omega) (by omega) (by omega)
  have hcd : c ≠ d := by rw [hd, hc, hb]; exact hNE 2 3 (by omega) (by omega) (by omega)
  -- the two points the orbit misses
  obtain ⟨u, hu⟩ := exists_notMem (l := [a, b, c, d])
    (by simp [hM])
  obtain ⟨v, hv⟩ := exists_notMem (l := [u, a, b, c, d])
    (by simp [hM])
  have hau : a ≠ u := fun h => hu (by rw [h]; simp)
  have hbu : b ≠ u := fun h => hu (by rw [h]; simp)
  have hcu : c ≠ u := fun h => hu (by rw [h]; simp)
  have hdu : d ≠ u := fun h => hu (by rw [h]; simp)
  have huv : u ≠ v := fun h => hv (by rw [h]; simp)
  have hav : a ≠ v := fun h => hv (by rw [h]; simp)
  have hbv : b ≠ v := fun h => hv (by rw [h]; simp)
  have hcv : c ≠ v := fun h => hv (by rw [h]; simp)
  have hdv : d ≠ v := fun h => hv (by rw [h]; simp)
  -- the six elements exhaust the carrier
  have hspan : ∀ z : M, z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = u ∨ z = v :=
    span_six hM hab hac had hau hav hbc hbd hbu hbv hcd hcu hcv hdu hdv huv
  -- $L_a$ maps the orbit onto itself, so it permutes $\{u, v\}$, and it fixes neither
  have hauv : a * u = v := by
    rcases hspan (a * u) with h | h | h | h | h | h
    · exact absurd (mul_left_cancel (had0.trans h.symm)) hdu
    · exact absurd (mul_left_cancel (h.trans hb)).symm hau
    · exact absurd (mul_left_cancel (h.trans hc)).symm hbu
    · exact absurd (mul_left_cancel (h.trans hd)).symm hcu
    · exact absurd (eq_of_mul_eq_self_of_card_eq_six hM h) hau
    · exact h
  have havu : a * v = u := by
    rcases hspan (a * v) with h | h | h | h | h | h
    · exact absurd (mul_left_cancel (had0.trans h.symm)) hdv
    · exact absurd (mul_left_cancel (h.trans hb)).symm hav
    · exact absurd (mul_left_cancel (h.trans hc)).symm hbv
    · exact absurd (mul_left_cancel (h.trans hd)).symm hcv
    · exact h
    · exact absurd (eq_of_mul_eq_self_of_card_eq_six hM h) hav
  -- no element is a left unit for $a$
  have hno : ∀ x : M, x * a ≠ a := by
    intro x hx
    have hxc : x = c := by
      have h' := eq_cube_of_mul_eq hx
      rw [← hb, hba] at h'
      exact h'
    have h255 : Eq255At a := by
      change a * a * a * a = a
      rw [← hb, hba, ← hxc]
      exact hx
    have h4 : a * (a * a) = a * a * a := by rw [← hb, hc.symm, hba]
    exact hnid (isIdempotentElem_of_mul_sq_eq_sq_mul h255 h4)
  rcases hspan (d * a) with hcs1 | hcs1 | hcs1 | hcs1 | hcs1 | hcs1
  · -- $d \diamond a = a$
    exact absurd hcs1 (hno _)
  · -- $d \diamond a = b$
    have e1 : d * a = a * a := hcs1.trans hb.symm.symm
    have e2 : d * (a * a) = a * (a * a) := by
      rw [hb.symm]
      exact hdb.trans hc.symm.symm
    exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (had.symm)
  · -- $d \diamond a = c$
    exact absurd (mul_left_cancel (hcs1.trans hdb.symm)) hab
  · -- $d \diamond a = d$
    have hv2 : c * d = b :=
      mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
        ((congrArg (· * a) hd.symm).trans hcs1))).symm.trans
        (eq677 c a)).trans hc.symm.symm)
    rcases hspan (c * a) with hcs3 | hcs3 | hcs3 | hcs3 | hcs3 | hcs3
    · -- $c \diamond a = a$
      exact absurd hcs3 (hno _)
    · -- $c \diamond a = b$
      exact absurd (mul_left_cancel (hcs3.trans hv2.symm)) had
    · -- $c \diamond a = c$
      have hv4 : b * c = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs3))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv5 : c * b = b :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv4.symm)).trans hc.symm.symm)
      exact absurd (mul_left_cancel (hv5.trans hv2.symm)) hbd
    · -- $c \diamond a = d$
      have hv6 : b * d = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs3))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv7 : c * b = c :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv6.symm)).trans hd.symm.symm)
      rcases hspan (c * c) with hcs8 | hcs8 | hcs8 | hcs8 | hcs8 | hcs8
      · -- $c \diamond c = a$
        have hv9 : d * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
            (eq677 a c)).trans hcs8.symm)).trans hc.symm.symm)
        have hv10 : c * c = b :=
          (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv7).trans
            hcs8)).trans hba)).symm.trans (eq677 b c)
        exact absurd (hv10.symm.trans hcs8) (hab.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs8.trans hv2.symm)) hcd
      · -- $c \diamond c = c$
        exact absurd (mul_left_cancel (hcs8.trans hv7.symm)) (hbc.symm)
      · -- $c \diamond c = d$
        exact absurd (mul_left_cancel (hcs8.trans hcs3.symm)) (hac.symm)
      · -- $c \diamond c = u$
        have hv11 : b * u = d :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv7).trans hcs8))).symm.trans
            (eq677 b c)).trans hv2.symm)
        have hv12 : u * c = d :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (c * ·) (congrArg (· * c) hcs8))).symm.trans
            (eq677 c c)).trans hv7.symm)).trans hv2.symm)
        have hv13 : d * c = u :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
            ((congrArg (· * b) hv6).trans hc.symm))).symm.trans
            (eq677 d b)).trans hv11.symm)
        have hv14 : b * d = u :=
          (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv11).trans
            hdb)).trans hv12)).symm.trans (eq677 u b)
        exact absurd (hv14.symm.trans hv6) (hau.symm)
      · -- $c \diamond c = v$
        have hv15 : b * v = d :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv7).trans hcs8))).symm.trans
            (eq677 b c)).trans hv2.symm)
        have hv16 : v * c = d :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (c * ·) (congrArg (· * c) hcs8))).symm.trans
            (eq677 c c)).trans hv7.symm)).trans hv2.symm)
        have hv17 : d * c = v :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
            ((congrArg (· * b) hv6).trans hc.symm))).symm.trans
            (eq677 d b)).trans hv15.symm)
        have hv18 : b * d = v :=
          (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv15).trans
            hdb)).trans hv16)).symm.trans (eq677 v b)
        exact absurd (hv18.symm.trans hv6) (hav.symm)
    · -- $c \diamond a = u$
      have hv19 : b * u = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs3))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv20 : c * b = v :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv19.symm)).trans havu.symm)
      rcases hspan (c * c) with hcs21 | hcs21 | hcs21 | hcs21 | hcs21 | hcs21
      · -- $c \diamond c = a$
        have hv22 : u * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
            (eq677 a c)).trans hcs21.symm)).trans hc.symm.symm)
        have hv23 : c * b = c :=
          (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs21).trans
            hd.symm)).trans hv2)).symm.trans (eq677 c c)
        exact absurd (hv23.symm.trans hv20) hcv
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs21.trans hv2.symm)) hcd
      · -- $c \diamond c = c$
        rcases hspan (c * u) with hcs24 | hcs24 | hcs24 | hcs24 | hcs24 | hcs24
        · -- $c \diamond u = a$
          have hv25 : u * c = v :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
              (eq677 a c)).trans hcs24.symm)).trans havu.symm)
          have hv26 : u * d = a :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hcs24).trans hd.symm))).symm.trans
              (eq677 u c)).trans hcs3.symm)
          have hv27 : c * v = d := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact absurd (mul_left_cancel (hz.trans hcs24.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv2.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs21.symm)) (hcv.symm)
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hav.symm)
            · exact absurd (mul_left_cancel (hz.trans hv20.symm)) (hbv.symm)
          have hv28 : v * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (u * ·) (congrArg (· * a) hauv))).symm.trans
              (eq677 u a)).trans havu.symm)).trans hv25.symm)
          have hv29 : b * v = u :=
            (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv19).trans
              hc.symm)).trans hv25)).symm.trans (eq677 u b)
          have hv30 : v * a = a :=
            (congrArg (v * ·) ((congrArg (a * ·) ((congrArg (· * v) hv28).trans
              hv27)).trans had0)).symm.trans (eq677 a v)
          exact absurd (hv30.symm.trans hv28) hac
        · -- $c \diamond u = b$
          exact absurd (mul_left_cancel (hcs24.trans hv2.symm)) (hdu.symm)
        · -- $c \diamond u = c$
          exact absurd (mul_left_cancel (hcs24.trans hcs21.symm)) (hcu.symm)
        · -- $c \diamond u = d$
          have hv31 : c * v = a := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv2.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs21.symm)) (hcv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs24.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hav.symm)
            · exact absurd (mul_left_cancel (hz.trans hv20.symm)) (hbv.symm)
          have hv32 : u * c = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
              (eq677 a c)).trans hv31.symm)).trans hauv.symm)
          have hv33 : v * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (v * ·)
              ((congrArg (· * c) hv31).trans hd.symm))).symm.trans
              (eq677 v c)).trans hv20.symm)
          have hv34 : b * u = u :=
            (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv19).trans
              hc.symm)).trans hv32)).symm.trans (eq677 u b)
          exact absurd (hv34.symm.trans hv19) (hau.symm)
        · -- $c \diamond u = u$
          exact absurd (mul_left_cancel (hcs24.trans hcs3.symm)) (hau.symm)
        · -- $c \diamond u = v$
          exact absurd (mul_left_cancel (hcs24.trans hv20.symm)) (hbu.symm)
      · -- $c \diamond c = d$
        have hv35 : b * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (d * ·) (congrArg (· * c) hv2))).symm.trans
            (eq677 d c)).trans hcs21.symm)).trans hdb.symm)
        rcases hspan (c * u) with hcs36 | hcs36 | hcs36 | hcs36 | hcs36 | hcs36
        · -- $c \diamond u = a$
          have hv37 : b * b = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
              (congrArg (c * ·) (congrArg (· * b) hv35))).symm.trans
              (eq677 c b)).trans hba.symm)).trans hcs36.symm)
          have hv38 : u * c = b :=
            mul_left_cancel (((congrArg (b * ·) (congrArg (u * ·)
              ((congrArg (· * b) hv19).trans hc.symm))).symm.trans
              (eq677 u b)).trans hv37.symm)
          have hv39 : c * c = a :=
            (congrArg (c * ·) ((congrArg (a * ·) ((congrArg (· * c) hcs3).trans
              hv38)).trans hc.symm)).symm.trans (eq677 a c)
          exact absurd (hv39.symm.trans hcs21) had
        · -- $c \diamond u = b$
          exact absurd (mul_left_cancel (hcs36.trans hv2.symm)) (hdu.symm)
        · -- $c \diamond u = c$
          have hv40 : d * c = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (c * ·) (congrArg (· * c) hcs21))).symm.trans
              (eq677 c c)).trans hcs36.symm)).trans hcs3.symm)
          have hv41 : u * d = a :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hcs36).trans hcs21))).symm.trans
              (eq677 u c)).trans hcs3.symm)
          have hv42 : d * d = b :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (a * ·) (congrArg (· * d) hcs1))).symm.trans
              (eq677 a d)).trans hv40.symm)).trans hc.symm.symm)
          have hv43 : b * b = d :=
            mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
              ((congrArg (· * d) hdb).trans hv2))).symm.trans
              (eq677 b d)).trans hv42.symm)
          have e : b * b * (b * b) = b := by rw [hv43]; exact hv42
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hv43) hbd
        · -- $c \diamond u = d$
          exact absurd (mul_left_cancel (hcs36.trans hcs21.symm)) (hcu.symm)
        · -- $c \diamond u = u$
          exact absurd (mul_left_cancel (hcs36.trans hcs3.symm)) (hau.symm)
        · -- $c \diamond u = v$
          exact absurd (mul_left_cancel (hcs36.trans hv20.symm)) (hbu.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs21.trans hcs3.symm)) (hac.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs21.trans hv20.symm)) (hbc.symm)
    · -- $c \diamond a = v$
      have hv44 : b * v = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs3))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv45 : c * b = u :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv44.symm)).trans hauv.symm)
      rcases hspan (c * c) with hcs46 | hcs46 | hcs46 | hcs46 | hcs46 | hcs46
      · -- $c \diamond c = a$
        have hv47 : v * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
            (eq677 a c)).trans hcs46.symm)).trans hc.symm.symm)
        have hv48 : c * b = c :=
          (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs46).trans
            hd.symm)).trans hv2)).symm.trans (eq677 c c)
        exact absurd (hv48.symm.trans hv45) hcu
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs46.trans hv2.symm)) hcd
      · -- $c \diamond c = c$
        rcases hspan (c * u) with hcs49 | hcs49 | hcs49 | hcs49 | hcs49 | hcs49
        · -- $c \diamond u = a$
          have hv50 : v * c = v :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
              (eq677 a c)).trans hcs49.symm)).trans havu.symm)
          have hv51 : u * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hcs49).trans hd.symm))).symm.trans
              (eq677 u c)).trans hv45.symm)
          have hv52 : c * v = d := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact absurd (mul_left_cancel (hz.trans hcs49.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv2.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs46.symm)) (hcv.symm)
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv45.symm)) (hbv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hav.symm)
          have hv53 : b * v = v :=
            (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv44).trans
              hc.symm)).trans hv50)).symm.trans (eq677 v b)
          exact absurd (hv53.symm.trans hv44) (hav.symm)
        · -- $c \diamond u = b$
          exact absurd (mul_left_cancel (hcs49.trans hv2.symm)) (hdu.symm)
        · -- $c \diamond u = c$
          exact absurd (mul_left_cancel (hcs49.trans hcs46.symm)) (hcu.symm)
        · -- $c \diamond u = d$
          have hv54 : c * v = a := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv2.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs46.symm)) (hcv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs49.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv45.symm)) (hbv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hav.symm)
          have hv55 : v * c = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
              (eq677 a c)).trans hv54.symm)).trans hauv.symm)
          have hv56 : v * d = a :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (v * ·)
              ((congrArg (· * c) hv54).trans hd.symm))).symm.trans
              (eq677 v c)).trans hcs3.symm)
          have hv57 : u * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (v * ·) (congrArg (· * a) havu))).symm.trans
              (eq677 v a)).trans hauv.symm)).trans hv55.symm)
          have hv58 : b * u = v :=
            (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv44).trans
              hc.symm)).trans hv55)).symm.trans (eq677 v b)
          have hv59 : u * a = a :=
            (congrArg (u * ·) ((congrArg (a * ·) ((congrArg (· * u) hv57).trans
              hcs49)).trans had0)).symm.trans (eq677 a u)
          exact absurd (hv59.symm.trans hv57) hac
        · -- $c \diamond u = u$
          exact absurd (mul_left_cancel (hcs49.trans hv45.symm)) (hbu.symm)
        · -- $c \diamond u = v$
          exact absurd (mul_left_cancel (hcs49.trans hcs3.symm)) (hau.symm)
      · -- $c \diamond c = d$
        have hv60 : b * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (d * ·) (congrArg (· * c) hv2))).symm.trans
            (eq677 d c)).trans hcs46.symm)).trans hdb.symm)
        rcases hspan (c * u) with hcs61 | hcs61 | hcs61 | hcs61 | hcs61 | hcs61
        · -- $c \diamond u = a$
          have hv62 : b * b = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
              (congrArg (c * ·) (congrArg (· * b) hv60))).symm.trans
              (eq677 c b)).trans hba.symm)).trans hcs61.symm)
          have hv63 : v * c = v :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
              (eq677 a c)).trans hcs61.symm)).trans havu.symm)
          have hv64 : u * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hcs61).trans hd.symm))).symm.trans
              (eq677 u c)).trans hv45.symm)
          have hv65 : d * u = b :=
            (congrArg (d * ·) ((congrArg (b * ·) ((congrArg (· * d) hdb).trans
              hv2)).trans hv62)).symm.trans (eq677 b d)
          have hv66 : c * v = c := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact absurd (mul_left_cancel (hz.trans hcs61.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv2.symm)) (hdv.symm)
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hcs46.symm)) (hcv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv45.symm)) (hbv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hav.symm)
          have hv67 : u * b = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
              (congrArg (b * ·) (congrArg (· * b) hv62))).symm.trans
              (eq677 b b)).trans hv60.symm)).trans hba.symm)
          have hv68 : b * v = v :=
            (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv44).trans
              hc.symm)).trans hv63)).symm.trans (eq677 v b)
          exact absurd (hv68.symm.trans hv44) (hav.symm)
        · -- $c \diamond u = b$
          exact absurd (mul_left_cancel (hcs61.trans hv2.symm)) (hdu.symm)
        · -- $c \diamond u = c$
          have hv69 : d * c = b :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (c * ·) (congrArg (· * c) hcs46))).symm.trans
              (eq677 c c)).trans hcs61.symm)).trans hv45.symm)
          have hv70 : u * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hcs61).trans hcs46))).symm.trans
              (eq677 u c)).trans hv45.symm)
          have hv71 : b * b = c :=
            mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
              ((congrArg (· * d) hdb).trans hv2))).symm.trans
              (eq677 b d)).trans hv69.symm)
          exact absurd (mul_left_cancel (hv71.trans hba.symm)) (hab.symm)
        · -- $c \diamond u = d$
          exact absurd (mul_left_cancel (hcs61.trans hcs46.symm)) (hcu.symm)
        · -- $c \diamond u = u$
          exact absurd (mul_left_cancel (hcs61.trans hv45.symm)) (hbu.symm)
        · -- $c \diamond u = v$
          exact absurd (mul_left_cancel (hcs61.trans hcs3.symm)) (hau.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs46.trans hv45.symm)) (hbc.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs46.trans hcs3.symm)) (hac.symm)
  · -- $d \diamond a = u$
    have hv72 : c * u = b :=
      mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
        ((congrArg (· * a) hd.symm).trans hcs1))).symm.trans
        (eq677 c a)).trans hc.symm.symm)
    rcases hspan (c * a) with hcs73 | hcs73 | hcs73 | hcs73 | hcs73 | hcs73
    · -- $c \diamond a = a$
      exact absurd hcs73 (hno _)
    · -- $c \diamond a = b$
      exact absurd (mul_left_cancel (hcs73.trans hv72.symm)) hau
    · -- $c \diamond a = c$
      have hv74 : b * c = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv75 : c * b = b :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv74.symm)).trans hc.symm.symm)
      exact absurd (mul_left_cancel (hv75.trans hv72.symm)) hbu
    · -- $c \diamond a = d$
      have hv76 : b * d = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv77 : c * b = c :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv76.symm)).trans hd.symm.symm)
      rcases hspan (c * c) with hcs78 | hcs78 | hcs78 | hcs78 | hcs78 | hcs78
      · -- $c \diamond c = a$
        have hv79 : d * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
            (eq677 a c)).trans hcs78.symm)).trans hc.symm.symm)
        have hv80 : c * c = b :=
          (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv77).trans
            hcs78)).trans hba)).symm.trans (eq677 b c)
        exact absurd (hv80.symm.trans hcs78) (hab.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs78.trans hv72.symm)) hcu
      · -- $c \diamond c = c$
        exact absurd (mul_left_cancel (hcs78.trans hv77.symm)) (hbc.symm)
      · -- $c \diamond c = d$
        exact absurd (mul_left_cancel (hcs78.trans hcs73.symm)) (hac.symm)
      · -- $c \diamond c = u$
        have e : c * (c * (c * c)) = c := by rw [hcs78, hv72]; exact hv77
        exact absurd ((isIdempotentElem_of_mul_mul_sq e).eq.symm.trans hcs78) hcu
      · -- $c \diamond c = v$
        have hv81 : b * v = u :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv77).trans hcs78))).symm.trans
            (eq677 b c)).trans hv72.symm)
        have hv82 : v * c = u :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (c * ·) (congrArg (· * c) hcs78))).symm.trans
            (eq677 c c)).trans hv77.symm)).trans hv72.symm)
        have hv83 : u * a = c :=
          mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
            (congrArg (v * ·) (congrArg (· * a) havu))).symm.trans
            (eq677 v a)).trans hauv.symm)).trans hv82.symm)
        have hv84 : u * c = a :=
          (congrArg (u * ·) ((congrArg (a * ·) ((congrArg (· * u) hv83).trans
            hv72)).trans hc.symm)).symm.trans (eq677 a u)
        have hv85 : c * v = a :=
          mul_left_cancel (((congrArg (u * ·) (congrArg (c * ·)
            ((congrArg (· * u) hv84).trans hauv))).symm.trans
            (eq677 c u)).trans hv83.symm)
        have hv86 : c * d = u := by
          rcases hspan (c * d) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans hv85.symm)) hdv
          · exact absurd (mul_left_cancel (hz.trans hv72.symm)) hdu
          · exact absurd (mul_left_cancel (hz.trans hv77.symm)) (hbd.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs73.symm)) (had.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs78.symm)) (hcd.symm)
        have hv87 : d * c = u :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
            (eq677 a c)).trans hv85.symm)).trans hauv.symm)
        exact absurd (mul_left_cancel (hv87.trans hcs1.symm)) (hac.symm)
    · -- $c \diamond a = u$
      have hv88 : b * u = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv89 : c * b = v :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv88.symm)).trans havu.symm)
      rcases hspan (c * c) with hcs90 | hcs90 | hcs90 | hcs90 | hcs90 | hcs90
      · -- $c \diamond c = a$
        have hv91 : u * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
            (eq677 a c)).trans hcs90.symm)).trans hc.symm.symm)
        have hv92 : u * u = c :=
          (congrArg (u * ·) ((congrArg (c * ·) ((congrArg (· * u) hv91).trans
            hv88)).trans hcs73)).symm.trans (eq677 c u)
        have hv93 : b * b = u :=
          (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv88).trans
            hc.symm)).trans hv91)).symm.trans (eq677 u b)
        have hv94 : v * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (b * ·) (congrArg (· * c) hv89))).symm.trans
            (eq677 b c)).trans hv72.symm)).trans hv93.symm)
        rcases hspan (c * d) with hcs95 | hcs95 | hcs95 | hcs95 | hcs95 | hcs95
        · -- $c \diamond d = a$
          exact absurd (mul_left_cancel (hcs95.trans hcs90.symm)) (hcd.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs95.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          have hv96 : c * c = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs90).trans
              hd.symm)).trans hcs95)).symm.trans (eq677 c c)
          exact absurd (hv96.symm.trans hcs90) (hac.symm)
        · -- $c \diamond d = d$
          have hv97 : c * d = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs90).trans
              hd.symm)).trans hcs95)).symm.trans (eq677 c c)
          exact absurd (hv97.symm.trans hcs95) hcd
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs95.trans hcs73.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs95.trans hv89.symm)) (hbd.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs90.trans hv72.symm)) hcu
      · -- $c \diamond c = c$
        rcases hspan (c * d) with hcs98 | hcs98 | hcs98 | hcs98 | hcs98 | hcs98
        · -- $c \diamond d = a$
          have hv99 : u * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
              (eq677 a c)).trans hcs98.symm)).trans hd.symm.symm)
          exact absurd ((eq_cube_of_mul_eq hcs90).trans (eq_cube_of_mul_eq hv99).symm) hcu
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs98.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          exact absurd (mul_left_cancel (hcs98.trans hcs90.symm)) (hcd.symm)
        · -- $c \diamond d = d$
          have hv100 : c * v = a := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv72.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs90.symm)) (hcv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs98.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs73.symm)) (hav.symm)
            · exact absurd (mul_left_cancel (hz.trans hv89.symm)) (hbv.symm)
          have hv101 : u * c = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
              (eq677 a c)).trans hv100.symm)).trans hauv.symm)
          have hv102 : v * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (v * ·)
              ((congrArg (· * c) hv100).trans hd.symm))).symm.trans
              (eq677 v c)).trans hv89.symm)
          have hv103 : b * u = u :=
            (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv88).trans
              hc.symm)).trans hv101)).symm.trans (eq677 u b)
          exact absurd (hv103.symm.trans hv88) (hau.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs98.trans hcs73.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs98.trans hv89.symm)) (hbd.symm)
      · -- $c \diamond c = d$
        rcases hspan (c * d) with hcs104 | hcs104 | hcs104 | hcs104 | hcs104 | hcs104
        · -- $c \diamond d = a$
          have e1 : c * c = a * c := hcs90.trans hd.symm.symm
          have e2 : c * (a * c) = a * (a * c) := by
            rw [hd.symm]
            exact hcs104.trans had0.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hac.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs104.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          have e : c * (c * c) = c := by rw [hcs90]; exact hcs104
          exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs90) hcd
        · -- $c \diamond d = d$
          exact absurd (mul_left_cancel (hcs104.trans hcs90.symm)) (hcd.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs104.trans hcs73.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs104.trans hv89.symm)) (hbd.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs90.trans hcs73.symm)) (hac.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs90.trans hv89.symm)) (hbc.symm)
    · -- $c \diamond a = v$
      have hv105 : b * v = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv106 : c * b = u :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv105.symm)).trans hauv.symm)
      rcases hspan (c * c) with hcs107 | hcs107 | hcs107 | hcs107 | hcs107 | hcs107
      · -- $c \diamond c = a$
        have hv108 : v * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
            (eq677 a c)).trans hcs107.symm)).trans hc.symm.symm)
        have hv109 : v * v = c :=
          (congrArg (v * ·) ((congrArg (c * ·) ((congrArg (· * v) hv108).trans
            hv105)).trans hcs73)).symm.trans (eq677 c v)
        have hv110 : b * b = v :=
          (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv105).trans
            hc.symm)).trans hv108)).symm.trans (eq677 v b)
        rcases hspan (c * d) with hcs111 | hcs111 | hcs111 | hcs111 | hcs111 | hcs111
        · -- $c \diamond d = a$
          exact absurd (mul_left_cancel (hcs111.trans hcs107.symm)) (hcd.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs111.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          have hv112 : c * c = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs107).trans
              hd.symm)).trans hcs111)).symm.trans (eq677 c c)
          exact absurd (hv112.symm.trans hcs107) (hac.symm)
        · -- $c \diamond d = d$
          have hv113 : c * d = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs107).trans
              hd.symm)).trans hcs111)).symm.trans (eq677 c c)
          exact absurd (hv113.symm.trans hcs111) hcd
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs111.trans hv106.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs111.trans hcs73.symm)) (had.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs107.trans hv72.symm)) hcu
      · -- $c \diamond c = c$
        rcases hspan (c * d) with hcs114 | hcs114 | hcs114 | hcs114 | hcs114 | hcs114
        · -- $c \diamond d = a$
          have hv115 : v * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
              (eq677 a c)).trans hcs114.symm)).trans hd.symm.symm)
          exact absurd ((eq_cube_of_mul_eq hcs107).trans (eq_cube_of_mul_eq hv115).symm) hcv
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs114.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          exact absurd (mul_left_cancel (hcs114.trans hcs107.symm)) (hcd.symm)
        · -- $c \diamond d = d$
          have hv116 : c * v = a := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv72.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs107.symm)) (hcv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs114.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv106.symm)) (hbv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs73.symm)) (hav.symm)
          have hv117 : v * c = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
              (eq677 a c)).trans hv116.symm)).trans hauv.symm)
          have hv118 : v * d = a :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (v * ·)
              ((congrArg (· * c) hv116).trans hd.symm))).symm.trans
              (eq677 v c)).trans hcs73.symm)
          have hv119 : u * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (v * ·) (congrArg (· * a) havu))).symm.trans
              (eq677 v a)).trans hauv.symm)).trans hv117.symm)
          have hv120 : b * u = v :=
            (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv105).trans
              hc.symm)).trans hv117)).symm.trans (eq677 v b)
          have hv121 : u * c = a :=
            (congrArg (u * ·) ((congrArg (a * ·) ((congrArg (· * u) hv119).trans
              hv72)).trans hc.symm)).symm.trans (eq677 a u)
          have hv122 : c * c = b :=
            (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv106).trans
              hv121)).trans hba)).symm.trans (eq677 b c)
          exact absurd (hv122.symm.trans hcs107) hbc
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs114.trans hv106.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs114.trans hcs73.symm)) (had.symm)
      · -- $c \diamond c = d$
        rcases hspan (c * d) with hcs123 | hcs123 | hcs123 | hcs123 | hcs123 | hcs123
        · -- $c \diamond d = a$
          have e1 : c * c = a * c := hcs107.trans hd.symm.symm
          have e2 : c * (a * c) = a * (a * c) := by
            rw [hd.symm]
            exact hcs123.trans had0.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hac.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs123.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          have e : c * (c * c) = c := by rw [hcs107]; exact hcs123
          exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs107) hcd
        · -- $c \diamond d = d$
          exact absurd (mul_left_cancel (hcs123.trans hcs107.symm)) (hcd.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs123.trans hv106.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs123.trans hcs73.symm)) (had.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs107.trans hv106.symm)) (hbc.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs107.trans hcs73.symm)) (hac.symm)
  · -- $d \diamond a = v$
    have hv124 : c * v = b :=
      mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
        ((congrArg (· * a) hd.symm).trans hcs1))).symm.trans
        (eq677 c a)).trans hc.symm.symm)
    rcases hspan (c * a) with hcs125 | hcs125 | hcs125 | hcs125 | hcs125 | hcs125
    · -- $c \diamond a = a$
      exact absurd hcs125 (hno _)
    · -- $c \diamond a = b$
      exact absurd (mul_left_cancel (hcs125.trans hv124.symm)) hav
    · -- $c \diamond a = c$
      have hv126 : b * c = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs125))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv127 : c * b = b :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv126.symm)).trans hc.symm.symm)
      exact absurd (mul_left_cancel (hv127.trans hv124.symm)) hbv
    · -- $c \diamond a = d$
      have hv128 : b * d = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs125))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv129 : c * b = c :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv128.symm)).trans hd.symm.symm)
      rcases hspan (c * c) with hcs130 | hcs130 | hcs130 | hcs130 | hcs130 | hcs130
      · -- $c \diamond c = a$
        have hv131 : d * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
            (eq677 a c)).trans hcs130.symm)).trans hc.symm.symm)
        have hv132 : c * c = b :=
          (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv129).trans
            hcs130)).trans hba)).symm.trans (eq677 b c)
        exact absurd (hv132.symm.trans hcs130) (hab.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs130.trans hv124.symm)) hcv
      · -- $c \diamond c = c$
        exact absurd (mul_left_cancel (hcs130.trans hv129.symm)) (hbc.symm)
      · -- $c \diamond c = d$
        exact absurd (mul_left_cancel (hcs130.trans hcs125.symm)) (hac.symm)
      · -- $c \diamond c = u$
        have hv133 : b * u = v :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv129).trans hcs130))).symm.trans
            (eq677 b c)).trans hv124.symm)
        have hv134 : u * c = v :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (c * ·) (congrArg (· * c) hcs130))).symm.trans
            (eq677 c c)).trans hv129.symm)).trans hv124.symm)
        have hv135 : v * a = c :=
          mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
            (congrArg (u * ·) (congrArg (· * a) hauv))).symm.trans
            (eq677 u a)).trans havu.symm)).trans hv134.symm)
        have hv136 : v * c = a :=
          (congrArg (v * ·) ((congrArg (a * ·) ((congrArg (· * v) hv135).trans
            hv124)).trans hc.symm)).symm.trans (eq677 a v)
        have hv137 : c * u = a :=
          mul_left_cancel (((congrArg (v * ·) (congrArg (c * ·)
            ((congrArg (· * v) hv136).trans havu))).symm.trans
            (eq677 c v)).trans hv135.symm)
        have hv138 : c * d = v := by
          rcases hspan (c * d) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans hv137.symm)) hdu
          · exact absurd (mul_left_cancel (hz.trans hv124.symm)) hdv
          · exact absurd (mul_left_cancel (hz.trans hv129.symm)) (hbd.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs125.symm)) (had.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs130.symm)) (hcd.symm)
          · exact hz
        have hv139 : d * c = v :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
            (eq677 a c)).trans hv137.symm)).trans havu.symm)
        exact absurd (mul_left_cancel (hv139.trans hcs1.symm)) (hac.symm)
      · -- $c \diamond c = v$
        have e : c * (c * (c * c)) = c := by rw [hcs130, hv124]; exact hv129
        exact absurd ((isIdempotentElem_of_mul_mul_sq e).eq.symm.trans hcs130) hcv
    · -- $c \diamond a = u$
      have hv140 : b * u = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs125))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv141 : c * b = v :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv140.symm)).trans havu.symm)
      rcases hspan (c * c) with hcs142 | hcs142 | hcs142 | hcs142 | hcs142 | hcs142
      · -- $c \diamond c = a$
        have hv143 : u * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
            (eq677 a c)).trans hcs142.symm)).trans hc.symm.symm)
        have hv144 : u * u = c :=
          (congrArg (u * ·) ((congrArg (c * ·) ((congrArg (· * u) hv143).trans
            hv140)).trans hcs125)).symm.trans (eq677 c u)
        have hv145 : b * b = u :=
          (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv140).trans
            hc.symm)).trans hv143)).symm.trans (eq677 u b)
        rcases hspan (c * d) with hcs146 | hcs146 | hcs146 | hcs146 | hcs146 | hcs146
        · -- $c \diamond d = a$
          exact absurd (mul_left_cancel (hcs146.trans hcs142.symm)) (hcd.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs146.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          have hv147 : c * c = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs142).trans
              hd.symm)).trans hcs146)).symm.trans (eq677 c c)
          exact absurd (hv147.symm.trans hcs142) (hac.symm)
        · -- $c \diamond d = d$
          have hv148 : c * d = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs142).trans
              hd.symm)).trans hcs146)).symm.trans (eq677 c c)
          exact absurd (hv148.symm.trans hcs146) hcd
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs146.trans hcs125.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs146.trans hv141.symm)) (hbd.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs142.trans hv124.symm)) hcv
      · -- $c \diamond c = c$
        rcases hspan (c * d) with hcs149 | hcs149 | hcs149 | hcs149 | hcs149 | hcs149
        · -- $c \diamond d = a$
          have hv150 : u * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
              (eq677 a c)).trans hcs149.symm)).trans hd.symm.symm)
          exact absurd ((eq_cube_of_mul_eq hcs142).trans (eq_cube_of_mul_eq hv150).symm) hcu
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs149.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          exact absurd (mul_left_cancel (hcs149.trans hcs142.symm)) (hcd.symm)
        · -- $c \diamond d = d$
          have hv151 : c * u = a := by
            rcases hspan (c * u) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv124.symm)) huv
            · exact absurd (mul_left_cancel (hz.trans hcs142.symm)) (hcu.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs149.symm)) (hdu.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs125.symm)) (hau.symm)
            · exact absurd (mul_left_cancel (hz.trans hv141.symm)) (hbu.symm)
          have hv152 : u * c = v :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
              (eq677 a c)).trans hv151.symm)).trans havu.symm)
          have hv153 : u * d = a :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hv151).trans hd.symm))).symm.trans
              (eq677 u c)).trans hcs125.symm)
          have hv154 : v * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (u * ·) (congrArg (· * a) hauv))).symm.trans
              (eq677 u a)).trans havu.symm)).trans hv152.symm)
          have hv155 : b * v = u :=
            (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv140).trans
              hc.symm)).trans hv152)).symm.trans (eq677 u b)
          have hv156 : v * c = a :=
            (congrArg (v * ·) ((congrArg (a * ·) ((congrArg (· * v) hv154).trans
              hv124)).trans hc.symm)).symm.trans (eq677 a v)
          have hv157 : c * c = b :=
            (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv141).trans
              hv156)).trans hba)).symm.trans (eq677 b c)
          exact absurd (hv157.symm.trans hcs142) hbc
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs149.trans hcs125.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs149.trans hv141.symm)) (hbd.symm)
      · -- $c \diamond c = d$
        rcases hspan (c * d) with hcs158 | hcs158 | hcs158 | hcs158 | hcs158 | hcs158
        · -- $c \diamond d = a$
          have e1 : c * c = a * c := hcs142.trans hd.symm.symm
          have e2 : c * (a * c) = a * (a * c) := by
            rw [hd.symm]
            exact hcs158.trans had0.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hac.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs158.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          have e : c * (c * c) = c := by rw [hcs142]; exact hcs158
          exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs142) hcd
        · -- $c \diamond d = d$
          exact absurd (mul_left_cancel (hcs158.trans hcs142.symm)) (hcd.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs158.trans hcs125.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs158.trans hv141.symm)) (hbd.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs142.trans hcs125.symm)) (hac.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs142.trans hv141.symm)) (hbc.symm)
    · -- $c \diamond a = v$
      have hv159 : b * v = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs125))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv160 : c * b = u :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv159.symm)).trans hauv.symm)
      rcases hspan (c * c) with hcs161 | hcs161 | hcs161 | hcs161 | hcs161 | hcs161
      · -- $c \diamond c = a$
        have hv162 : v * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
            (eq677 a c)).trans hcs161.symm)).trans hc.symm.symm)
        have hv163 : v * v = c :=
          (congrArg (v * ·) ((congrArg (c * ·) ((congrArg (· * v) hv162).trans
            hv159)).trans hcs125)).symm.trans (eq677 c v)
        have hv164 : b * b = v :=
          (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv159).trans
            hc.symm)).trans hv162)).symm.trans (eq677 v b)
        have hv165 : u * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (b * ·) (congrArg (· * c) hv160))).symm.trans
            (eq677 b c)).trans hv124.symm)).trans hv164.symm)
        rcases hspan (c * d) with hcs166 | hcs166 | hcs166 | hcs166 | hcs166 | hcs166
        · -- $c \diamond d = a$
          exact absurd (mul_left_cancel (hcs166.trans hcs161.symm)) (hcd.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs166.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          have hv167 : c * c = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs161).trans
              hd.symm)).trans hcs166)).symm.trans (eq677 c c)
          exact absurd (hv167.symm.trans hcs161) (hac.symm)
        · -- $c \diamond d = d$
          have hv168 : c * d = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs161).trans
              hd.symm)).trans hcs166)).symm.trans (eq677 c c)
          exact absurd (hv168.symm.trans hcs166) hcd
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs166.trans hv160.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs166.trans hcs125.symm)) (had.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs161.trans hv124.symm)) hcv
      · -- $c \diamond c = c$
        rcases hspan (c * d) with hcs169 | hcs169 | hcs169 | hcs169 | hcs169 | hcs169
        · -- $c \diamond d = a$
          have hv170 : v * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
              (eq677 a c)).trans hcs169.symm)).trans hd.symm.symm)
          exact absurd ((eq_cube_of_mul_eq hcs161).trans (eq_cube_of_mul_eq hv170).symm) hcv
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs169.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          exact absurd (mul_left_cancel (hcs169.trans hcs161.symm)) (hcd.symm)
        · -- $c \diamond d = d$
          have hv171 : c * u = a := by
            rcases hspan (c * u) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv124.symm)) huv
            · exact absurd (mul_left_cancel (hz.trans hcs161.symm)) (hcu.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs169.symm)) (hdu.symm)
            · exact absurd (mul_left_cancel (hz.trans hv160.symm)) (hbu.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs125.symm)) (hau.symm)
          have hv172 : v * c = v :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
              (eq677 a c)).trans hv171.symm)).trans havu.symm)
          have hv173 : u * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hv171).trans hd.symm))).symm.trans
              (eq677 u c)).trans hv160.symm)
          have hv174 : b * v = v :=
            (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv159).trans
              hc.symm)).trans hv172)).symm.trans (eq677 v b)
          exact absurd (hv174.symm.trans hv159) (hav.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs169.trans hv160.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs169.trans hcs125.symm)) (had.symm)
      · -- $c \diamond c = d$
        rcases hspan (c * d) with hcs175 | hcs175 | hcs175 | hcs175 | hcs175 | hcs175
        · -- $c \diamond d = a$
          have e1 : c * c = a * c := hcs161.trans hd.symm.symm
          have e2 : c * (a * c) = a * (a * c) := by
            rw [hd.symm]
            exact hcs175.trans had0.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hac.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs175.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          have e : c * (c * c) = c := by rw [hcs161]; exact hcs175
          exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs161) hcd
        · -- $c \diamond d = d$
          exact absurd (mul_left_cancel (hcs175.trans hcs161.symm)) (hcd.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs175.trans hv160.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs175.trans hcs125.symm)) (had.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs161.trans hv160.symm)) (hbc.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs161.trans hcs125.symm)) (hac.symm)

/-- **At order six every element is idempotent.** A non-idempotent element has degree $4$, $5$ or
$6$ (degrees $2$ and $3$ never occur, and the degree is at most the order), and each is
excluded above. -/
theorem forall_isIdempotentElem_of_card_eq_six (hM : Nat.card M = 6) (a : M) :
    Idempotent a := by
  by_cases ha : Idempotent a
  · exact ha
  · obtain ⟨n, hn, hdeg⟩ := exists_hasDeg a
    rw [hM] at hn
    have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
      have := hdeg.1
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (ha hdeg.2.1).elim
    · exact absurd hdeg (not_hasDeg_two a)
    · exact absurd hdeg (not_hasDeg_three a)
    · exact absurd hdeg (not_hasDeg_four_of_card_eq_six hM a)
    · exact absurd hdeg (not_hasDeg_five_of_card_eq_six hM a)
    · exact absurd hdeg (not_hasDeg_six_of_card_eq_six hM a)


end Spectrum.E677.OrderSix

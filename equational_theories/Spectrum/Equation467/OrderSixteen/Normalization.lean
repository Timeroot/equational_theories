import equational_theories.Spectrum.Equation467.OrderSixteen.SymmetryData

set_option maxRecDepth 4096
namespace Spectrum.E467.OrderSixteen
open FiniteSearch (relabel)
attribute [local irreducible] cells

def key (i : Case) (f : Point → Point → Point) : Lex (Fin 256 → Point) :=
  toLex (fun j => f (cells i j).1 (cells i j).2)

def Minimal (i : Case) (f : Point → Point → Point) : Prop :=
  ∀ g, InCase i g → key i f ≤ key i g

private theorem finiteMinimum {A B : Type} [Fintype A] [LinearOrder B]
    (P : A → Prop) (K : A → B) (a : A) (ha : P a) :
    ∃ b, P b ∧ ∀ c, P c → K b ≤ K c := by
  classical
  let S := Finset.univ.filter P
  obtain ⟨b,hb,hm⟩ := S.exists_min_image K ⟨a,by simp [S,ha]⟩
  exact ⟨b,(Finset.mem_filter.mp hb).2,fun c hc => hm c (by simp [S,hc])⟩

/-- A least representative exists by finiteness, without computing its orbit. -/
theorem exists_minimal (i : Case) (f : Point → Point → Point) (hf : InCase i f) :
    ∃ g, InCase i g ∧ Minimal i g :=
  finiteMinimum (InCase i) (key i) f hf

theorem case_relabel (i : Case) (f : Point → Point → Point) (hf : InCase i f)
    (e : Equiv.Perm Point) (he0 : e 0 = 0)
    (he : ∀ x, e (axis i x) = axis i (e x)) : InCase i (relabel f e) := by
  refine ⟨holds_relabel f hf.1 e, ?_, ?_⟩
  · intro x
    simp only [relabel, hf.2.1, diagonal]
    split
    · exact e.apply_symm_apply x
    · rw [he, Equiv.apply_symm_apply]
  · intro hi
    have he0' : e.symm 0 = 0 := by apply e.injective; simpa using he0.symm
    funext y
    simp only [relabel, he0', hf.2.2 hi, he, Equiv.apply_symm_apply]

/-- No new cycle or rotation is named before an earlier available one. -/
theorem minimal_groups (i : Case) (f : Point → Point → Point)
    (hf : InCase i f) (hm : Minimal i f) (y : Point) (hy : y.val < fixedCount i)
    (r : Point × ℕ × Point) (hr : r ∈ requests i)
    (hz : f (scanRow i) y = r.2.2) :
    ∃ j : Point, j.val < y.val ∧ r.1.val ≤ (f (scanRow i) j).val ∧
      (f (scanRow i) j).val < r.2.1 := by
  classical
  by_contra hn
  obtain ⟨hless, hcomm, hfix, hout, hmove⟩ := request_checked i r hr
  let e := move i r.1 r.2.2
  have h0 : e 0 = 0 := hfix 0 (initial_cells i).1
  have hsr : e (scanRow i) = scanRow i := hfix _ (initial_cells i).2.1
  have symmfix (x : Point) (hx : x.val < fixedCount i) : e.symm x = x := by
    apply e.injective
    simpa using (hfix x hx).symm
  have smaller : key i (relabel f e) < key i f := by
    refine ⟨⟨y.val, by omega⟩, ?_, ?_⟩
    · intro j hj
      let x : Point := ⟨j.val, by have := y.isLt; change j.val < y.val at hj; omega⟩
      have hx : x.val < y.val := hj
      have hxx : x.val < fixedCount i := lt_trans hx hy
      have hc : cells i j = (scanRow i,x) := initial_cells i |>.2.2 x hxx
      change relabel f e (cells i j).1 (cells i j).2 = f (cells i j).1 (cells i j).2
      rw [hc]
      simp only [relabel, symmfix _ (initial_cells i).2.1, symmfix x hxx]
      apply hout
      exact fun h => hn ⟨x,hx,h⟩
    · change relabel f e (cells i ⟨y.val, by omega⟩).1 (cells i ⟨y.val, by omega⟩).2 <
        f (cells i ⟨y.val, by omega⟩).1 (cells i ⟨y.val, by omega⟩).2
      rw [(initial_cells i).2.2 y hy]
      simp only [relabel, symmfix _ (initial_cells i).2.1, symmfix y hy, hz]
      exact hmove ▸ hless
  exact (not_lt_of_ge (hm _ (case_relabel i f hf e h0 hcomm))) smaller

/-- For the one-moving-cycle cases, all remaining fixed points can be named
in order of first appearance throughout the table. -/
theorem minimal_full (i : Case) (f : Point → Point → Point)
    (hf : InCase i f) (hm : Minimal i f) (hi : fullFirstUse i = true)
    (j : Fin 256) (z : Point) (hz : fullBound i j < z.val)
    (he : f (cells i j).1 (cells i j).2 = z) :
    ∃ t < j, (f (cells i t).1 (cells i t).2).val = z.val - 1 := by
  classical
  obtain ⟨hidem, hout, hin, hc⟩ := full_data i hi
  let a : Point := ⟨z.val - 1, by have := z.isLt; omega⟩
  have haz : a < z := by change z.val - 1 < z.val; omega
  have ha : fixedCount i ≤ a.val := by
    have hb : fixedCount i ≤ fullBound i j := le_max_left _ _
    dsimp [a]; omega
  by_contra! hn
  let C := Finset.univ.filter (fun t : Fin 256 => t ≤ j ∧ f (cells i t).1 (cells i t).2 = z)
  have hnC : C.Nonempty := ⟨j, by simp [C, he]⟩
  let t := C.min' hnC
  have htm := C.min'_mem hnC
  have htj : t ≤ j := (Finset.mem_filter.mp htm).2.1
  have htz : f (cells i t).1 (cells i t).2 = z := (Finset.mem_filter.mp htm).2.2
  let s := Equiv.swap a z
  have sfixed (x : Point) (hx : x < a) : s x = x :=
    Equiv.swap_apply_of_ne_of_ne (ne_of_lt hx) (ne_of_lt (hx.trans haz))
  have sk (x : Point) (hx : x.val < fixedCount i) : s x = x := sfixed x (by change x.val < a.val; omega)
  have hclosed : InCase i (relabel f s) :=
    case_relabel i f hf s (sk 0 (initial_cells i).1)
      (FiniteSearch.commute_of_fixed_initial (axis i) (fixedCount i) hout hin s sk)
  have smaller : key i (relabel f s) < key i f := by
    refine ⟨t, ?_, ?_⟩
    · intro u hut
      have huj : u ≤ j := (le_of_lt hut).trans htj
      have hinputs := hc u j huj
      change s (f (s (cells i u).1) (s (cells i u).2)) = f (cells i u).1 (cells i u).2
      rw [sfixed (cells i u).1 (by change (cells i u).1.val < a.val; dsimp [a]; omega),
          sfixed (cells i u).2 (by change (cells i u).2.val < a.val; dsimp [a]; omega)]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro hh
        exact hn u (lt_of_lt_of_le hut htj) (congrArg Fin.val hh)
      · intro hh
        have hum : u ∈ C := by simp [C, huj, hh]
        exact (not_le_of_gt hut) (C.min'_le u hum)
    · have hinputs := hc t j htj
      change s (f (s (cells i t).1) (s (cells i t).2)) < f (cells i t).1 (cells i t).2
      rw [sfixed (cells i t).1 (by change (cells i t).1.val < a.val; dsimp [a]; omega),
          sfixed (cells i t).2 (by change (cells i t).2.val < a.val; dsimp [a]; omega),
          htz, Equiv.swap_apply_right]
      exact haz
  exact (not_lt_of_ge (hm _ hclosed)) smaller

end Spectrum.E467.OrderSixteen

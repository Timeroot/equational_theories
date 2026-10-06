import equational_theories.Spectrum.Equation467.OrderSixteen.Canonical

namespace Spectrum.E467.OrderSixteen
open FiniteSearch (relabel)

private theorem idempotent_case (f : Point → Point → Point) (hf : Holds f)
    (hd : ∀ x, f x x = x) : ∃ i g, InCase i g := by
  obtain ⟨e, he0, hc⟩ := E63.OrderTen.exists_chain_label (f 0)
  let g := relabel f e
  have hg : Holds g := holds_relabel f hf e
  have hdg (x : Point) : g x x = x := by simp only [g,relabel,hd,Equiv.apply_symm_apply]
  have he0' : e.symm 0 = 0 := by apply e.injective; simpa using he0.symm
  have hgc : ∀ x, (g 0 x).val ≤ x.val+1 := by
    intro x
    simpa only [g,relabel,he0'] using hc x
  have hga : rowAdmissible (g 0) := by
    constructor
    · intro x
      simpa only [E467.square,hdg] using E467.translation_fixed_iff g hg 0 x
    · intro x hx
      exact (E467.no_two_cycle g hg 0 x (g 0 x) rfl hx).symm
  obtain ⟨ha0,i,hi,harow⟩ := row_covers (g 0) (E467.left_injective g hg 0) hgc hga
  let a := canonicalPermutation false (g 0)
  let q := relabel g a
  have ha0' : a.symm 0 = 0 := by apply a.injective; simpa only [Equiv.apply_symm_apply] using ha0.symm
  have hidem : isIdempotent i = true := by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    simp [isIdempotent]
  refine ⟨i,q,holds_relabel g hg a,?_,?_⟩
  · intro x
    simp only [q,relabel,hdg,Equiv.apply_symm_apply,diagonal,hidem,↓reduceIte]
  · intro _
    funext y
    change a (g (a.symm 0) (a.symm y)) = axis i y
    rw [ha0']
    simpa only [a,Equiv.apply_symm_apply] using harow (a.symm y)

/-- Any order-sixteen model belongs to one of the 67 canonical cases.
The two finite checks cover chain-labelled permutations (32768), not 16!.
-/
theorem exists_case (f : Point → Point → Point) (hf : Holds f) : ∃ i g, InCase i g := by
  obtain ⟨e,_,hc⟩ := E63.OrderTen.exists_chain_label (E467.square f)
  let g := relabel f e
  have hg : Holds g := holds_relabel f hf e
  have hgc : ∀ x, (E467.square g x).val ≤ x.val+1 := by
    intro x
    simpa only [E467.square,g,relabel] using hc x
  have hga : squareAdmissible (E467.square g) :=
    ⟨E467.square_period_two g hg,E467.square_period_three g hg⟩
  obtain ⟨d,hd,he⟩ := square_covers (E467.square g) (E467.square_injective g hg) hgc hga
  let a := canonicalPermutation true (E467.square g)
  let q := relabel g a
  have hq : Holds q := holds_relabel g hg a
  have hdq (x : Point) : q x x = d x := by
    change a (E467.square g (a.symm x)) = d x
    simpa only [a,Equiv.apply_symm_apply] using he (a.symm x)
  rcases List.mem_append.mp hd with h | h
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
    let i : Case := ⟨j.val,by omega⟩
    have hi : isIdempotent i = false := by
      simp only [isIdempotent,decide_eq_false_iff_not]
      have := j.isLt
      dsimp [i]
      omega
    refine ⟨i,q,hq,?_,?_⟩
    · intro x
      simpa only [diagonal,hi,↓reduceIte] using hdq x
    · simp [hi]
  · have heq : d = id := by simpa only [List.mem_singleton] using h
    exact idempotent_case q hq (by simpa only [heq,id_eq] using hdq)

spectrum_assert exists_case complete
end Spectrum.E467.OrderSixteen

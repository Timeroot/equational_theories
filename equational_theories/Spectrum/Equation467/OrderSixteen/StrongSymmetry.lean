import equational_theories.Spectrum.Equation467.OrderSixteen.Encoding

/-! Further symmetries used to shorten the order-sixteen refutations. -/
namespace Spectrum.E467.OrderSixteen
open FiniteSearch (relabel)
attribute [local irreducible] cells

def rootOffset (i : Case) : ℕ := if isIdempotent i then 1 else 0
def rootLength (i : Case) : ℕ := fixedCount i - rootOffset i
def rootAction (i : Case) (s : ℕ) (x : Point) : Point :=
  if rootOffset i ≤ x.val ∧ x.val < fixedCount i then
    ⟨(rootOffset i + (x.val-rootOffset i+s)%rootLength i)%16, Nat.mod_lt _ (by decide)⟩
  else x
def rootInverse (i : Case) (s : Point) : Point → Point :=
  rootAction i (rootLength i - s.val%rootLength i)

@[spectrum_native]
theorem root_actions_checked : ∀ (i : Case) (s x : Point),
    rootInverse i s (rootAction i s.val x) = x ∧
    rootAction i s.val (rootInverse i s x) = x ∧
    rootAction i s.val (axis i x) = axis i (rootAction i s.val x) ∧
    (isIdempotent i = true → rootAction i s.val 0 = 0) := by native_decide

def rootPerm (i : Case) (s : Point) : Equiv.Perm Point where
  toFun := rootAction i s.val
  invFun := rootInverse i s
  left_inv := fun x => (root_actions_checked i s x).1
  right_inv := fun x => (root_actions_checked i s x).2.1

theorem case_relabel_general (i : Case) (f : Point → Point → Point) (hf : InCase i f)
    (e : Equiv.Perm Point) (he0 : isIdempotent i = true → e 0 = 0)
    (he : ∀ x, e (axis i x) = axis i (e x)) : InCase i (relabel f e) := by
  refine ⟨holds_relabel f hf.1 e, ?_, ?_⟩
  · intro x
    simp only [relabel, hf.2.1, diagonal]
    split
    · exact e.apply_symm_apply x
    · rw [he, Equiv.apply_symm_apply]
  · intro hi
    have he0' : e.symm 0 = 0 := by apply e.injective; simpa using (he0 hi).symm
    funext y
    simp only [relabel, he0', hf.2.2 hi, he, Equiv.apply_symm_apply]

def rootPosition (i : Case) : Point := if isIdempotent i then 0 else 3

@[spectrum_native]
theorem root_position_checked : ∀ i : Case,
    (rootPosition i).val < fixedCount i ∧
    (isIdempotent i = false → diagonal i 0 = 1 ∧ diagonal i (diagonal i 0) = 2) := by
  native_decide

private theorem row_root_value (i : Case) (f : Point → Point → Point) (hf : InCase i f) :
    f 0 (diagonal i 0) = inverseDiagonal i 0 := by
  have hh := E467.root_square f hf.1 (inverseDiagonal i 0)
  change E467.root f (f _ _) = _ at hh
  rw [hf.2.1, Encoding.inverse_checked] at hh
  simpa only [E467.root, E467.square, hf.2.1] using hh

/-- The three entries before the first free entry are prescribed by the law. -/
theorem prefix_agrees (i : Case) (f g : Point → Point → Point)
    (hf : InCase i f) (hg : InCase i g) (j : Fin 256)
    (hj : j.val < (rootPosition i).val) :
    f (cells i j).1 (cells i j).2 = g (cells i j).1 (cells i j).2 := by
  have hid : isIdempotent i = false := by
    cases h : isIdempotent i <;> simp [rootPosition,h] at hj ⊢
  have h3 : j.val < 3 := by simpa [rootPosition,hid] using hj
  have hk := (root_position_checked i).1
  have hk' : 3 < fixedCount i := by simpa [rootPosition,hid] using hk
  have hc := (initial_cells i).2.2 (⟨j.val,by omega⟩ : Point) (by
    exact lt_trans h3 hk')
  have hc' : cells i j = (0, (⟨j.val,by omega⟩ : Point)) := by
    simpa [scanRow,hid] using hc
  rw [hc']
  obtain ⟨hd,hd2⟩ := (root_position_checked i).2 hid
  have ff : f 0 2 = 2 := by
    have h := (E467.translation_fixed_iff f hf.1 0 (diagonal i (diagonal i 0))).mpr
      (by simp [E467.square,hf.2.1])
    simpa [hd2] using h
  have gg : g 0 2 = 2 := by
    have h := (E467.translation_fixed_iff g hg.1 0 (diagonal i (diagonal i 0))).mpr
      (by simp [E467.square,hg.2.1])
    simpa [hd2] using h
  have hcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
  rcases hcases with h | h | h
  · have he : (⟨j.val,by omega⟩ : Point) = 0 := Fin.ext h
    simp [he,hf.2.1,hg.2.1]
  · have he : (⟨j.val,by omega⟩ : Point) = 1 := Fin.ext h
    simpa [he,hd] using (row_root_value i f hf).trans (row_root_value i g hg).symm
  · have he : (⟨j.val,by omega⟩ : Point) = 2 := Fin.ext h
    simpa [he] using ff.trans gg.symm

/-- Rotate the distinguished cycle so that its first free table entry is least. -/
theorem minimal_rotation (i : Case) (f : Point → Point → Point)
    (hf : InCase i f) (hm : Minimal i f) (s : Point) :
    f (scanRow i) (rootPosition i) ≤
      (rootPerm i s) (f ((rootPerm i s).symm (scanRow i))
        ((rootPerm i s).symm (rootPosition i))) := by
  let e := rootPerm i s
  have hg : InCase i (relabel f e) := case_relabel_general i f hf e
    ((root_actions_checked i s 0).2.2.2) (fun x => (root_actions_checked i s x).2.2.1)
  by_contra hn
  have hc := (initial_cells i).2.2 (rootPosition i) (root_position_checked i).1
  have hs : key i (relabel f e) < key i f := by
    refine ⟨⟨(rootPosition i).val, by have := (rootPosition i).isLt; omega⟩, ?_, ?_⟩
    · intro j hj
      exact prefix_agrees i _ _ hg hf j hj
    · change relabel f e (cells i _).1 (cells i _).2 < f (cells i _).1 (cells i _).2
      rw [hc]
      exact lt_of_not_ge hn
  exact (not_lt_of_ge (hm _ hg)) hs

end Spectrum.E467.OrderSixteen

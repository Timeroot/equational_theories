import equational_theories.Spectrum.Equation167

/-! A finite even involution has a square root. Pair its transpositions and
use a four-cycle on each pair; the fixed points stay fixed. -/

namespace Spectrum.InvolutionRoots
variable {G : Type*} [LinearOrder G] (f : Equiv.Perm G) (hf : ∀ x, f (f x) = x)
abbrev Fixed := {x : G // f x = x}
abbrev Asc := {x : G // x < f x}

def encode (x : G) : Fixed f ⊕ (Asc f × Bool) :=
  if he : f x = x then .inl ⟨x, he⟩
  else if hl : x < f x then .inr (⟨x, hl⟩, false)
  else .inr (⟨f x, by rw [hf]; exact lt_of_le_of_ne (le_of_not_gt hl) he⟩, true)

def decode : Fixed f ⊕ (Asc f × Bool) → G
  | .inl x => x.val
  | .inr (x, false) => x.val
  | .inr (x, true) => f x.val

def orbitEquiv : G ≃ Fixed f ⊕ (Asc f × Bool) where
  toFun := encode f hf
  invFun := decode f
  left_inv x := by
    simp only [encode]
    split_ifs <;> simp_all [decode]
  right_inv := by
    rintro (⟨x,hx⟩ | ⟨⟨x,hx⟩,b⟩)
    · simp [decode, encode, hx]
    · cases b <;> simp [decode, encode, hf, ne_of_lt hx, ne_of_gt hx, hx, not_lt_of_gt hx]

theorem encode_apply (x : G) :
    encode f hf (f x) = Sum.map id (fun q => (q.1, !q.2)) (encode f hf x) := by
  obtain ⟨q, rfl⟩ := (orbitEquiv f hf).symm.surjective x
  rcases q with ⟨x,hx⟩ | ⟨⟨x,hx⟩,b⟩
  · simp [orbitEquiv, decode, encode, hx]
  · cases b <;> simp [orbitEquiv, decode, encode, hf, ne_of_lt hx, ne_of_gt hx, hx, not_lt_of_gt hx]

include hf in
theorem card_decompose [Fintype G] :
    Fintype.card G = Fintype.card (Fixed f) + 2 * Fintype.card (Asc f) := by
  simpa [Fintype.card_sum, Fintype.card_prod, Nat.mul_comm] using
    Fintype.card_congr (orbitEquiv f hf)

include hf in
theorem sign_eq [Fintype G] : Equiv.Perm.sign f = (-1 : ℤˣ) ^ Fintype.card (Asc f) := by
  have hs := Equiv.Perm.sign_eq_sign_of_equiv f
    (Equiv.sumCongr (Equiv.refl (Fixed f)) (Equiv.prodCongrRight fun _ : Asc f => Equiv.boolNot))
    (orbitEquiv f hf) (encode_apply f hf)
  rw [hs, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_prodCongrRight]
  have hb : Equiv.Perm.sign Equiv.boolNot = -1 := by decide
  simp [hb]
  congr 1

def root {K : Type*} (e : Asc f ≃ K × Bool) (x : G) : G :=
  (orbitEquiv f hf).symm (Sum.map id (Bookend.turn e) (orbitEquiv f hf x))

theorem root_twice {K : Type*} (e : Asc f ≃ K × Bool) (x : G) :
    root f hf e (root f hf e x) = f x := by
  apply (orbitEquiv f hf).injective
  simp only [root, Equiv.apply_symm_apply]
  rw [show orbitEquiv f hf (f x) = Sum.map id (fun q => (q.1, !q.2)) (orbitEquiv f hf x)
    from encode_apply f hf x]
  cases orbitEquiv f hf x <;> simp [Bookend.turn_twice]

include hf in
theorem exists_root_of_even [Fintype G] (he : Even (Fintype.card (Asc f))) :
    ∃ r : G → G, ∀ x, r (r x) = f x := by
  classical
  obtain ⟨k,hk⟩ := he
  let e : Asc f ≃ Fin k × Bool := Fintype.equivOfCardEq (by simp [hk, Nat.mul_two])
  exact ⟨root f hf e, root_twice f hf e⟩

include hf in
theorem exists_root_of_sign [Fintype G] (he : Equiv.Perm.sign f = 1) :
    ∃ r : G → G, ∀ x, r (r x) = f x := by
  apply exists_root_of_even f hf
  rw [sign_eq f hf] at he
  exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp he

/-- info: 'Spectrum.InvolutionRoots.exists_root_of_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_root_of_sign
end Spectrum.InvolutionRoots

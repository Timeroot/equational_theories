import equational_theories.Parastrophes.Equation917SandwichCandidate

/-!
# Commuting permutations in the E917 sandwich candidate

This is a reduction of the still-open candidate, not a characterization.
Its common maps a and b extend to three commuting permutations a,b,c such
that every row sends b to a and a to c. There is also the identity
`(b(x))*(c(y)) = x*y`, and `a(b(c(U(x)))) = x`.

The important missing step is the next conjugation, `x*c(y)=b(x*y)`.
It is NOT a consequence of commutativity alone and is not assumed here.
The proof below works by row cancellation and uses no search certificates.
-/
namespace Parastrophes.Eq917Image.SandwichCandidate

private theorem commute_reduction {A : Type} (m : A → A → A)
    (a b c : A → A) (hi : ∀ x, Function.Injective (m x))
    (mb : ∀ x y, m x (b y) = a (m x y))
    (ma : ∀ x y, m x (a y) = c (m x y))
    (inv : ∀ x y, m (b x) (c y) = m x y) :
    Function.Commute b c ∧ Function.Commute a c ∧ Function.Commute a b := by
  have bc : Function.Commute b c := by
    intro x
    apply hi (b x)
    rw [mb, inv, inv, mb]
  have ac : Function.Commute a c := by
    intro x
    apply hi (b x)
    rw [ma, inv, inv, ma]
  refine ⟨bc, ac, ?_⟩
  intro x
  apply hi x
  rw [ma, mb, mb, ma]
  exact (ac (m x x)).symm

/-- A purely algebraic description of the remaining obstruction. No identity
of a, b, c with the identity permutation is claimed. -/
theorem commuting_permutations {A : Type} [Finite A] [Nonempty A]
    (D : Magma A) (h : Identity D) :
    ∃ a b c : A → A,
      Function.Bijective a ∧ Function.Bijective b ∧ Function.Bijective c ∧
      (∀ x y, F D x y = a x) ∧
      (∀ x y, G D x y = b y) ∧
      (∀ x y, D.op x (b y) = a (D.op x y)) ∧
      (∀ x y, D.op x (a y) = c (D.op x y)) ∧
      (∀ x y, D.op (b x) (c y) = D.op x y) ∧
      Function.Commute a b ∧ Function.Commute a c ∧ Function.Commute b c ∧
      (∀ x, a (b (c (U D x))) = x) := by
  classical
  obtain ⟨a, b, ha, hb, hf, hg, hc⟩ := common_maps D h
  have hq := rows D h
  let ae := Equiv.ofBijective a ha
  let be := Equiv.ofBijective b hb
  let ue := Equiv.ofBijective (U D) (unit_bijective D h)
  let c := fun x => ue.symm (be.symm (ae.symm x))
  have hcb : Function.Bijective c :=
    ue.symm.bijective.comp (be.symm.bijective.comp ae.symm.bijective)
  have mb (x y) : D.op x (b y) = a (D.op x y) := by
    rw [← hg x y]
    exact hf (D.op x y) x
  have ma (x y) : D.op x (a y) = c (D.op x y) := by
    have he := hc (c (D.op x y)) x
    have ht : b (U D (c (D.op x y))) = ae.symm (D.op x y) := by
      change be (ue (ue.symm (be.symm (ae.symm (D.op x y))))) = _
      rw [ue.apply_symm_apply, be.apply_symm_apply]
    rw [ht] at he
    have hh : H D (ae.symm (D.op x y)) x = y := by
      apply (hq x).1
      have hz := hf (ae.symm (D.op x y)) x
      exact hz.trans (ae.apply_symm_apply _)
    rwa [hh] at he
  have hH (x y) : H D x (b y) = c (H D x y) := by
    unfold H
    rw [mb, ma]
  have inv (x y) : D.op (b x) (c y) = D.op x y := by
    obtain ⟨t, ht⟩ := ha.2 (D.op x y)
    have hv : H D t x = y := (hq x).1 ((hf t x).trans ht)
    rw [← hv, ← hH]
    exact (hf t (b x)).trans (hf t x).symm
  obtain ⟨bc, ac, ab⟩ := commute_reduction D.op a b c (fun x => (hq x).1) mb ma inv
  refine ⟨a, b, c, ha, hb, hcb, hf, hg, mb, ma, inv, ab, ac, bc, ?_⟩
  intro x
  rw [bc (U D x), ac (b (U D x))]
  change ue.symm (be.symm (ae.symm (ae (be (ue x))))) = x
  rw [ae.symm_apply_apply, be.symm_apply_apply, ue.symm_apply_apply]

end Parastrophes.Eq917Image.SandwichCandidate

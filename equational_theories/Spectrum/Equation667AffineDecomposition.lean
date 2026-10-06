import equational_theories.Spectrum.Equation667AffineStructure

/-! Explicit primary decomposition of affine E667 algebras away from 2 and 5.
The three summands are the Gaussian family, an idempotent E63 family, and
the negative of an idempotent E63 family. All denominators divide ten. -/
namespace Spectrum.E667.AffineStructure
variable {A : Type*} [AddCommGroup A]

def F (g : AddMonoid.End A) := g^2+1
def G (g : AddMonoid.End A) := g^3-g-1

def factor (g : AddMonoid.End A) : Fin 3 → AddMonoid.End A := ![F g,G g,H g]
def projectorN (g : AddMonoid.End A) : Fin 3 → AddMonoid.End A :=
  ![-2*G g*H g, F g*H g*(-2*g^2+g+4), F g*G g*(2*g^2+g-4)]

/-- The three integral projection numerators sum to ten times the identity. -/
theorem projectors_sum (g : AddMonoid.End A) :
    projectorN g 0 + projectorN g 1 + projectorN g 2 = 10 := by
  dsimp [projectorN, F, G, H]
  noncomm_ring
  norm_num

/-- Each numerator takes values in the required kernel when P(g)=0. -/
theorem projector_annihilated (g : AddMonoid.End A) (hp : P g = 0) (i : Fin 3) :
    factor g i * projectorN g i = 0 := by
  have hh : factor g i * projectorN g i = ![-2,-2*g^2+g+4,2*g^2+g-4] i * P g := by
    fin_cases i <;> dsimp [factor, projectorN, F, G, H, P] <;> noncomm_ring <;> norm_num
  rw [hh, hp, mul_zero]

/-- Off-diagonal projection numerators kill the other primary kernels. -/
theorem projector_kills (g : AddMonoid.End A) (i j : Fin 3) (hij : i ≠ j)
    (x : A) (hx : factor g j x = 0) : projectorN g i x = 0 := by
  have he : ∃ R : AddMonoid.End A, projectorN g i = R * factor g j := by
    fin_cases i <;> fin_cases j <;> try contradiction
    · exact ⟨-2*H g, by dsimp [projectorN, factor, G, H]; noncomm_ring⟩
    · exact ⟨-2*G g, by dsimp [projectorN, factor]⟩
    · exact ⟨H g*(-2*g^2+g+4), by dsimp [projectorN, factor, F, H]; noncomm_ring⟩
    · exact ⟨F g*(-2*g^2+g+4), by dsimp [projectorN, factor, H]; noncomm_ring⟩
    · exact ⟨G g*(2*g^2+g-4), by dsimp [projectorN, factor, F, G]; noncomm_ring⟩
    · exact ⟨F g*(2*g^2+g-4), by dsimp [projectorN, factor, G]; noncomm_ring⟩
  obtain ⟨R,he⟩ := he
  rw [he, end_mul_apply, hx, map_zero]

theorem projector_recovers (g : AddMonoid.End A) (i : Fin 3) (x : A)
    (hx : factor g i x = 0) : projectorN g i x = (10 : ℕ) • x := by
  have hh := congrArg (fun f : AddMonoid.End A => f x) (projectors_sum g)
  change projectorN g 0 x + projectorN g 1 x + projectorN g 2 x = (10 : ℕ) • x at hh
  fin_cases i
  · rw [projector_kills g 1 0 (by decide) x hx,
      projector_kills g 2 0 (by decide) x hx, add_zero, add_zero] at hh
    exact hh
  · rw [projector_kills g 0 1 (by decide) x hx,
      projector_kills g 2 1 (by decide) x hx, zero_add, add_zero] at hh
    exact hh
  · rw [projector_kills g 0 2 (by decide) x hx,
      projector_kills g 1 2 (by decide) x hx, zero_add, zero_add] at hh
    exact hh

/-- Every element splits uniquely into three factor kernels. This is the
module Chinese remainder decomposition, with explicit projection formulas. -/
theorem unique_splitting (g : AddMonoid.End A) (hp : P g = 0)
    (hn : (Nat.card A).Coprime 10) (a : A) :
    ∃! x : Fin 3 → A, (∀ i, factor g i (x i) = 0) ∧ x 0+x 1+x 2=a := by
  have hb : Function.Bijective (fun x : A => (10 : ℕ) • x) := hn.nsmul_right_bijective
  choose x hx using (fun i : Fin 3 => hb.surjective (projectorN g i a))
  have hx' (i) : (10 : ℕ) • x i = projectorN g i a := hx i
  have hk (i) : factor g i (x i) = 0 := by
    apply hb.injective
    change (10 : ℕ) • factor g i (x i) = (10 : ℕ) • (0 : A)
    rw [← map_nsmul, hx']
    have hh := congrArg (fun f : AddMonoid.End A => f a) (projector_annihilated g hp i)
    simpa only [end_mul_apply, zero_nsmul, nsmul_zero] using hh
  have hs : x 0+x 1+x 2=a := by
    apply hb.injective
    change (10 : ℕ) • (x 0+x 1+x 2) = (10 : ℕ) • a
    rw [nsmul_add, nsmul_add, hx', hx', hx']
    exact congrArg (fun f : AddMonoid.End A => f a) (projectors_sum g)
  refine ⟨x,⟨hk,hs⟩,?_⟩
  intro y hy
  funext i
  apply hb.injective
  change (10 : ℕ) • y i = (10 : ℕ) • x i
  rw [hx', ← hy.2, map_add, map_add]
  fin_cases i
  · change (10 : ℕ) • y 0 = projectorN g 0 (y 0)+projectorN g 0 (y 1)+projectorN g 0 (y 2)
    rw [projector_recovers g 0 _ (hy.1 0), projector_kills g 0 1 (by decide) _ (hy.1 1),
      projector_kills g 0 2 (by decide) _ (hy.1 2), add_zero, add_zero]
  · change (10 : ℕ) • y 1 = projectorN g 1 (y 0)+projectorN g 1 (y 1)+projectorN g 1 (y 2)
    rw [projector_recovers g 1 _ (hy.1 1), projector_kills g 1 0 (by decide) _ (hy.1 0),
      projector_kills g 1 2 (by decide) _ (hy.1 2), zero_add, add_zero]
  · change (10 : ℕ) • y 2 = projectorN g 2 (y 0)+projectorN g 2 (y 1)+projectorN g 2 (y 2)
    rw [projector_recovers g 2 _ (hy.1 2), projector_kills g 2 0 (by decide) _ (hy.1 0),
      projector_kills g 2 1 (by decide) _ (hy.1 1), zero_add, zero_add]

/-- Each primary kernel is preserved by the coefficient operator. -/
theorem kernel_invariant (g : AddMonoid.End A) (i : Fin 3) (x : A)
    (hx : factor g i x = 0) : factor g i (g x) = 0 := by
  have he : factor g i * g = g * factor g i := by
    fin_cases i <;> dsimp [factor, F, G, H] <;> noncomm_ring
  have hh := congrArg (fun f : AddMonoid.End A => f x) he
  change factor g i (g x) = g (factor g i x) at hh
  rw [hh, hx, map_zero]

/-- The first kernel has the Gaussian coefficient B²=-1. -/
theorem gaussian_kernel (g : AddMonoid.End A) (x : A) (hx : F g x = 0) :
    g (g x) = -x ∧ (-(g^3) : AddMonoid.End A) x = g x := by
  change g (g x)+x=0 at hx
  have he : g (g x) = -x := eq_neg_of_add_eq_zero_left hx
  refine ⟨he,?_⟩
  change -g (g (g x)) = g x
  rw [he, map_neg, neg_neg]

/-- The third kernel has the idempotent E63 coefficient A=1-B. -/
theorem idempotent_kernel (g : AddMonoid.End A) (x : A) (hx : H g x = 0) :
    (-(g^3) : AddMonoid.End A) x = x-g x := by
  change g (g (g x))-g x+x=0 at hx
  change -g (g (g x)) = x-g x
  calc
    -g (g (g x)) = x-g x-(g (g (g x))-g x+x) := by abel
    _ = x-g x := by rw [hx, sub_zero]

/-- The second kernel has A=-1-B, the negative idempotent-E63 family. -/
theorem negative_idempotent_kernel (g : AddMonoid.End A) (x : A) (hx : G g x = 0) :
    (-(g^3) : AddMonoid.End A) x = -x-g x := by
  change g (g (g x))-g x-x=0 at hx
  change -g (g (g x)) = -x-g x
  calc
    -g (g (g x)) = -x-g x-(g (g (g x))-g x-x) := by abel
    _ = -x-g x := by rw [hx, sub_zero]

/-- Translation by an idempotent removes the affine constant. -/
theorem translation_hom (f g : AddMonoid.End A) (c e : A)
    (he : op f g c e e = e) (x y : A) :
    op f g 0 x y+e = op f g c (x+e) (y+e) := by
  change f e+g e+c=e at he
  simp only [op, map_add, add_zero]
  calc
    f x+g y+e = f x+g y+(f e+g e+c) := by rw [he]
    _ = f x+f e+(g y+g e)+c := by abel

spectrum_assert gaussian_kernel complete
spectrum_assert idempotent_kernel complete
spectrum_assert negative_idempotent_kernel complete
spectrum_assert translation_hom complete
spectrum_assert unique_splitting complete
end Spectrum.E667.AffineStructure

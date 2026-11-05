import equational_theories.Parastrophes.AffineIdentityCertificate

/-! Symbolic identity checks for affine operations whose coefficients depend on
finitely many parts of the carrier. Only the part assignments are enumerated. -/
namespace Parastrophes.PartitionedAffineIdentityCertificate
open Law FreeMagma AffineIdentityCertificate

structure Operation (B R : Type) where
  colour : B → B → B
  left : B → B → R
  right : B → B → R
  offset : B → B → R

@[implicit_reducible] def magma {B R : Type} [CommRing R] (f : Operation B R) : Magma (B × R) :=
  ⟨fun x y => (f.colour x.1 y.1, f.left x.1 y.1*x.2 + f.right x.1 y.1*y.2 + f.offset x.1 y.1)⟩

@[simp] theorem magma_op {B R : Type} [CommRing R] (f : Operation B R) (x y : B × R) :
    (magma f).op x y =
      (f.colour x.1 y.1, f.left x.1 y.1*x.2 + f.right x.1 y.1*y.2 + f.offset x.1 y.1) := rfl

def coefficients {B R : Type} [CommRing R] (f : Operation B R) (colours : Fin 3 → B) :
    FreeMagma (Fin 3) → B × Coefficients R
  | .Leaf i => (colours i, if i = 0 then ⟨1,0,0,0⟩ else if i = 1 then ⟨0,1,0,0⟩ else ⟨0,0,1,0⟩)
  | .Fork a b =>
    let u := coefficients f colours a
    let v := coefficients f colours b
    let p := f.left u.1 v.1
    let q := f.right u.1 v.1
    (f.colour u.1 v.1, ⟨p*u.2.x+q*v.2.x, p*u.2.y+q*v.2.y, p*u.2.z+q*v.2.z,
      p*u.2.constant+q*v.2.constant+f.offset u.1 v.1⟩)

theorem eval_eq_value {B R : Type} [CommRing R] (f : Operation B R)
    (t : FreeMagma (Fin 3)) (c : Fin 3 → B) (v : Fin 3 → R) :
    @evalInMagma _ _ (magma f) (fun i => (c i,v i)) t =
      ((coefficients f c t).1, value (coefficients f c t).2 v) := by
  induction t with
  | Leaf i => fin_cases i <;> simp [evalInMagma, coefficients, value]
  | Fork a b ha hb =>
    change (magma f).op (@evalInMagma _ _ (magma f) _ a)
      (@evalInMagma _ _ (magma f) _ b) = _
    rw [ha, hb]
    apply Prod.ext
    · rfl
    · simp only [magma_op, coefficients, value]
      ring

/-- Eight assignments of colours suffice when there are two parts. The four
coefficient equalities prove the identity for all choices of the ring entries. -/
theorem satisfies_of_coefficients {B R : Type} [CommRing R] (f : Operation B R)
    (t : FreeMagma (Fin 3))
    (h : ∀ c : Fin 3 → B, coefficients f c t = (c 0, ⟨1,0,0,0⟩)) :
    @satisfies _ (B × R) (magma f) (identity t) := by
  letI : Magma (B × R) := magma f
  intro v
  change v 0 = @evalInMagma _ _ (magma f) v (fmapFreeMagma Fin.val t)
  rw [← evalInMagma_comp]
  have he := eval_eq_value f t (fun i => (v i.val).1) (fun i => (v i.val).2)
  change v 0 = @evalInMagma _ _ (magma f) (fun i => ((v i.val).1,(v i.val).2)) t
  rw [he, h]
  simp [value]

end Parastrophes.PartitionedAffineIdentityCertificate

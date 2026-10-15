import equational_theories.Definability.ComposedDiagonalSwaps

/-! The one-generated submagmas of E4439 and E4476 have at most three
elements: x, its square q, and a common value c for all remaining products.
Their mixed-cube identities make the two-swap E1426 companion immediate. -/
open Law Law.MagmaLaw DiagonalOutputSwap
set_option maxHeartbeats 500000
namespace CollapsedUnaryProducts

def Table {G : Type} (M : Magma G) (x : G) : Prop :=
  let q := M.op x x
  let c := M.op q q
  M.op x q = c ∧ M.op q x = c ∧ M.op x c = c ∧ M.op c x = c ∧
    M.op q c = c ∧ M.op c q = c ∧ M.op c c = c

/-- Product rows depend only on the square of their left argument. Comparing
these rows forces both mixed cubes to equal the square of the square. -/
theorem table4439 {G : Type} (M : Magma G) (h : @Equation4439 G M) (x : G) : Table M x := by
  let q := M.op x x
  let c := M.op q q
  let t := M.op q x
  have rows (a b z : G) : M.op (M.op a b) z = M.op (M.op a a) z :=
    (h a z b).symm.trans (h a z a)
  have comm : M.op x q = t := h x x x
  have xt : M.op x t = c := h x q x
  have rt (z : G) : M.op t z = M.op c z := rows q x z
  have rc (z : G) : M.op c z = M.op q z := by
    have hh := rows x t z
    change M.op (M.op x t) z = M.op q z at hh
    rwa [xt] at hh
  have tx : M.op t x = t := (rt x).trans (rc x)
  have qt : M.op q t = t := by
    have hh := h q x x
    change M.op q (M.op x q) = M.op t x at hh
    rwa [comm,tx] at hh
  have xt' : M.op x t = t := by
    have hh := h x t x
    change M.op x (M.op t x) = M.op q t at hh
    rwa [tx,qt] at hh
  have tc : t = c := xt'.symm.trans xt
  have qc : M.op q c = c := by simpa only [tc] using qt
  change M.op x q = c ∧ M.op q x = c ∧ M.op x c = c ∧ M.op c x = c ∧
    M.op q c = c ∧ M.op c q = c ∧ M.op c c = c
  exact ⟨comm.trans tc, tc, by simpa only [tc] using xt,
    by simpa only [tc] using tx, qc, rc q, (rc c).trans qc⟩

theorem table4476 {G : Type} (M : Magma G) (h : @Equation4476 G M) (x : G) : Table M x := by
  unfold Table
  have seed0 := h x x x
  have seed1 := h x x (M.op x x)
  have seed3 := h x (M.op x x) x
  have seed4 := h x (M.op x x) (M.op x x)
  have seed6 := h x (M.op (M.op x x) (M.op x x)) x
  have seed7 := h x (M.op (M.op x x) (M.op x x)) (M.op x x)
  have seed9 := h (M.op x x) x x
  have seed12 := h (M.op x x) (M.op x x) x
  clear h
  grind

end CollapsedUnaryProducts

namespace CollapsedUnaryProducts

/-- Two equal mixed cubes suffice for the two-swap construction. -/
theorem target1426 {G : Type} (M : Magma G) (o : Bool)
    (hr : ∀ x, M.op x (M.op x x) = M.op (M.op x x) (M.op x x))
    (hl : ∀ x, M.op (M.op x x) x = M.op (M.op x x) (M.op x x)) :
    @Equation1426 G ((forward 1 2 false).magma ((forward 0 3 o).magma M)) := by
  classical
  let N := (forward 1 2 false).magma ((forward 0 3 o).magma M)
  have right (x : G) : N.op x (M.op x x) = x := by
    by_cases h : M.op x x = x
    · simp [N, h]
    · cases o <;> simp [N, forward_apply, value, Ne.symm h, hr, hl]
  have left (x : G) : N.op (M.op x x) x = x := by
    by_cases h : M.op x x = x
    · simp [N, h]
    · cases o <;> simp [N, forward_apply, value, h, hr, hl]
  intro x
  change x = N.op (N.op x x) (N.op x (N.op x x))
  have hs : N.op x x = M.op x x := by simp [N]
  rw [hs, right, left]

theorem Equation1426_structuralFrom_Equation4439_unaryProducts :
    Law1426.StructuralFrom Law4439 :=
  structuralFrom_twoDiagonalSwaps 0 3 1 2 false fun {G} M hM =>
    (@Law1426.models_iff G ((forward 1 2 false).magma ((forward 0 3 false).magma M))).mpr (target1426 M false
      (fun x => (table4439 M ((@Law4439.models_iff G M).mp hM) x).1)
      (fun x => (table4439 M ((@Law4439.models_iff G M).mp hM) x).2.1))

theorem Equation1426_structuralFrom_Equation4476_unaryProducts :
    Law1426.StructuralFrom Law4476 :=
  structuralFrom_twoDiagonalSwaps 0 3 1 2 true fun {G} M hM =>
    (@Law1426.models_iff G ((forward 1 2 false).magma ((forward 0 3 true).magma M))).mpr (target1426 M true
      (fun x => (table4476 M ((@Law4476.models_iff G M).mp hM) x).1)
      (fun x => (table4476 M ((@Law4476.models_iff G M).mp hM) x).2.1))
end CollapsedUnaryProducts

/-- info: 'CollapsedUnaryProducts.Equation1426_structuralFrom_Equation4439_unaryProducts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CollapsedUnaryProducts.Equation1426_structuralFrom_Equation4439_unaryProducts
/-- info: 'CollapsedUnaryProducts.Equation1426_structuralFrom_Equation4476_unaryProducts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CollapsedUnaryProducts.Equation1426_structuralFrom_Equation4476_unaryProducts

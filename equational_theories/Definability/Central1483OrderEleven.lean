import equational_theories.Spectrum.Equation1483.OrderEleven.Certificates
import equational_theories.Spectrum.Basic
import equational_theories.Spectrum.Status
import equational_theories.Equations.All

/-!
# E1483 has no model of order eleven

The proof fixes a minimum-rank row, normalizes its image, and sorts the column
image before the remaining points. Translation regularity makes the row map
injective on the column image. Naming the first new row-image value `2` removes
another symmetry. Sixteen compact certificates cover every remaining case.

All certificates are distributed (10.9 MB total). Lean reconstructs their RUP
hints and checks the resulting LRAT proofs against the Lean-defined formulas.
See `docs/definability_1483_order_eleven.md` for the mathematics and trust boundary.
-/
namespace Magma.Central1483

theorem no_operation_eleven (f : Fin 11 → Fin 11 → Fin 11)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) : False :=
  Spectrum.E1483.OrderEleven.no_operation f h

spectrum_assert no_operation_eleven complete
end Magma.Central1483

namespace Spectrum

theorem not_order_1483_11 : ¬ Law1483.HasModel 11 := by
  rintro ⟨M, hM⟩
  have h := (@Law1483.models_iff (Fin 11) M).mp hM
  exact Magma.Central1483.no_operation_eleven M.op (fun x y z => (h x y z).symm)

spectrum_assert not_order_1483_11 complete
end Spectrum

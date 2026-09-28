import equational_theories.Spectrum.Equation1083.Exclusion5
import equational_theories.Spectrum.Equation1083.Exclusion6

/-!
E1083 has no model of order five or six. The proof covers every multiplication
table, using the verified finite-table encoding and saved LRAT certificates.
Rebuilds replay these certificates with `bv_check`; no SAT search is required.
The registered native checks are audited transitively by `spectrum_assert`.
-/

spectrum_assert Spectrum.not_order_1083_5 complete
spectrum_assert Spectrum.not_order_1083_6 complete

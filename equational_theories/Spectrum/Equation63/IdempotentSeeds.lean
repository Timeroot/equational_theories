import equational_theories.Spectrum.Equation63.IdempotentConstructions

/-! Idempotent E63 seeds at orders 27 and 32. The cubic construction is algebraic
over an arbitrary commutative ring. The order-32 seed is reconstructed from
Bennett (1989), Figure 1 and Lemma 5.13, by
`scripts/spectrum_63_idempotent_seeds.py`; the Lean kernel checks its table. -/
namespace Spectrum.E63
open Classical

/-- The affine operation `x - B x + B y` for the companion matrix
`B(x₀,x₁,x₂) = (-x₂,x₀+x₂,x₁)`. Its relation `B³-B+I=0` gives E63. -/
def cubicOp {R : Type*} [CommRing R] (x y : R × R × R) : R × R × R :=
  (x.1 + x.2.2 - y.2.2,
    x.2.1 - x.1 - x.2.2 + y.1 + y.2.2,
    x.2.2 - x.2.1 + y.2.1)

theorem cubic_law {R : Type*} [CommRing R] : Lawful (@cubicOp R _) := by
  intro x y
  apply Prod.ext
  · simp only [cubicOp]
    ring
  · apply Prod.ext <;> simp only [cubicOp] <;> ring

theorem cubic_idem {R : Type*} [CommRing R] : Idem (@cubicOp R _) := by
  intro x
  apply Prod.ext
  · simp only [cubicOp]
    ring
  · apply Prod.ext <;> simp only [cubicOp] <;> ring

/-- Every cube is the order of an idempotent E63 model. -/
theorem cubic_idempotent (n : ℕ) [NeZero n] : Model (Fin (n^3)) true := by
  have h : Model (ZMod n × ZMod n × ZMod n) true :=
    ⟨cubicOp, cubic_law, fun _ => cubic_idem⟩
  exact h.relabel (Fintype.equivFinOfCardEq (by simp [pow_succ, Nat.mul_assoc]))

theorem idem27 : Model (Fin 27) true := cubic_idempotent 3

set_option maxRecDepth 65536 in
private def packedIdem32 : Nat := 0xff5ed08803ceb1b4a90be798e298878ca13ada97e798e00c22c6f3a42d2aff5ed21ca684e32a5eb66bfbf18041de3595a149733dc390c59c251bd2d5733dc10460d6778525686bfbf314e494670b56f48ca13de569efb9fada9729887c690a088036b98f84e32c690ae7fbea5eb621ca6de56900c2263dae9c2514af3bff3ddbd2d5390c552358180417b1cd9467052358f77fcb56f4314e44af3b10460735ec4a90b6b98fbd4e5ceb1b8ca1308803a5886efb9f42d2a63daea5886c6f3a84e3200c22bd4e5e7fbe5a1497b1cd29eb7de3599c25118041312d4ff3dd52568735ec312d4d6778946701046029eb7f77fcceb1b298874a90b9c461ada976b98fefb9f84802c6f3a21ca642d2a84802a5eb663daee7fbe9c461de359390c55a14908e33bd2d57b1cdff3dd10250d6778314e45256810250b56f4735ecf77fc08e3363b9eada9708803298877b7fd8ca134a90bceb1b7b7fda5eb600c2221ca663b9e84e3242d2ac6f3af71ccbd2d518041390c5efdaf9c2515a149de359efdafb56f410460314e4f71cc9467052568d6778ada9742b1a8ca13efb9f088035a7796b98f29887a5eb65a77984e32e7fbe00c2242b1a63dae21ca6bd2d5d61489c251ff3dd18041ced2b7b1cd390c5b56f4ced2b94670f77fc10460d6148735ec314e4088038ca1321a966b98fceb1befb9f396f54a90b00c2284e32396f563daec6f3ae7fbe21a9642d2a180419c251b50c47b1cdde359ff3ddadca75a1491046094670adca7735ecd6778f77fcb50c45256829887efb9f6b98f00a124a90bada97ceb1b1867121ca6e7fbe63dae1867142d2aa5eb6c6f3a00a12390c5ff3dd7b1cd940405a149bd2d5de3598cc23314e4f77fc735ec8cc2352568b56f4d677894040

/-- Packed row-major into five-bit entries, least significant entry first. -/
def idemTable32 (x y : Fin 32) : Fin 32 :=
  ⟨(packedIdem32 >>> ((x.val*32+y.val)*5)) % 32, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem idem_law32 : Lawful idemTable32 := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem idem_diag32 : Idem idemTable32 := by decide +kernel

theorem idem32 : Model (Fin 32) true := ⟨idemTable32, idem_law32, fun _ => idem_diag32⟩

end Spectrum.E63

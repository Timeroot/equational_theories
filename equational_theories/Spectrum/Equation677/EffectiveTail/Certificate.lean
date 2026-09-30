import equational_theories.Spectrum.Equation677.EffectiveTail.Data

/-! Kernel replay of the three-stage certificate for the E677 tail at 164475.
No numerical tail hypothesis or external solver result is assumed. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace Spectrum.E677.EffectiveTail.OrderBitmap.Cert
open Law Law.MagmaLaw
/-- The orders recorded before any instruction runs: `0`, `1`, the nine-element `GF9`, the
`21`-element `Plane21`, the idempotent translation-invariant models `T79` and `T127`, and the
fourth powers `j ^ 4` for `j ≤ 20`. -/
def seedList : List Nat := [0, 1, 9, 21, 79, 127] ++ (List.range 21).map (· ^ 4)

/-- The bitmap of `seedList`. -/
def seedBits : Nat := seedList.foldr (fun n B => B ||| 1 <<< n) 0

theorem hasModel_of_mem_seedList {n : Nat} (h : n ∈ seedList) : Law677.HasModel n := by
  unfold seedList at h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | h
    · exact Law677.hasModel_zero
    · exact Law677.hasModel_one
    · exact model9
    · exact model21
    · exact idem79.hasModel
    · exact model127
    · cases h
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
    exact hasModel_pow_four j

theorem sound_seedBits : Sound seedBits := sound_foldr fun _ h => hasModel_of_mem_seedList h

/-- The bitmap of the orders below `171623` that the certificate records. -/
noncomputable def certH : Nat := ofWords hWords 0

set_option Elab.async false

theorem stageA0_ok : blocksOK seedBits certH 0 stageA0 = true := by
  decide +kernel

theorem stageA0_end : blocksEnd 0 stageA0 = 8192 := by rfl

theorem stageA1_ok : blocksOK seedBits certH 8192 stageA1 = true := by
  decide +kernel

theorem stageA1_end : blocksEnd 8192 stageA1 = 16384 := by rfl

theorem stageA2_ok : blocksOK seedBits certH 16384 stageA2 = true := by
  decide +kernel

theorem stageA2_end : blocksEnd 16384 stageA2 = 32768 := by rfl

theorem stageA3_ok : blocksOK seedBits certH 32768 stageA3 = true := by
  decide +kernel

theorem stageA3_end : blocksEnd 32768 stageA3 = 65536 := by rfl

theorem stageA4_ok : blocksOK seedBits certH 65536 stageA4 = true := by
  decide +kernel

theorem stageA4_end : blocksEnd 65536 stageA4 = 163840 := by rfl

theorem stageA5_ok : blocksOK seedBits certH 163840 stageA5 = true := by
  decide +kernel

theorem stageA5_end : blocksEnd 163840 stageA5 = 171623 := by rfl

theorem sound_certH_mod : Sound (certH % 2 ^ 171623) := by
  have h0 : Sound (certH % 2 ^ 0) := by
    rw [Nat.pow_zero, Nat.mod_one]
    intro n hn
    simp at hn
  have h1 := Sound.of_blocksOK sound_seedBits 0 stageA0 h0 stageA0_ok
  rw [stageA0_end] at h1
  have h2 := Sound.of_blocksOK sound_seedBits 8192 stageA1 h1 stageA1_ok
  rw [stageA1_end] at h2
  have h3 := Sound.of_blocksOK sound_seedBits 16384 stageA2 h2 stageA2_ok
  rw [stageA2_end] at h3
  have h4 := Sound.of_blocksOK sound_seedBits 32768 stageA3 h3 stageA3_ok
  rw [stageA3_end] at h4
  have h5 := Sound.of_blocksOK sound_seedBits 65536 stageA4 h4 stageA4_ok
  rw [stageA4_end] at h5
  have h6 := Sound.of_blocksOK sound_seedBits 163840 stageA5 h5 stageA5_ok
  rw [stageA5_end] at h6
  exact h6

theorem certH_lt : certH < 2 ^ 171623 := by
  decide +kernel

/-- **Every order recorded in `certH` carries a model.** -/
theorem sound_certH : Sound certH := by
  have h := sound_certH_mod
  rwa [Nat.mod_eq_of_lt certH_lt] at h

theorem certH_interval : intervalOK certH 164475 7148 = true := by
  decide +kernel

theorem stageB0_ok : coversOK certH 171623 stageB0 = true := by
  decide +kernel

theorem stageB0_end : blocksEnd 171623 stageB0 = 302695 := by rfl

theorem stageB1_ok : coversOK certH 302695 stageB1 = true := by
  decide +kernel

theorem stageB1_end : blocksEnd 302695 stageB1 = 433767 := by rfl

theorem stageB2_ok : coversOK certH 433767 stageB2 = true := by
  decide +kernel

theorem stageB2_end : blocksEnd 433767 stageB2 = 564839 := by rfl

theorem stageB3_ok : coversOK certH 564839 stageB3 = true := by
  decide +kernel

theorem stageB3_end : blocksEnd 564839 stageB3 = 826983 := by rfl

theorem stageB4_ok : coversOK certH 826983 stageB4 = true := by
  decide +kernel

theorem stageB4_end : blocksEnd 826983 stageB4 = 1220199 := by rfl

theorem stageB5_ok : coversOK certH 1220199 stageB5 = true := by
  decide +kernel

theorem stageB5_end : blocksEnd 1220199 stageB5 = 1875559 := by rfl

theorem stageB6_ok : coversOK certH 1875559 stageB6 = true := by
  decide +kernel

theorem stageB6_end : blocksEnd 1875559 stageB6 = 3317351 := by rfl

theorem stageB7_ok : coversOK certH 3317351 stageB7 = true := by
  decide +kernel

theorem stageB7_end : blocksEnd 3317351 stageB7 = 12361319 := by rfl

theorem stageB8_ok : coversOK certH 12361319 stageB8 = true := by
  decide +kernel

theorem stageB8_end : blocksEnd 12361319 stageB8 = 13558001 := by rfl

/-- **Every size in `[164475, 13558000]` carries a model.** -/
theorem upto_certificate : Upto 164475 13558000 := by
  intro n h1 h2
  by_cases hY : n ≤ 171622
  · exact sound_certH n (testBit_of_intervalOK certH_interval h1 (by omega))
  by_cases hB0 : n < 302695
  · exact hasModel_of_coversOK sound_certH _ _ stageB0_ok n (by omega)
      (by rw [stageB0_end]; omega)
  by_cases hB1 : n < 433767
  · exact hasModel_of_coversOK sound_certH _ _ stageB1_ok n (by omega)
      (by rw [stageB1_end]; omega)
  by_cases hB2 : n < 564839
  · exact hasModel_of_coversOK sound_certH _ _ stageB2_ok n (by omega)
      (by rw [stageB2_end]; omega)
  by_cases hB3 : n < 826983
  · exact hasModel_of_coversOK sound_certH _ _ stageB3_ok n (by omega)
      (by rw [stageB3_end]; omega)
  by_cases hB4 : n < 1220199
  · exact hasModel_of_coversOK sound_certH _ _ stageB4_ok n (by omega)
      (by rw [stageB4_end]; omega)
  by_cases hB5 : n < 1875559
  · exact hasModel_of_coversOK sound_certH _ _ stageB5_ok n (by omega)
      (by rw [stageB5_end]; omega)
  by_cases hB6 : n < 3317351
  · exact hasModel_of_coversOK sound_certH _ _ stageB6_ok n (by omega)
      (by rw [stageB6_end]; omega)
  by_cases hB7 : n < 12361319
  · exact hasModel_of_coversOK sound_certH _ _ stageB7_ok n (by omega)
      (by rw [stageB7_end]; omega)
  exact hasModel_of_coversOK sound_certH _ _ stageB8_ok n (by omega)
    (by rw [stageB8_end]; omega)

theorem chain_certificate : 80 * (79 * (P79 + 2) + 164475) ≤ chain 164475 5263 13558000 := by
  decide +kernel

/-- **Every size from `164475` on carries a model.** -/
theorem hasModel_of_ge {n : Nat} (hn : 164475 ≤ n) : Law677.HasModel n :=
  (upto_certificate.chain 5263).tail chain_certificate n hn

end Spectrum.E677.EffectiveTail.OrderBitmap.Cert

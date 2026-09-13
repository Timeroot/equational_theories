import equational_theories.Spectrum.Finite
import equational_theories.Equations.All

/-! Additional exhaustive order-three certificates for the note's initial segments. -/

set_option maxHeartbeats 2000000
namespace Spectrum.NoteExclusion

theorem not_three_467 : ¬ Law467.HasModel 3 := by
  rintro ⟨M, hM⟩
  have h := (@Law467.models_iff (Fin 3) M).mp hM
  have split (x y : Fin 3) : M.op x y = 0 ∨ M.op x y = 1 ∨ M.op x y = 2 := by omega
  rcases split 0 0 with h0 | h0 | h0
  · rcases split 1 1 with h4 | h4 | h4
    · rcases split 1 0 with h3 | h3 | h3
      · exact (by decide : (1 : Fin 3) ≠ 0)
          (by simpa only [h0, h4, h3] using h 1 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h4, h3] using h 0 1)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h4, h3] using h 0 1)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 2 0 with h6 | h6 | h6
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h6] using h 2 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h6] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h6] using h 0 2)
      · rcases split 2 1 with h7 | h7 | h7
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h7] using h 1 2)
        · exact (by decide : (2 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h7] using h 2 1)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h7] using h 1 2)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 1)
        · rcases split 0 2 with h2 | h2 | h2
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h2, h3] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h2, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h2, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h2] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h2] using h 0 2)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 2 0 with h6 | h6 | h6
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h6] using h 2 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h6] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h6] using h 0 2)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h3] using h 1 0)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h3] using h 1 1)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h3] using h 1 0)
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h7] using h 1 2)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h5, h7] using h 2 2)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h7] using h 1 2)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 1 1)
      · rcases split 1 2 with h5 | h5 | h5
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h5] using h 2 1)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 1 2)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 1 1)
  · rcases split 1 1 with h4 | h4 | h4
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 0)
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 0)
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h3, h5] using h 1 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h3, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h3, h5] using h 0 1)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 0)
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 0)
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h3, h2] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h3, h2] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h3, h2] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h2] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h2] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h2] using h 0 0)
    · rcases split 0 1 with h1 | h1 | h1
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h4, h1] using h 0 1)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h4, h1] using h 0 0)
      · exact (by decide : (1 : Fin 3) ≠ 2)
          (by simpa only [h0, h4, h1] using h 1 0)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h6] using h 2 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h6] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h6] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h2] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h2] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h2] using h 0 0)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h5, h7, h6] using h 1 2)
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h5, h7, h6] using h 2 2)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h5, h7, h6] using h 1 2)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h5, h7] using h 2 2)
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h7] using h 2 1)
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h7] using h 1 2)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h5, h7] using h 2 2)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h7] using h 1 2)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 1 1)
      · rcases split 1 2 with h5 | h5 | h5
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h5] using h 2 1)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 1 2)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 1 1)
  · rcases split 2 2 with h8 | h8 | h8
    · rcases split 1 1 with h4 | h4 | h4
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h2, h6] using h 2 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h6] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h6] using h 0 2)
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h2, h6] using h 2 2)
          · rcases split 2 1 with h7 | h7 | h7
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h2, h6, h7] using h 2 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h2, h6, h7] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h2, h6, h7] using h 0 2)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h6] using h 2 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h2] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h2, h6] using h 2 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h6] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h6] using h 0 2)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h1] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h2] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h2, h6] using h 2 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h6] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h6] using h 0 2)
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h2, h6] using h 2 2)
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h2, h6, h1] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h2, h6, h1] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h2, h6, h1] using h 0 0)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h6] using h 2 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h2] using h 0 0)
    · rcases split 1 1 with h4 | h4 | h4
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h2, h3] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h3] using h 0 1)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h1] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h2] using h 0 0)
      · rcases split 2 1 with h7 | h7 | h7
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h8, h4, h7] using h 1 2)
        · exact (by decide : (2 : Fin 3) ≠ 1)
            (by simpa only [h0, h8, h4, h7] using h 2 1)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h7] using h 1 2)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h5, h7, h3] using h 1 0)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h5, h7, h3] using h 1 1)
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h8, h4, h5, h7, h3] using h 1 1)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h5, h7] using h 2 2)
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h5, h7] using h 2 1)
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h5, h7] using h 1 2)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h5, h7] using h 2 2)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h5, h7] using h 1 2)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h5] using h 1 1)
    · rcases split 0 2 with h2 | h2 | h2
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h8, h2] using h 0 2)
      · exact (by decide : (2 : Fin 3) ≠ 1)
          (by simpa only [h0, h8, h2] using h 2 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h8, h2] using h 0 0)

theorem not_three_670 : ¬ Law670.HasModel 3 := by
  rintro ⟨M, hM⟩
  have h := (@Law670.models_iff (Fin 3) M).mp hM
  have split (x y : Fin 3) : M.op x y = 0 ∨ M.op x y = 1 ∨ M.op x y = 2 := by omega
  rcases split 0 0 with h0 | h0 | h0
  · rcases split 0 1 with h1 | h1 | h1
    · rcases split 1 0 with h3 | h3 | h3
      · exact (by decide : (1 : Fin 3) ≠ 0)
          (by simpa only [h0, h1, h3] using h 1 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h1, h3] using h 0 1)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h1, h3] using h 0 1)
    · rcases split 1 1 with h4 | h4 | h4
      · rcases split 1 0 with h3 | h3 | h3
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h1, h4, h3] using h 1 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h4, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h4, h3] using h 0 1)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h1, h4] using h 0 1)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h4, h2, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h4, h2, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h4, h2, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h4, h2] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 2 2 with h8 | h8 | h8
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h1, h4, h2, h5, h8, h6] using h 1 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h1, h4, h2, h5, h8, h6] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h1, h4, h2, h5, h8, h6] using h 0 2)
            · rcases split 2 1 with h7 | h7 | h7
              · rcases split 1 0 with h3 | h3 | h3
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h1, h4, h2, h5, h8, h7, h3] using h 1 0)
                · exact (by decide : (1 : Fin 3) ≠ 2)
                    (by simpa only [h0, h1, h4, h2, h5, h8, h7, h3] using h 1 0)
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h1, h4, h2, h5, h8, h7, h3] using h 1 1)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h1, h4, h2, h5, h8, h7] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h1, h4, h2, h5, h8, h7] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h4, h2, h5, h8] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h4, h2, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h4, h2, h5] using h 0 1)
    · rcases split 2 1 with h7 | h7 | h7
      · rcases split 1 0 with h3 | h3 | h3
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h1, h7, h3] using h 1 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h7, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h7, h3] using h 0 1)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 0 2 with h2 | h2 | h2
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h7, h5, h2, h6] using h 2 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h1, h7, h5, h2, h6] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h7, h5, h2, h6] using h 0 2)
          · rcases split 1 1 with h4 | h4 | h4
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h1, h7, h5, h2, h4, h6] using h 1 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h1, h7, h5, h2, h4, h6] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h1, h7, h5, h2, h4, h6] using h 0 2)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h1, h7, h5, h2, h4] using h 2 1)
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h7, h5, h2, h4] using h 1 1)
          · rcases split 2 2 with h8 | h8 | h8
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h1, h7, h5, h2, h8, h6] using h 1 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h1, h7, h5, h2, h8, h6] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h1, h7, h5, h2, h8, h6] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h1, h7, h5, h2, h8] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h7, h5, h2, h8] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h7, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h7, h5] using h 0 1)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h7, h2, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h7, h2, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h7, h2, h3] using h 0 1)
        · rcases split 1 1 with h4 | h4 | h4
          · rcases split 1 2 with h5 | h5 | h5
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h1, h7, h2, h4, h5, h6] using h 1 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h1, h7, h2, h4, h5, h6] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h1, h7, h2, h4, h5, h6] using h 0 2)
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h7, h2, h4, h5] using h 1 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h7, h2, h4, h5] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h7, h2, h4] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h7, h2, h4] using h 0 1)
        · rcases split 2 2 with h8 | h8 | h8
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h7, h2, h8, h6] using h 2 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h1, h7, h2, h8, h6] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h7, h2, h8, h6] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h7, h2, h8] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h7, h2, h8] using h 0 2)
  · rcases split 1 0 with h3 | h3 | h3
    · rcases split 0 1 with h1 | h1 | h1
      · rcases split 1 1 with h4 | h4 | h4
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h3, h1, h4] using h 1 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h1, h4] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h1, h4] using h 0 1)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h1] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h3, h1] using h 0 0)
    · rcases split 0 1 with h1 | h1 | h1
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h1] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h1] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 1 1 with h4 | h4 | h4
            · rcases split 1 2 with h5 | h5 | h5
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h3, h1, h2, h7, h4, h5] using h 1 2)
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h3, h1, h2, h7, h4, h5] using h 1 1)
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h1, h2, h7, h4, h5] using h 1 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h3, h1, h2, h7, h4] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h1, h2, h7, h4] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h3, h1, h2, h7] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h3, h1, h2, h7] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h1, h2] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h1, h2] using h 0 0)
    · rcases split 0 2 with h2 | h2 | h2
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h2] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 1 with h4 | h4 | h4
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h3, h2, h1, h4, h5] using h 1 1)
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h3, h2, h1, h4, h5, h6] using h 1 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h3, h2, h1, h4, h5, h6] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h2, h1, h4, h5, h6] using h 0 2)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h2, h1, h4, h5] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h3, h2, h1, h4] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h2, h1, h4] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h2, h1] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h2, h1] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h3, h2] using h 0 0)
  · rcases split 2 0 with h6 | h6 | h6
    · rcases split 0 2 with h2 | h2 | h2
      · rcases split 2 2 with h8 | h8 | h8
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h6, h2, h8] using h 2 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h6, h2, h8] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h6, h2, h8] using h 0 2)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h6, h2] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h6, h2] using h 0 0)
    · rcases split 0 1 with h1 | h1 | h1
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h6, h1] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h6, h1] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 2 2 with h8 | h8 | h8
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h6, h1, h2, h7, h8] using h 2 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h6, h1, h2, h7, h8] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h6, h1, h2, h7, h8] using h 0 2)
          · rcases split 1 2 with h5 | h5 | h5
            · rcases split 1 0 with h3 | h3 | h3
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h6, h1, h2, h7, h5, h3] using h 1 0)
              · rcases split 1 1 with h4 | h4 | h4
                · exact (by decide : (1 : Fin 3) ≠ 2)
                    (by simpa only [h0, h6, h1, h2, h7, h5, h3, h4] using h 1 0)
                · exact (by decide : (1 : Fin 3) ≠ 2)
                    (by simpa only [h0, h6, h1, h2, h7, h5, h3, h4] using h 1 0)
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h6, h1, h2, h7, h5, h3, h4] using h 1 0)
              · rcases split 2 2 with h8 | h8 | h8
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h6, h1, h2, h7, h5, h3, h8] using h 1 2)
                · exact (by decide : (0 : Fin 3) ≠ 1)
                    (by simpa only [h0, h6, h1, h2, h7, h5, h3, h8] using h 0 2)
                · exact (by decide : (0 : Fin 3) ≠ 2)
                    (by simpa only [h0, h6, h1, h2, h7, h5, h3, h8] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h6, h1, h2, h7, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h6, h1, h2, h7, h5] using h 0 1)
          · rcases split 1 0 with h3 | h3 | h3
            · rcases split 2 2 with h8 | h8 | h8
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h6, h1, h2, h7, h3, h8] using h 2 1)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h6, h1, h2, h7, h3, h8] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h6, h1, h2, h7, h3, h8] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h6, h1, h2, h7, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h6, h1, h2, h7, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h6, h1, h2] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h6, h1, h2] using h 0 0)
    · rcases split 0 2 with h2 | h2 | h2
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h6, h2] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 2 2 with h8 | h8 | h8
            · rcases split 1 1 with h4 | h4 | h4
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h6, h2, h1, h5, h8, h4] using h 1 2)
              · rcases split 2 1 with h7 | h7 | h7
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h6, h2, h1, h5, h8, h4, h7] using h 1 2)
                · exact (by decide : (2 : Fin 3) ≠ 1)
                    (by simpa only [h0, h6, h2, h1, h5, h8, h4, h7] using h 2 1)
                · exact (by decide : (1 : Fin 3) ≠ 2)
                    (by simpa only [h0, h6, h2, h1, h5, h8, h4, h7] using h 1 2)
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h6, h2, h1, h5, h8, h4] using h 1 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h6, h2, h1, h5, h8] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h6, h2, h1, h5, h8] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h6, h2, h1, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h6, h2, h1, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h6, h2, h1] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h6, h2, h1] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h6, h2] using h 0 0)

theorem not_three_704 : ¬ Law704.HasModel 3 := by
  rintro ⟨M, hM⟩
  have h := (@Law704.models_iff (Fin 3) M).mp hM
  have split (x y : Fin 3) : M.op x y = 0 ∨ M.op x y = 1 ∨ M.op x y = 2 := by omega
  rcases split 0 0 with h0 | h0 | h0
  · rcases split 1 1 with h4 | h4 | h4
    · exact (by decide : (1 : Fin 3) ≠ 0)
        (by simpa only [h0, h4] using h 1 0)
    · rcases split 2 2 with h8 | h8 | h8
      · exact (by decide : (2 : Fin 3) ≠ 0)
          (by simpa only [h0, h4, h8] using h 2 0)
      · exact (by decide : (2 : Fin 3) ≠ 1)
          (by simpa only [h0, h4, h8] using h 2 1)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
          · rcases split 1 2 with h5 | h5 | h5
            · rcases split 0 2 with h2 | h2 | h2
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h1, h3, h5, h2] using h 1 0)
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h1, h3, h5, h2] using h 1 0)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h1, h3, h5, h2] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h3, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h3, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 1)
    · rcases split 2 2 with h8 | h8 | h8
      · exact (by decide : (2 : Fin 3) ≠ 0)
          (by simpa only [h0, h4, h8] using h 2 0)
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h7, h6] using h 1 0)
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h7, h6, h1] using h 1 0)
            · rcases split 1 2 with h5 | h5 | h5
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h7, h6, h1, h5] using h 2 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h7, h6, h1, h5] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h7, h6, h1, h5] using h 0 1)
            · rcases split 1 2 with h5 | h5 | h5
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h7, h6, h1, h5] using h 2 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h7, h6, h1, h5] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h7, h6, h1, h5] using h 0 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h6] using h 1 2)
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h7, h5] using h 1 1)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h7, h5] using h 2 2)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h5] using h 1 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h7, h5, h3] using h 1 1)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h7, h5, h3] using h 2 1)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h7, h5, h3] using h 1 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h5] using h 1 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h5] using h 1 1)
      · exact (by decide : (1 : Fin 3) ≠ 2)
          (by simpa only [h0, h4, h8] using h 1 2)
  · rcases split 1 1 with h4 | h4 | h4
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 0 1 with h1 | h1 | h1
        · exact (by decide : (2 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 2 0)
        · exact (by decide : (2 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 2 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h2] using h 1 0)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h2] using h 2 0)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h2] using h 1 0)
      · rcases split 1 0 with h3 | h3 | h3
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h3] using h 2 1)
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h3] using h 2 1)
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h5] using h 2 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h5] using h 0 1)
      · rcases split 1 0 with h3 | h3 | h3
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h1] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h3, h1, h2] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h3, h1, h2] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h1, h2] using h 0 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h2] using h 0 0)
          · rcases split 0 1 with h1 | h1 | h1
            · rcases split 1 2 with h5 | h5 | h5
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h3, h2, h1, h5] using h 1 1)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h3, h2, h1, h5] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h3, h2, h1, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h3, h2, h1] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h2, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h2] using h 0 0)
    · exact (by decide : (0 : Fin 3) ≠ 1)
        (by simpa only [h0, h4] using h 0 1)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h6] using h 1 2)
          · rcases split 2 1 with h7 | h7 | h7
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h5, h6, h7] using h 1 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h5, h6, h7] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h5, h6, h7] using h 0 2)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h6] using h 1 2)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 0 1)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h3] using h 2 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h5, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 0 1)
      · exact (by decide : (1 : Fin 3) ≠ 2)
          (by simpa only [h0, h4, h8] using h 1 2)
  · rcases split 2 2 with h8 | h8 | h8
    · rcases split 1 1 with h4 | h4 | h4
      · rcases split 0 2 with h2 | h2 | h2
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h2] using h 1 0)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h2, h1] using h 1 0)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h1] using h 2 0)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h1] using h 1 0)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h2] using h 1 0)
      · rcases split 2 0 with h6 | h6 | h6
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h6, h2] using h 2 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h1] using h 0 0)
          · rcases split 0 2 with h2 | h2 | h2
            · rcases split 2 1 with h7 | h7 | h7
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h8, h4, h6, h1, h2, h7] using h 2 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h8, h4, h6, h1, h2, h7] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h8, h4, h6, h1, h2, h7] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h6, h1, h2] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h6, h1, h2] using h 0 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h8, h4, h6, h2, h1] using h 2 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h6, h2, h1] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h6, h2, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
      · rcases split 2 0 with h6 | h6 | h6
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h8, h4, h6] using h 1 2)
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h6, h7] using h 1 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h7] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h7] using h 0 2)
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h8, h4, h6] using h 1 2)
    · rcases split 1 1 with h4 | h4 | h4
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h7, h3] using h 2 1)
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h7, h3] using h 2 1)
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h8, h4, h7, h3, h5] using h 2 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h7, h3, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h7, h3, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h8, h4, h7] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h8, h4, h7] using h 0 2)
      · exact (by decide : (2 : Fin 3) ≠ 1)
          (by simpa only [h0, h8, h4] using h 2 1)
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h7, h6] using h 1 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h7, h6] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h7, h6] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h8, h4, h7] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h8, h4, h7] using h 0 2)
    · exact (by decide : (0 : Fin 3) ≠ 2)
        (by simpa only [h0, h8] using h 0 2)

theorem not_three_1076 : ¬ Law1076.HasModel 3 := by
  rintro ⟨M, hM⟩
  have h := (@Law1076.models_iff (Fin 3) M).mp hM
  have split (x y : Fin 3) : M.op x y = 0 ∨ M.op x y = 1 ∨ M.op x y = 2 := by omega
  rcases split 0 0 with h0 | h0 | h0
  · rcases split 0 1 with h1 | h1 | h1
    · rcases split 1 0 with h3 | h3 | h3
      · exact (by decide : (1 : Fin 3) ≠ 0)
          (by simpa only [h0, h1, h3] using h 1 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h1, h3] using h 0 1)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h1, h3] using h 0 1)
    · rcases split 1 1 with h4 | h4 | h4
      · rcases split 1 0 with h3 | h3 | h3
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h1, h4, h3] using h 1 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h4, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h4, h3] using h 0 1)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h1, h4] using h 0 1)
      · rcases split 1 2 with h5 | h5 | h5
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h4, h5] using h 1 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h4, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h4, h5] using h 0 1)
    · rcases split 0 2 with h2 | h2 | h2
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h2, h5, h6] using h 2 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h2, h5, h6] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h2, h5, h6] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h2, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h2, h5] using h 0 1)
      · rcases split 1 1 with h4 | h4 | h4
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h2, h4, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h2, h4, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h2, h4, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h2, h4] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h2, h4, h5] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h2, h4, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h2, h4, h5] using h 0 1)
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h2, h7, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h2, h7, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h2, h7, h3] using h 0 1)
        · rcases split 1 1 with h4 | h4 | h4
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h2, h7, h4, h3] using h 1 0)
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h2, h7, h4, h3] using h 1 0)
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h2, h7, h4, h3] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h2, h7, h4] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h2, h7, h4] using h 0 1)
        · rcases split 2 2 with h8 | h8 | h8
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h2, h7, h8, h5] using h 2 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h1, h2, h7, h8, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h2, h7, h8, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h2, h7, h8] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h2, h7, h8] using h 0 2)
  · rcases split 0 1 with h1 | h1 | h1
    · rcases split 1 1 with h4 | h4 | h4
      · rcases split 1 0 with h3 | h3 | h3
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h1, h4, h3] using h 1 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h4, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h4, h3] using h 0 1)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h1, h4] using h 0 1)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h4, h5, h3] using h 1 0)
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h4, h5, h3, h6] using h 1 2)
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h4, h5, h3, h6] using h 1 0)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h4, h5, h3, h6] using h 1 2)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h4, h5, h3] using h 1 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h4, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h4, h5] using h 0 1)
    · rcases split 1 0 with h3 | h3 | h3
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h1, h3] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h1, h3] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 1 1 with h4 | h4 | h4
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h3, h2, h5, h4] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h1, h3, h2, h5, h4] using h 0 1)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h3, h2, h5, h4] using h 1 1)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h3, h2, h5] using h 1 0)
          · rcases split 2 2 with h8 | h8 | h8
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h1, h3, h2, h5, h8, h6] using h 1 2)
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h1, h3, h2, h5, h8, h6] using h 2 2)
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h1, h3, h2, h5, h8, h6] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h1, h3, h2, h5, h8] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h3, h2, h5, h8] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h3, h2] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h3, h2] using h 0 0)
    · rcases split 2 0 with h6 | h6 | h6
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h1, h6] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h1, h6] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h6, h2, h5] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h6, h2, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h6, h2, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h6, h2] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h6, h2] using h 0 0)
  · rcases split 0 2 with h2 | h2 | h2
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 2 0 with h6 | h6 | h6
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h2, h8, h6] using h 2 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h2, h8, h6] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h2, h8, h6] using h 0 2)
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h2, h8, h7, h6] using h 2 0)
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h2, h8, h7, h6] using h 2 0)
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h2, h8, h7, h6, h3] using h 1 0)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h2, h8, h7, h6, h3] using h 2 1)
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h2, h8, h7, h6, h3] using h 2 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h2, h8, h7] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h2, h8, h7] using h 0 2)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h2, h8] using h 0 2)
    · rcases split 1 0 with h3 | h3 | h3
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h2, h3] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h2, h3, h1, h7] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h2, h3, h1, h7] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h2, h3, h1, h7] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h2, h3, h1] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h2, h3, h1] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h2, h3] using h 0 0)
    · rcases split 2 0 with h6 | h6 | h6
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h2, h6] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h2, h6, h1, h7, h3] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h2, h6, h1, h7, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h2, h6, h1, h7, h3] using h 0 1)
          · rcases split 1 1 with h4 | h4 | h4
            · rcases split 1 0 with h3 | h3 | h3
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h2, h6, h1, h7, h4, h3] using h 1 0)
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h2, h6, h1, h7, h4, h3] using h 1 0)
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h2, h6, h1, h7, h4, h3] using h 1 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h2, h6, h1, h7, h4] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h2, h6, h1, h7, h4] using h 0 1)
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h2, h6, h1, h7] using h 2 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h2, h6, h1] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h2, h6, h1] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h2, h6] using h 0 0)

theorem not_three_1110 : ¬ Law1110.HasModel 3 := by
  rintro ⟨M, hM⟩
  have h := (@Law1110.models_iff (Fin 3) M).mp hM
  have split (x y : Fin 3) : M.op x y = 0 ∨ M.op x y = 1 ∨ M.op x y = 2 := by omega
  rcases split 0 0 with h0 | h0 | h0
  · rcases split 1 1 with h4 | h4 | h4
    · exact (by decide : (1 : Fin 3) ≠ 0)
        (by simpa only [h0, h4] using h 1 0)
    · rcases split 2 2 with h8 | h8 | h8
      · exact (by decide : (2 : Fin 3) ≠ 0)
          (by simpa only [h0, h4, h8] using h 2 0)
      · exact (by decide : (2 : Fin 3) ≠ 1)
          (by simpa only [h0, h4, h8] using h 2 1)
      · rcases split 1 0 with h3 | h3 | h3
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h1] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 1)
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h3, h1, h5] using h 2 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h3, h1, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h1, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h3] using h 0 1)
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h7] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h7] using h 0 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h7] using h 1 2)
    · rcases split 2 2 with h8 | h8 | h8
      · exact (by decide : (2 : Fin 3) ≠ 0)
          (by simpa only [h0, h4, h8] using h 2 0)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h6] using h 1 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h5, h6] using h 0 2)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h6] using h 1 2)
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h7] using h 1 2)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h5, h7] using h 2 2)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h7] using h 1 2)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h5, h7, h3] using h 1 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h5, h7, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h5, h7, h3] using h 0 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h7] using h 1 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h7] using h 1 1)
      · exact (by decide : (1 : Fin 3) ≠ 2)
          (by simpa only [h0, h4, h8] using h 1 2)
  · rcases split 1 1 with h4 | h4 | h4
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 1 0 with h3 | h3 | h3
        · exact (by decide : (2 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h3] using h 2 0)
        · exact (by decide : (2 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h3] using h 2 1)
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h7] using h 1 1)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h7] using h 1 1)
          · rcases split 2 0 with h6 | h6 | h6
            · rcases split 0 2 with h2 | h2 | h2
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h3, h7, h6, h2] using h 1 0)
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h3, h7, h6, h2] using h 1 2)
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h3, h7, h6, h2] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h3, h7, h6] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h7, h6] using h 0 2)
      · rcases split 0 1 with h1 | h1 | h1
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h1] using h 2 0)
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h1] using h 2 1)
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h6] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h6] using h 0 0)
          · rcases split 2 1 with h7 | h7 | h7
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h6, h7] using h 1 2)
            · rcases split 1 2 with h5 | h5 | h5
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h1, h6, h7, h5] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h1, h6, h7, h5] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h1, h6, h7, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h6, h7] using h 0 2)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h3, h2] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h3, h2] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h3, h2] using h 0 0)
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h6] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h6] using h 0 0)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h6] using h 1 2)
    · exact (by decide : (0 : Fin 3) ≠ 1)
        (by simpa only [h0, h4] using h 0 1)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h7, h3] using h 2 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h7, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h7] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 0 1 with h1 | h1 | h1
            · rcases split 1 0 with h3 | h3 | h3
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h7, h5, h1, h3] using h 1 1)
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h7, h5, h1, h3] using h 2 0)
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h7, h5, h1, h3] using h 1 1)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h7, h5, h1] using h 1 1)
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h7, h5, h1] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h7, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h5] using h 0 1)
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 0 2 with h2 | h2 | h2
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h7, h2, h1] using h 1 0)
            · rcases split 1 0 with h3 | h3 | h3
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h7, h2, h1, h3] using h 0 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h7, h2, h1, h3] using h 0 0)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h7, h2, h1, h3] using h 0 1)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h7, h2, h1] using h 1 0)
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h7, h2] using h 2 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h7, h2] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h7] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h7] using h 0 2)
      · exact (by decide : (1 : Fin 3) ≠ 2)
          (by simpa only [h0, h4, h8] using h 1 2)
  · rcases split 2 2 with h8 | h8 | h8
    · rcases split 1 1 with h4 | h4 | h4
      · rcases split 2 0 with h6 | h6 | h6
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h6] using h 1 0)
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h5] using h 2 2)
          · rcases split 1 0 with h3 | h3 | h3
            · rcases split 0 1 with h1 | h1 | h1
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h8, h4, h6, h5, h3, h1] using h 1 0)
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h8, h4, h6, h5, h3, h1] using h 1 1)
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h8, h4, h6, h5, h3, h1] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h6, h5, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h6, h5, h3] using h 0 1)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h6, h5] using h 1 2)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h6] using h 1 2)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h2, h6] using h 2 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h6] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h6] using h 0 2)
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h3] using h 0 0)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h3] using h 2 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h3] using h 0 0)
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h6] using h 0 0)
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h2, h6, h1] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h2, h6, h1] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h2, h6, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h6] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h8, h4, h2] using h 1 0)
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h2, h3] using h 0 0)
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h8, h4, h2, h3, h5] using h 2 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h2, h3, h5] using h 0 1)
            · rcases split 2 1 with h7 | h7 | h7
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h8, h4, h2, h3, h5, h7] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h8, h4, h2, h3, h5, h7] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h8, h4, h2, h3, h5, h7] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h2, h3] using h 0 0)
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h8, h4, h2] using h 1 2)
    · rcases split 1 1 with h4 | h4 | h4
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 0 1 with h1 | h1 | h1
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h8, h4, h5, h1, h3] using h 1 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h5, h1, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h5, h1, h3] using h 0 1)
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h5, h1] using h 2 1)
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h5, h1] using h 2 1)
        · rcases split 1 0 with h3 | h3 | h3
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h8, h4, h5, h3, h1] using h 1 1)
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h8, h4, h5, h3, h1] using h 1 1)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h5, h3, h1] using h 2 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h5, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h5, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h8, h4, h5] using h 0 2)
      · exact (by decide : (2 : Fin 3) ≠ 1)
          (by simpa only [h0, h8, h4] using h 2 1)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 0 1 with h1 | h1 | h1
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h8, h4, h5, h1, h2] using h 1 0)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h5, h1, h2] using h 2 0)
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h8, h4, h5, h1, h2, h6] using h 0 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h8, h4, h5, h1, h2, h6] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h8, h4, h5, h1, h2, h6] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h5, h1] using h 0 1)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h5, h1] using h 1 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h8, h4, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h8, h4, h5] using h 0 2)
    · exact (by decide : (0 : Fin 3) ≠ 2)
        (by simpa only [h0, h8] using h 0 2)

theorem not_three_1279 : ¬ Law1279.HasModel 3 := by
  rintro ⟨M, hM⟩
  have h := (@Law1279.models_iff (Fin 3) M).mp hM
  have split (x y : Fin 3) : M.op x y = 0 ∨ M.op x y = 1 ∨ M.op x y = 2 := by omega
  rcases split 0 0 with h0 | h0 | h0
  · rcases split 1 1 with h4 | h4 | h4
    · exact (by decide : (1 : Fin 3) ≠ 0)
        (by simpa only [h0, h4] using h 1 0)
    · rcases split 2 2 with h8 | h8 | h8
      · exact (by decide : (2 : Fin 3) ≠ 0)
          (by simpa only [h0, h4, h8] using h 2 0)
      · exact (by decide : (2 : Fin 3) ≠ 1)
          (by simpa only [h0, h4, h8] using h 2 1)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 1)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h7, h3] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h7, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h7, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h7] using h 0 1)
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h7, h5] using h 2 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h7, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h7, h5] using h 0 1)
    · rcases split 2 2 with h8 | h8 | h8
      · exact (by decide : (2 : Fin 3) ≠ 0)
          (by simpa only [h0, h4, h8] using h 2 0)
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 0 1 with h1 | h1 | h1
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h7, h1, h3] using h 1 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h7, h1, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h7, h1, h3] using h 0 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h1] using h 1 1)
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h7, h1, h3] using h 2 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h7, h1, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h7, h1, h3] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h7, h5] using h 1 1)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h7, h5] using h 2 2)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h5] using h 1 1)
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h7, h5] using h 1 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h5] using h 1 2)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h5] using h 1 1)
      · exact (by decide : (1 : Fin 3) ≠ 2)
          (by simpa only [h0, h4, h8] using h 1 2)
  · rcases split 1 1 with h4 | h4 | h4
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 1 0 with h3 | h3 | h3
        · exact (by decide : (2 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h3] using h 2 0)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h2] using h 1 0)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h2] using h 2 0)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h2] using h 1 0)
      · rcases split 1 0 with h3 | h3 | h3
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h1] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h1] using h 1 1)
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h3, h1, h5] using h 2 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h3, h1, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h1, h5] using h 0 1)
      · rcases split 1 0 with h3 | h3 | h3
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h1] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h6] using h 0 0)
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h6, h1] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h3, h6, h1] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h6, h1] using h 0 0)
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h3, h6, h2] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h3, h6, h2] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h6, h2] using h 0 0)
    · exact (by decide : (0 : Fin 3) ≠ 1)
        (by simpa only [h0, h4] using h 0 1)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 1 0 with h3 | h3 | h3
        · exact (by decide : (2 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h3] using h 2 0)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h1] using h 2 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h1] using h 0 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h2] using h 2 0)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h3, h2] using h 2 0)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h2] using h 1 2)
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h7, h3] using h 2 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h7, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h7] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h7, h5] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h7, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h7, h5] using h 0 1)
      · exact (by decide : (1 : Fin 3) ≠ 2)
          (by simpa only [h0, h4, h8] using h 1 2)
  · rcases split 2 2 with h8 | h8 | h8
    · rcases split 1 1 with h4 | h4 | h4
      · rcases split 2 0 with h6 | h6 | h6
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h6] using h 1 0)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h6, h1] using h 1 0)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h1] using h 2 0)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h1] using h 1 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
      · rcases split 2 0 with h6 | h6 | h6
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h6, h2] using h 2 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h3] using h 0 0)
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h8, h4, h6, h3, h1] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h6, h3, h1] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h6, h3, h1] using h 0 0)
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h6, h3, h2] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h6, h3, h2] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h6, h3, h2] using h 0 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
      · rcases split 2 0 with h6 | h6 | h6
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h6, h2] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 2)
          · rcases split 2 1 with h7 | h7 | h7
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h8, h4, h6, h2, h7] using h 1 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h6, h2, h7] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h6, h2, h7] using h 0 2)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h6, h2] using h 1 2)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
    · rcases split 1 1 with h4 | h4 | h4
      · rcases split 2 0 with h6 | h6 | h6
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h8, h4, h6] using h 1 0)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h6, h1] using h 1 0)
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h6, h1] using h 2 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h1] using h 1 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h6, h2] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h6, h2] using h 0 0)
      · exact (by decide : (2 : Fin 3) ≠ 1)
          (by simpa only [h0, h8, h4] using h 2 1)
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h8, h4, h7, h5, h6] using h 1 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h8, h4, h7, h5, h6] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h8, h4, h7, h5, h6] using h 0 2)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h7, h5] using h 1 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h7, h5] using h 0 2)
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h7, h5] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h7, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h7, h5] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h8, h4, h7, h5] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h8, h4, h7, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h8, h4, h7, h5] using h 0 1)
    · exact (by decide : (0 : Fin 3) ≠ 2)
        (by simpa only [h0, h8] using h 0 2)

theorem not_three_1286 : ¬ Law1286.HasModel 3 := by
  rintro ⟨M, hM⟩
  have h := (@Law1286.models_iff (Fin 3) M).mp hM
  have split (x y : Fin 3) : M.op x y = 0 ∨ M.op x y = 1 ∨ M.op x y = 2 := by omega
  rcases split 0 0 with h0 | h0 | h0
  · rcases split 0 1 with h1 | h1 | h1
    · rcases split 1 0 with h3 | h3 | h3
      · exact (by decide : (1 : Fin 3) ≠ 0)
          (by simpa only [h0, h1, h3] using h 1 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h1, h3] using h 0 1)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h1, h3] using h 0 1)
    · rcases split 1 0 with h3 | h3 | h3
      · exact (by decide : (1 : Fin 3) ≠ 0)
          (by simpa only [h0, h1, h3] using h 1 0)
      · rcases split 1 1 with h4 | h4 | h4
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h3, h4] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h3, h4] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h3, h4, h5, h6] using h 1 0)
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h3, h4, h5, h6] using h 2 0)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h3, h4, h5, h6] using h 1 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h3, h4, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h3, h4, h5] using h 0 1)
      · rcases split 2 1 with h7 | h7 | h7
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h3, h7] using h 0 1)
        · rcases split 1 1 with h4 | h4 | h4
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h3, h7, h4] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h3, h7, h4] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h3, h7, h4] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h3, h7, h5, h6] using h 1 0)
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h3, h7, h5, h6] using h 2 0)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h3, h7, h5, h6] using h 1 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h3, h7, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h3, h7, h5] using h 0 1)
    · rcases split 2 0 with h6 | h6 | h6
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h6, h5, h2] using h 2 0)
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h1, h6, h5, h2, h3] using h 1 0)
            · rcases split 1 1 with h4 | h4 | h4
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h1, h6, h5, h2, h3, h4] using h 1 0)
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h1, h6, h5, h2, h3, h4] using h 1 0)
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h1, h6, h5, h2, h3, h4] using h 1 0)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h1, h6, h5, h2, h3] using h 2 0)
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h6, h5, h2] using h 2 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h6, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h1, h6, h5] using h 0 1)
      · rcases split 1 1 with h4 | h4 | h4
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h6, h4, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h6, h4, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h6, h4, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h1, h6, h4] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h6, h4, h5] using h 2 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h6, h4, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h6, h4, h5] using h 0 1)
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 1 0 with h3 | h3 | h3
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h6, h7, h3, h2] using h 0 2)
            · rcases split 1 1 with h4 | h4 | h4
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h1, h6, h7, h3, h2, h4] using h 1 1)
              · exact (by decide : (2 : Fin 3) ≠ 1)
                  (by simpa only [h0, h1, h6, h7, h3, h2, h4] using h 2 1)
              · rcases split 1 2 with h5 | h5 | h5
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h1, h6, h7, h3, h2, h4, h5] using h 1 1)
                · exact (by decide : (2 : Fin 3) ≠ 1)
                    (by simpa only [h0, h1, h6, h7, h3, h2, h4, h5] using h 2 1)
                · exact (by decide : (1 : Fin 3) ≠ 2)
                    (by simpa only [h0, h1, h6, h7, h3, h2, h4, h5] using h 1 1)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h6, h7, h3, h2] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h6, h7, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h6, h7, h3] using h 0 1)
        · rcases split 1 1 with h4 | h4 | h4
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h6, h7, h4] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h1, h6, h7, h4] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h1, h6, h7, h4] using h 0 1)
        · rcases split 2 2 with h8 | h8 | h8
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h1, h6, h7, h8] using h 2 0)
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h6, h7, h8, h5] using h 1 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h1, h6, h7, h8, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h6, h7, h8, h5] using h 0 1)
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h6, h7, h8, h5] using h 1 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h1, h6, h7, h8, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h1, h6, h7, h8, h5] using h 0 1)
  · rcases split 1 0 with h3 | h3 | h3
    · rcases split 0 1 with h1 | h1 | h1
      · exact (by decide : (1 : Fin 3) ≠ 0)
          (by simpa only [h0, h3, h1] using h 1 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h1] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h3, h1] using h 0 0)
    · rcases split 0 1 with h1 | h1 | h1
      · rcases split 1 1 with h4 | h4 | h4
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h1, h4] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h1, h4] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 0 2 with h2 | h2 | h2
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h3, h1, h4, h5, h2, h6] using h 1 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h3, h1, h4, h5, h2, h6] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h1, h4, h5, h2, h6] using h 0 2)
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h3, h1, h4, h5, h2, h6] using h 2 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h3, h1, h4, h5, h2, h6] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h1, h4, h5, h2, h6] using h 0 2)
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (2 : Fin 3) ≠ 1)
                  (by simpa only [h0, h3, h1, h4, h5, h2, h6] using h 2 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h3, h1, h4, h5, h2, h6] using h 0 2)
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h1, h4, h5, h2, h6] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h3, h1, h4, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h1, h4, h5] using h 0 1)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h1] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h3, h1] using h 0 0)
    · rcases split 2 0 with h6 | h6 | h6
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h6] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 1 with h4 | h4 | h4
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h6, h1, h4] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h3, h6, h1, h4] using h 0 1)
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h3, h6, h1, h4, h5] using h 2 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h3, h6, h1, h4, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h6, h1, h4, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h6, h1] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h6, h1] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 1 2 with h5 | h5 | h5
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h6, h2, h5] using h 0 2)
          · rcases split 2 1 with h7 | h7 | h7
            · rcases split 0 1 with h1 | h1 | h1
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h3, h6, h2, h5, h7, h1] using h 1 0)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h6, h2, h5, h7, h1] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h6, h2, h5, h7, h1] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h3, h6, h2, h5, h7] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h6, h2, h5, h7] using h 0 2)
          · rcases split 2 2 with h8 | h8 | h8
            · rcases split 2 1 with h7 | h7 | h7
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h6, h2, h5, h8, h7] using h 1 2)
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h3, h6, h2, h5, h8, h7] using h 1 0)
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h3, h6, h2, h5, h8, h7] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h3, h6, h2, h5, h8] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h6, h2, h5, h8] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h6, h2] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h6, h2] using h 0 0)
  · rcases split 2 0 with h6 | h6 | h6
    · rcases split 0 2 with h2 | h2 | h2
      · exact (by decide : (2 : Fin 3) ≠ 0)
          (by simpa only [h0, h6, h2] using h 2 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h6, h2] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h6, h2] using h 0 0)
    · rcases split 1 0 with h3 | h3 | h3
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h6, h3] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h6, h3, h1, h7] using h 0 1)
          · rcases split 1 1 with h4 | h4 | h4
            · rcases split 1 2 with h5 | h5 | h5
              · exact (by decide : (2 : Fin 3) ≠ 1)
                  (by simpa only [h0, h6, h3, h1, h7, h4, h5] using h 2 1)
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h6, h3, h1, h7, h4, h5] using h 2 0)
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h6, h3, h1, h7, h4, h5] using h 2 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h6, h3, h1, h7, h4] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h6, h3, h1, h7, h4] using h 0 1)
          · rcases split 1 2 with h5 | h5 | h5
            · rcases split 0 2 with h2 | h2 | h2
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h6, h3, h1, h7, h5, h2] using h 2 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h6, h3, h1, h7, h5, h2] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h6, h3, h1, h7, h5, h2] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h6, h3, h1, h7, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h6, h3, h1, h7, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h6, h3, h1] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h6, h3, h1] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 2 with h8 | h8 | h8
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h6, h3, h2, h8] using h 0 2)
          · rcases split 2 1 with h7 | h7 | h7
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h6, h3, h2, h8, h7] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h6, h3, h2, h8, h7] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h6, h3, h2, h8, h7] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h6, h3, h2, h8] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h6, h3, h2] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h6, h3, h2] using h 0 0)
    · rcases split 0 2 with h2 | h2 | h2
      · rcases split 2 2 with h8 | h8 | h8
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h6, h2, h8] using h 0 2)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 0 1 with h1 | h1 | h1
            · rcases split 1 0 with h3 | h3 | h3
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h6, h2, h8, h7, h1, h3] using h 1 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h6, h2, h8, h7, h1, h3] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h6, h2, h8, h7, h1, h3] using h 0 1)
            · rcases split 1 0 with h3 | h3 | h3
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h6, h2, h8, h7, h1, h3] using h 1 0)
              · exact (by decide : (2 : Fin 3) ≠ 1)
                  (by simpa only [h0, h6, h2, h8, h7, h1, h3] using h 2 0)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h6, h2, h8, h7, h1, h3] using h 0 1)
            · rcases split 1 0 with h3 | h3 | h3
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h6, h2, h8, h7, h1, h3] using h 1 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h6, h2, h8, h7, h1, h3] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h6, h2, h8, h7, h1, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h6, h2, h8, h7] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h6, h2, h8, h7] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h6, h2, h8] using h 0 2)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h6, h2] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h6, h2] using h 0 0)

theorem not_three_1313 : ¬ Law1313.HasModel 3 := by
  rintro ⟨M, hM⟩
  have h := (@Law1313.models_iff (Fin 3) M).mp hM
  have split (x y : Fin 3) : M.op x y = 0 ∨ M.op x y = 1 ∨ M.op x y = 2 := by omega
  rcases split 0 0 with h0 | h0 | h0
  · rcases split 1 0 with h3 | h3 | h3
    · rcases split 0 1 with h1 | h1 | h1
      · exact (by decide : (1 : Fin 3) ≠ 0)
          (by simpa only [h0, h3, h1] using h 1 0)
      · rcases split 1 1 with h4 | h4 | h4
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h3, h1, h4] using h 1 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h1, h4] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h1, h4] using h 0 1)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h3, h1, h5, h7] using h 1 0)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h3, h1, h5, h7] using h 1 0)
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h3, h1, h5, h7, h6] using h 1 0)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h1, h5, h7, h6] using h 1 0)
            · rcases split 2 2 with h8 | h8 | h8
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h1, h5, h7, h6, h8] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h1, h5, h7, h6, h8] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h1, h5, h7, h6, h8] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h1, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h1, h5] using h 0 1)
    · rcases split 1 1 with h4 | h4 | h4
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h4] using h 0 1)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h4] using h 0 1)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h3, h4, h5, h7, h1] using h 1 0)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h4, h5, h7, h1] using h 1 1)
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h3, h4, h5, h7, h1] using h 1 0)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h3, h4, h5, h7] using h 1 1)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h3, h4, h5, h7] using h 1 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h4, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h4, h5] using h 0 1)
    · rcases split 2 0 with h6 | h6 | h6
      · rcases split 0 1 with h1 | h1 | h1
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h6, h1] using h 0 1)
        · rcases split 1 1 with h4 | h4 | h4
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h3, h6, h1, h4] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h3, h6, h1, h4] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h6, h1, h4] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h3, h6, h1, h5, h2] using h 2 0)
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h3, h6, h1, h5, h2] using h 2 0)
            · rcases split 2 2 with h8 | h8 | h8
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h3, h6, h1, h5, h2, h8] using h 2 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h3, h6, h1, h5, h2, h8] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h6, h1, h5, h2, h8] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h3, h6, h1, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h6, h1, h5] using h 0 1)
      · rcases split 1 1 with h4 | h4 | h4
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h6, h4] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h6, h4] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 2 2 with h8 | h8 | h8
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h3, h6, h4, h5, h8] using h 0 2)
            · rcases split 2 1 with h7 | h7 | h7
              · rcases split 0 1 with h1 | h1 | h1
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h3, h6, h4, h5, h8, h7, h1] using h 1 0)
                · exact (by decide : (1 : Fin 3) ≠ 2)
                    (by simpa only [h0, h3, h6, h4, h5, h8, h7, h1] using h 1 1)
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h3, h6, h4, h5, h8, h7, h1] using h 1 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h3, h6, h4, h5, h8, h7] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h3, h6, h4, h5, h8, h7] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h6, h4, h5, h8] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h3, h6, h4, h5] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h6, h4, h5] using h 0 1)
      · rcases split 2 1 with h7 | h7 | h7
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h6, h7] using h 0 1)
        · rcases split 1 1 with h4 | h4 | h4
          · rcases split 2 2 with h8 | h8 | h8
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h6, h7, h4, h8] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h3, h6, h7, h4, h8] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h6, h7, h4, h8] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h3, h6, h7, h4] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h6, h7, h4] using h 0 1)
        · rcases split 2 2 with h8 | h8 | h8
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h6, h7, h8] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h6, h7, h8] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h6, h7, h8] using h 0 2)
  · rcases split 1 0 with h3 | h3 | h3
    · rcases split 0 1 with h1 | h1 | h1
      · exact (by decide : (1 : Fin 3) ≠ 0)
          (by simpa only [h0, h3, h1] using h 1 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h1] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h3, h1] using h 0 0)
    · rcases split 0 1 with h1 | h1 | h1
      · exact (by decide : (1 : Fin 3) ≠ 0)
          (by simpa only [h0, h3, h1] using h 1 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h1] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h3, h1] using h 0 0)
    · rcases split 2 0 with h6 | h6 | h6
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h3, h6] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h3, h6, h1] using h 1 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h6, h1] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h6, h1] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h3, h6, h2, h7] using h 0 1)
          · rcases split 1 1 with h4 | h4 | h4
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h6, h2, h7, h4] using h 1 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h3, h6, h2, h7, h4] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h6, h2, h7, h4] using h 0 1)
          · rcases split 2 2 with h8 | h8 | h8
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h6, h2, h7, h8] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h6, h2, h7, h8] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h3, h6, h2, h7, h8] using h 0 2)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h3, h6, h2] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h3, h6, h2] using h 0 0)
  · rcases split 2 0 with h6 | h6 | h6
    · rcases split 0 2 with h2 | h2 | h2
      · exact (by decide : (2 : Fin 3) ≠ 0)
          (by simpa only [h0, h6, h2] using h 2 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h6, h2] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h6, h2] using h 0 0)
    · rcases split 1 0 with h3 | h3 | h3
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h6, h3] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 1 with h4 | h4 | h4
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h6, h3, h1, h4] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h6, h3, h1, h4] using h 0 1)
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h6, h3, h1, h4, h5] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h6, h3, h1, h4, h5] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h6, h3, h1, h4, h5] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h6, h3, h1] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h6, h3, h1] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h6, h3, h2] using h 2 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h6, h3, h2] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h6, h3, h2] using h 0 0)
    · rcases split 0 2 with h2 | h2 | h2
      · exact (by decide : (2 : Fin 3) ≠ 0)
          (by simpa only [h0, h6, h2] using h 2 0)
      · exact (by decide : (0 : Fin 3) ≠ 1)
          (by simpa only [h0, h6, h2] using h 0 0)
      · exact (by decide : (0 : Fin 3) ≠ 2)
          (by simpa only [h0, h6, h2] using h 0 0)

theorem not_three_1516 : ¬ Law1516.HasModel 3 := by
  rintro ⟨M, hM⟩
  have h := (@Law1516.models_iff (Fin 3) M).mp hM
  have split (x y : Fin 3) : M.op x y = 0 ∨ M.op x y = 1 ∨ M.op x y = 2 := by omega
  rcases split 0 0 with h0 | h0 | h0
  · rcases split 1 1 with h4 | h4 | h4
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 1 0 with h3 | h3 | h3
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h3] using h 1 0)
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h3] using h 1 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h2] using h 1 1)
          · rcases split 0 1 with h1 | h1 | h1
            · rcases split 1 2 with h5 | h5 | h5
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h3, h2, h1, h5] using h 1 0)
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h3, h2, h1, h5] using h 1 0)
              · rcases split 2 0 with h6 | h6 | h6
                · exact (by decide : (2 : Fin 3) ≠ 0)
                    (by simpa only [h0, h4, h8, h3, h2, h1, h5, h6] using h 2 0)
                · exact (by decide : (2 : Fin 3) ≠ 0)
                    (by simpa only [h0, h4, h8, h3, h2, h1, h5, h6] using h 2 2)
                · exact (by decide : (2 : Fin 3) ≠ 0)
                    (by simpa only [h0, h4, h8, h3, h2, h1, h5, h6] using h 2 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h3, h2, h1] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h2, h1] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h2] using h 0 2)
      · rcases split 1 0 with h3 | h3 | h3
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h3] using h 1 0)
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h3] using h 1 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h2] using h 0 2)
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h2, h1] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h3, h2, h1] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h2, h1] using h 0 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h2] using h 1 1)
      · rcases split 1 0 with h3 | h3 | h3
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h3] using h 1 0)
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h3] using h 1 0)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h3, h2] using h 1 1)
          · rcases split 0 1 with h1 | h1 | h1
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h3, h2, h1, h6] using h 2 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h3, h2, h1, h6] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h3, h2, h1, h6] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h3, h2, h1] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h3, h2, h1] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h3, h2] using h 0 2)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 2 0 with h6 | h6 | h6
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h6] using h 2 0)
        · rcases split 0 1 with h1 | h1 | h1
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h6, h1] using h 2 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h6, h1] using h 0 1)
          · rcases split 0 2 with h2 | h2 | h2
            · rcases split 1 0 with h3 | h3 | h3
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h6, h1, h2, h3] using h 1 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h6, h1, h2, h3] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h6, h1, h2, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h6, h1, h2] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h6, h1, h2] using h 0 2)
        · exact (by decide : (2 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h6] using h 2 0)
      · rcases split 2 1 with h7 | h7 | h7
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h7, h3] using h 1 0)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h7, h3] using h 2 2)
          · rcases split 1 2 with h5 | h5 | h5
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h7, h3, h5] using h 1 0)
            · rcases split 0 1 with h1 | h1 | h1
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h7, h3, h5, h1] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h7, h3, h5, h1] using h 0 1)
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h7, h3, h5, h1] using h 1 0)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h7, h3, h5] using h 1 2)
        · exact (by decide : (2 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h7] using h 2 1)
        · exact (by decide : (2 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h7] using h 2 1)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 1)
        · rcases split 0 2 with h2 | h2 | h2
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h2, h3] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h2, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h2, h3] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h2] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h2] using h 0 2)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h6] using h 1 1)
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h5, h6, h1] using h 0 1)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h5, h6, h1] using h 2 2)
            · rcases split 0 2 with h2 | h2 | h2
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h5, h6, h1, h2] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h5, h6, h1, h2] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h5, h6, h1, h2] using h 0 2)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h6] using h 1 1)
        · rcases split 0 2 with h2 | h2 | h2
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h2] using h 1 2)
          · rcases split 0 1 with h1 | h1 | h1
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h5, h2, h1, h6] using h 2 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h5, h2, h1, h6] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h5, h2, h1, h6] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h5, h2, h1] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h5, h2, h1] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h2] using h 0 2)
        · exact (by decide : (1 : Fin 3) ≠ 0)
            (by simpa only [h0, h4, h8, h5] using h 1 1)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h3] using h 1 0)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h3] using h 1 2)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h3] using h 1 0)
        · rcases split 2 1 with h7 | h7 | h7
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h7] using h 1 1)
          · exact (by decide : (2 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h5, h7] using h 2 1)
          · exact (by decide : (1 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h5, h7] using h 1 1)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 1 2)
      · rcases split 1 2 with h5 | h5 | h5
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h3] using h 1 0)
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h5, h3, h2] using h 1 0)
            · rcases split 0 1 with h1 | h1 | h1
              · rcases split 2 0 with h6 | h6 | h6
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h4, h8, h5, h3, h2, h1, h6] using h 1 1)
                · exact (by decide : (0 : Fin 3) ≠ 1)
                    (by simpa only [h0, h4, h8, h5, h3, h2, h1, h6] using h 0 1)
                · exact (by decide : (0 : Fin 3) ≠ 2)
                    (by simpa only [h0, h4, h8, h5, h3, h2, h1, h6] using h 0 1)
              · rcases split 2 1 with h7 | h7 | h7
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h4, h8, h5, h3, h2, h1, h7] using h 1 2)
                · exact (by decide : (0 : Fin 3) ≠ 1)
                    (by simpa only [h0, h4, h8, h5, h3, h2, h1, h7] using h 0 1)
                · exact (by decide : (0 : Fin 3) ≠ 2)
                    (by simpa only [h0, h4, h8, h5, h3, h2, h1, h7] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h5, h3, h2, h1] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h5, h3, h2] using h 0 2)
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h5, h3] using h 1 0)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 1 2)
        · exact (by decide : (1 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h5] using h 1 1)
  · rcases split 1 1 with h4 | h4 | h4
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 1 0)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 1 1)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 1 0)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 1 1)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 1)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 1 0)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 1 1)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 0 1 with h1 | h1 | h1
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 0)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h2] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h5, h2] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h2] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 0)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h5, h2] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h5, h2] using h 0 1)
            · rcases split 1 0 with h3 | h3 | h3
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h1, h5, h2, h3] using h 1 0)
              · rcases split 2 1 with h7 | h7 | h7
                · exact (by decide : (2 : Fin 3) ≠ 1)
                    (by simpa only [h0, h4, h8, h1, h5, h2, h3, h7] using h 2 2)
                · exact (by decide : (2 : Fin 3) ≠ 1)
                    (by simpa only [h0, h4, h8, h1, h5, h2, h3, h7] using h 2 1)
                · exact (by decide : (2 : Fin 3) ≠ 1)
                    (by simpa only [h0, h4, h8, h1, h5, h2, h3, h7] using h 2 1)
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h1, h5, h2, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h1] using h 0 0)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 0 2 with h2 | h2 | h2
            · rcases split 1 0 with h3 | h3 | h3
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h1, h5, h2, h3] using h 1 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h1, h5, h2, h3] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h1, h5, h2, h3] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h5, h2] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h2] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h1] using h 0 0)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h5, h6] using h 1 1)
            · rcases split 0 2 with h2 | h2 | h2
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h1, h5, h6, h2] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h1, h5, h6, h2] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h1, h5, h6, h2] using h 0 2)
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h6] using h 1 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h1, h7, h3] using h 1 0)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h7, h3] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h7, h3] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h7] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h7] using h 0 1)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h1] using h 0 0)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 0 2 with h2 | h2 | h2
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h2] using h 0 2)
            · rcases split 2 1 with h7 | h7 | h7
              · rcases split 1 0 with h3 | h3 | h3
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h4, h8, h1, h5, h2, h7, h3] using h 1 0)
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h4, h8, h1, h5, h2, h7, h3] using h 1 0)
                · exact (by decide : (1 : Fin 3) ≠ 2)
                    (by simpa only [h0, h4, h8, h1, h5, h2, h7, h3] using h 1 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h1, h5, h2, h7] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h1, h5, h2, h7] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h1, h5, h2] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
      · rcases split 0 1 with h1 | h1 | h1
        · rcases split 1 0 with h3 | h3 | h3
          · exact (by decide : (1 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h1, h3] using h 1 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h3] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h1] using h 0 0)
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 0 2 with h2 | h2 | h2
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h1, h5, h2, h6] using h 1 1)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h1, h5, h2, h6] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h1, h5, h2, h6] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h2] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h1, h5, h2] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h1, h5] using h 0 0)
  · rcases split 1 1 with h4 | h4 | h4
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h2, h6] using h 2 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h6] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h6] using h 0 0)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h2, h7, h6] using h 2 0)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h6] using h 2 0)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h6] using h 2 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h2] using h 0 2)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h2, h6] using h 2 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h6] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h6] using h 0 0)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 1 0 with h3 | h3 | h3
            · exact (by decide : (1 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h2, h7, h3] using h 1 1)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h3] using h 2 2)
            · rcases split 0 1 with h1 | h1 | h1
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h2, h7, h3, h1] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h2, h7, h3, h1] using h 0 1)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h2, h7, h3, h1] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h2] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h2] using h 0 2)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h1] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h1] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h2, h7, h1] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h2] using h 0 0)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h2, h6] using h 2 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h6] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h6] using h 0 0)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h2, h7, h6] using h 2 0)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h6] using h 2 0)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h6] using h 2 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h2] using h 0 2)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h2, h6] using h 2 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h6] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h6] using h 0 0)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 0 1 with h1 | h1 | h1
            · rcases split 1 0 with h3 | h3 | h3
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h2, h7, h1, h3] using h 2 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h2, h7, h1, h3] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h2, h7, h1, h3] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h1] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h1] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h2] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h2] using h 0 2)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 0 1 with h1 | h1 | h1
            · rcases split 2 0 with h6 | h6 | h6
              · exact (by decide : (2 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h2, h7, h1, h6] using h 2 0)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h2, h7, h1, h6] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h2, h7, h1, h6] using h 0 2)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h1] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h1] using h 0 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h2] using h 0 0)
    · rcases split 2 2 with h8 | h8 | h8
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 2 0 with h6 | h6 | h6
          · exact (by decide : (2 : Fin 3) ≠ 0)
              (by simpa only [h0, h4, h8, h2, h6] using h 2 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h6] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h6] using h 0 0)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h2, h7, h6] using h 2 0)
            · exact (by decide : (2 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h6] using h 2 0)
            · exact (by decide : (2 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h2, h7, h6] using h 2 1)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h2] using h 0 2)
      · rcases split 0 2 with h2 | h2 | h2
        · rcases split 1 2 with h5 | h5 | h5
          · rcases split 2 0 with h6 | h6 | h6
            · exact (by decide : (1 : Fin 3) ≠ 0)
                (by simpa only [h0, h4, h8, h2, h5, h6] using h 1 1)
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h5, h6] using h 0 0)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h2, h5, h6] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h5] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h5] using h 0 2)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (0 : Fin 3) ≠ 1)
                (by simpa only [h0, h4, h8, h2, h7, h1] using h 0 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h2, h7, h1] using h 0 2)
            · rcases split 1 2 with h5 | h5 | h5
              · rcases split 1 0 with h3 | h3 | h3
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h4, h8, h2, h7, h1, h5, h3] using h 1 2)
                · exact (by decide : (1 : Fin 3) ≠ 2)
                    (by simpa only [h0, h4, h8, h2, h7, h1, h5, h3] using h 1 2)
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h4, h8, h2, h7, h1, h5, h3] using h 1 2)
              · exact (by decide : (0 : Fin 3) ≠ 1)
                  (by simpa only [h0, h4, h8, h2, h7, h1, h5] using h 0 2)
              · exact (by decide : (0 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h2, h7, h1, h5] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (by simpa only [h0, h4, h8, h2] using h 0 0)
      · rcases split 0 2 with h2 | h2 | h2
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h2] using h 0 2)
        · rcases split 2 1 with h7 | h7 | h7
          · rcases split 0 1 with h1 | h1 | h1
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h2, h7, h1] using h 0 1)
            · rcases split 1 2 with h5 | h5 | h5
              · rcases split 2 0 with h6 | h6 | h6
                · exact (by decide : (1 : Fin 3) ≠ 0)
                    (by simpa only [h0, h4, h8, h2, h7, h1, h5, h6] using h 1 1)
                · exact (by decide : (2 : Fin 3) ≠ 1)
                    (by simpa only [h0, h4, h8, h2, h7, h1, h5, h6] using h 2 0)
                · exact (by decide : (1 : Fin 3) ≠ 2)
                    (by simpa only [h0, h4, h8, h2, h7, h1, h5, h6] using h 1 1)
              · exact (by decide : (1 : Fin 3) ≠ 0)
                  (by simpa only [h0, h4, h8, h2, h7, h1, h5] using h 1 1)
              · exact (by decide : (1 : Fin 3) ≠ 2)
                  (by simpa only [h0, h4, h8, h2, h7, h1, h5] using h 1 1)
            · exact (by decide : (0 : Fin 3) ≠ 2)
                (by simpa only [h0, h4, h8, h2, h7, h1] using h 0 2)
          · exact (by decide : (0 : Fin 3) ≠ 1)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
          · exact (by decide : (0 : Fin 3) ≠ 2)
              (by simpa only [h0, h4, h8, h2, h7] using h 0 0)
        · exact (by decide : (0 : Fin 3) ≠ 2)
            (by simpa only [h0, h4, h8, h2] using h 0 0)

end Spectrum.NoteExclusion

import equational_theories.Spectrum.Equation63.Singular
import equational_theories.Spectrum.Generated.NoteWitnesses

/-! Affine E63 seeds and small singular products. -/
namespace Spectrum.E63
open Law Law.MagmaLaw Classical

variable {R : Type*} [CommRing R]

def affine (b : R) (x y : R) : R := -b^3*x+b*y

theorem affine_law (b : R) (h : b^5+b^4+1=0) : Lawful (affine b) := by
  intro x y
  dsimp [affine]
  linear_combination -h*x

theorem affine_idem (b : R) (h : b^3-b+1=0) : Idem (affine b) := by
  intro x
  dsimp [affine]
  linear_combination -h*x

theorem affine_pointed (b : R) (h : b^5+b^4+1=0) : Pointed R :=
  ⟨affine b, affine_law b h, 0, by simp [affine]⟩

theorem modular_pointed (n : ℕ) [NeZero n] (b : ZMod n) (h : b^5+b^4+1=0) :
    Pointed (Fin n) :=
  (affine_pointed b h).relabel (Fintype.equivFinOfCardEq (ZMod.card n))

theorem modular (n : ℕ) [NeZero n] (b : ZMod n) (h : b^5+b^4+1=0) : Law63.HasModel n :=
  (modular_pointed n b h).hasModel

theorem modular_idem (n : ℕ) [NeZero n] (b : ZMod n) (h : b^3-b+1=0) :
    Model (Fin n) true := by
  have hp : b^5+b^4+1=0 := by linear_combination (b^2+b+1)*h
  exact (show Model (ZMod n) true from
    ⟨affine b, affine_law b hp, fun _ => affine_idem b h⟩).relabel
      (Fintype.equivFinOfCardEq (ZMod.card n))

theorem idem5 : Model (Fin 5) true := modular_idem 5 3 (by decide)
theorem idem7 : Model (Fin 7) true := modular_idem 7 2 (by decide)
theorem idem8 : Model (Fin 8) true := ⟨NoteWitness.table_63_8.op, by decide, by decide⟩
theorem idem11 : Model (Fin 11) true := modular_idem 11 5 (by decide)
theorem idem19 : Model (Fin 19) true := modular_idem 19 13 (by decide)

theorem pointed3 : Pointed (Fin 3) := modular_pointed 3 1 (by decide)
theorem pointed4 : Pointed (Fin 4) := ⟨NoteWitness.table_63_4.op, by decide, 0, rfl⟩
theorem pointed5 : Pointed (Fin 5) := modular_pointed 5 3 (by decide)
theorem pointed8 : Pointed (Fin 8) := ⟨NoteWitness.table_63_8.op, by decide, 0, rfl⟩

theorem Pointed.mul {n m : ℕ} (h : Pointed (Fin n)) (k : Pointed (Fin m)) :
    Pointed (Fin (n*m)) := (h.product k).relabel (Fintype.equivFinOfCardEq (by simp))

theorem model22 : Law63.HasModel 22 := singular_model idem7 pointed4 pointed3.hasModel
theorem model29 : Law63.HasModel 29 := singular_model idem7 pointed5 pointed4.hasModel
theorem model34 : Law63.HasModel 34 := singular_model idem11 pointed4 pointed3.hasModel
theorem model41 : Law63.HasModel 41 :=
  singular_model idem5 (pointed3.mul pointed3) pointed8.hasModel
theorem model58 : Law63.HasModel 58 := singular_model idem19 pointed4 pointed3.hasModel
theorem model106 : Law63.HasModel 106 :=
  singular_model idem7 (pointed4.mul pointed4) (pointed3.mul pointed5).hasModel
theorem model110 : Law63.HasModel 110 := model22.mul pointed5.hasModel
theorem model254 : Law63.HasModel 254 :=
  singular_model idem11 (pointed3.mul pointed8) (modular 23 13 (by decide))

end Spectrum.E63

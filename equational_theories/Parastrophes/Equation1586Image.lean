import equational_theories.Parastrophes.TranslationChains
import equational_theories.Parastrophes.InverseIdentities
import equational_theories.Superposition

/-!
# The six-operation left-division image of E1586

The identity `x = y * ((z * (w*y)) * ((u*x)*x))` is E148963 in the
extended numbering. Its five independent variables express the independence
of two translation parameters. It characterizes the division image on
arbitrary carriers, not only finite ones.
-/
namespace Parastrophes
open Law FreeMagma

/-- E148963, with six operations and five variables. -/
def leftImage1586 : NatMagmaLaw :=
  ⟨Lf 0, Lf 1 ⋆ ((Lf 2 ⋆ (Lf 3 ⋆ Lf 1)) ⋆ ((Lf 4 ⋆ Lf 0) ⋆ Lf 0))⟩

theorem leftImage1586_iff {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage1586 ↔ ∀ x y z w u,
      x = M.op y (M.op (M.op z (M.op w y)) (M.op (M.op u x) x)) := by
  constructor
  · intro h x y z w u
    exact h (fun n => if n = 0 then x else if n = 1 then y else
      if n = 2 then z else if n = 3 then w else u)
  · intro h v
    exact h (v 0) (v 1) (v 2) (v 3) (v 4)

namespace Eq1586Image

/-- The independent parameters force every left translation to be injective. -/
private theorem left_injective {G : Type} (M : Magma G)
    (hM : @satisfies _ G M leftImage1586) (sK0 : G) :
    Function.Injective (M.op sK0) := by
  have h := (leftImage1586_iff M).mp hM
  intro sK1 sK2 he
  by_contra hn
  have e6 (X0 X1 X2 X3 X4 : G) : (M.op X3 (M.op (M.op X4 (M.op X1 X3)) (M.op (M.op X0 X2) X2))) = X2 :=
    mod_symm (h ..)
  have e7 : (M.op sK0 sK2) = (M.op sK0 sK1) :=
    mod_symm he
  have e8 : sK1 ≠ sK2 :=
    mod_symm hn
  have e9 (X0 X1 X2 : G) : (M.op sK2 (M.op (M.op X0 (M.op sK0 sK1)) (M.op (M.op X1 X2) X2))) = X2 :=
    superpose e7 e6
  have e10 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (M.op (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X4 X0) X0)) (M.op (M.op X5 X0) (M.op (M.op X6 X7) X7))) = X7 :=
    superpose e6 e6
  have e11 (X0 X1 X5 X6 : G) : (M.op (M.op (M.op X1 X0) X0) (M.op X0 (M.op (M.op X5 X6) X6))) = X6 :=
    superpose e6 e6
  have e12 (X0 X1 X2 : G) : sK2 = (M.op X0 (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op sK0 sK1) sK2))) :=
    superpose e7 e6
  have e13 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (M.op (M.op X5 (M.op X6 X4)) (M.op (M.op X7 X0) X0)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op (M.op X5 (M.op X6 X4)) (M.op (M.op X7 X0) X0))))) :=
    superpose e6 e6
  have e14 (X0 X1 X2 X4 : G) : (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) :=
    superpose e6 e6
  have e30 (X3 X4 : G) : (M.op (M.op (M.op sK0 sK1) sK2) (M.op sK2 (M.op (M.op X3 X4) X4))) = X4 :=
    superpose e12 e6
  have e33 (X0 X1 X2 X3 X4 X5 : G) : (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op sK0 sK1) sK2)) (M.op (M.op X3 sK2) (M.op (M.op X4 X5) X5))) = X5 :=
    superpose e12 e6
  have e53 (X0 X1 X2 X3 X5 X6 : G) : (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X3 X0) (M.op (M.op X5 X6) X6))) = X6 :=
    superpose e11 e6
  have e85 (X0 X1 X2 X3 X4 : G) : (M.op (M.op X1 (M.op X2 X0)) (M.op X2 X0)) = (M.op (M.op (M.op X3 (M.op sK0 sK1)) (M.op (M.op X4 X0) X0)) (M.op X2 X0)) :=
    superpose e9 e14
  have e222 (X0 X1 X5 X6 : G) : (M.op (M.op X5 (M.op (M.op X6 X0) X0)) (M.op (M.op X6 X0) X0)) = (M.op sK2 (M.op (M.op X1 (M.op sK0 sK1)) X0)) :=
    superpose e10 e9
  have e264 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X3 X4) X4)) = (M.op (M.op (M.op X5 (M.op X6 X7)) (M.op (M.op sK0 sK1) sK2)) (M.op (M.op X8 sK2) (M.op X4 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X3 X4) X4))))) :=
    superpose e12 e13
  have e331 (X0 X1 X2 X3 X4 : G) : (M.op (M.op X0 (M.op sK0 sK1)) (M.op (M.op X1 sK2) sK2)) = (M.op X2 (M.op (M.op X3 (M.op X4 X2)) sK2)) :=
    superpose e9 e13
  have e478 (X0 X4 X5 : G) : (M.op (M.op X4 (M.op (M.op X5 X0) X0)) (M.op (M.op X5 X0) X0)) = (M.op (M.op (M.op sK0 sK1) sK2) (M.op sK2 X0)) :=
    superpose e10 e30
  have e783 (X0 X1 X2 : G) : sK2 = (M.op sK1 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) sK2))) :=
    superpose e331 e6
  have e1705 (X0 X1 X2 X3 X4 X8 X9 : G) : (M.op (M.op X8 (M.op (M.op X9 X0) X0)) (M.op (M.op X9 X0) X0)) = (M.op (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op sK0 sK1) sK2)) (M.op (M.op X4 sK2) X0)) :=
    superpose e10 e33
  have e1766 (X0 X1 X2 X3 X4 : G) : (M.op (M.op (M.op sK0 sK1) sK2) (M.op sK2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op sK0 sK1) sK2)) (M.op (M.op X4 sK2) X0)) :=
    superpose e478 e1705
  have e2173 (X0 X1 : G) : (M.op X1 (M.op sK2 (M.op (M.op X0 (M.op sK0 sK1)) X1))) = X1 :=
    superpose e222 e6
  have e3614 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (M.op (M.op (M.op X3 (M.op X4 X5)) (M.op (M.op X6 (M.op (M.op X7 X2) X2)) (M.op (M.op X7 X2) X2))) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) = X2 :=
    superpose e85 e10
  have e3711 (X2 X3 X4 X5 X6 X7 : G) : (M.op (M.op (M.op X3 (M.op X4 X5)) (M.op (M.op X6 (M.op (M.op X7 X2) X2)) (M.op (M.op X7 X2) X2))) (M.op (M.op (M.op sK0 sK1) sK2) (M.op sK2 X2))) = X2 :=
    superpose e478 e3614
  have e3802 (X2 X3 X4 X5 : G) : (M.op (M.op (M.op X3 (M.op X4 X5)) (M.op (M.op (M.op sK0 sK1) sK2) (M.op sK2 X2))) (M.op (M.op (M.op sK0 sK1) sK2) (M.op sK2 X2))) = X2 :=
    superpose e478 e3711
  have e3850 (X2 : G) : (M.op X2 (M.op (M.op (M.op sK0 sK1) sK2) (M.op sK2 X2))) = X2 :=
    superpose e14 e3802
  have e4842 (X0 X1 : G) : sK2 = (M.op sK1 (M.op (M.op (M.op X1 (M.op sK0 sK1)) X0) (M.op X0 sK2))) :=
    superpose e2173 e783
  have e9139 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X3 X0) X0)) = (M.op (M.op (M.op X4 (M.op X5 X6)) (M.op (M.op sK0 sK1) sK2)) (M.op (M.op X7 sK2) X0)) :=
    superpose e6 e264
  have e9265 (X0 X1 X2 X3 : G) : (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X3 X0) X0)) = (M.op (M.op (M.op sK0 sK1) sK2) (M.op sK2 X0)) :=
    superpose e1766 e9139
  have e11750 (X0 X1 X2 X3 X4 X5 : G) : (M.op (M.op X1 (M.op (M.op X2 (M.op sK2 (M.op (M.op X3 (M.op sK0 sK1)) X0))) (M.op sK2 (M.op (M.op X3 (M.op sK0 sK1)) X0)))) (M.op X0 (M.op (M.op X4 X5) X5))) = X5 :=
    superpose e2173 e53
  have e12257 (X0 X1 X3 X4 X5 : G) : (M.op (M.op X1 (M.op X0 (M.op sK2 (M.op (M.op X3 (M.op sK0 sK1)) X0)))) (M.op X0 (M.op (M.op X4 X5) X5))) = X5 :=
    superpose e14 e11750
  have e12311 (X0 X1 X4 X5 : G) : (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X4 X5) X5))) = X5 :=
    superpose e2173 e12257
  have e12485 (X0 X1 X2 X4 X5 : G) : (M.op (M.op X4 (M.op (M.op X5 X0) X0)) (M.op (M.op X5 X0) X0)) = (M.op (M.op X1 X2) (M.op X2 X0)) :=
    superpose e53 e12311
  have e12717 (X0 X1 X2 : G) : (M.op (M.op (M.op sK0 sK1) sK2) (M.op sK2 X0)) = (M.op (M.op X1 X2) (M.op X2 X0)) :=
    superpose e9265 e12485
  have e17092 (X0 : G) : sK2 = (M.op sK1 (M.op (M.op (M.op X0 (M.op sK0 sK1)) sK0) (M.op sK0 sK1))) :=
    superpose e7 e4842
  have e17248 : sK2 = (M.op sK1 (M.op (M.op (M.op sK0 sK1) sK2) (M.op sK2 sK1))) :=
    superpose e12717 e17092
  have e17266 : sK1 = sK2 :=
    superpose e3850 e17248
  subsumption e17266 e8

/-- Source multiplication to its left-division image. -/
private theorem forward {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (hM : @Equation1586 G M) : @satisfies _ G D leftImage1586 := by
  apply (leftImage1586_iff D).mpr
  have h := hM
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK2, sK3, sK4, sK1, sK0, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op (M.op X1 X2) (M.op X2 (M.op X0 X0))) = X0 :=
    mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 :=
    hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 :=
    hd.2 ..
  have e11 : sK2 ≠ (D.op sK3 (D.op (D.op sK4 (D.op sK1 sK3)) (D.op (D.op sK0 sK2) sK2))) :=
    mod_symm hn
  have e12 (X0 X1 X2 : G) : (M.op X0 (M.op (D.op X1 X0) (M.op X2 X2))) = X2 :=
    superpose e9 e8
  have e16 (X0 X1 X2 : G) : (M.op X2 (M.op X0 X0)) = (D.op (M.op X1 X2) X0) :=
    superpose e8 e10
  have e20 (X0 X1 X2 : G) : (D.op X1 X0) = (M.op (D.op X2 X1) (M.op X0 X0)) :=
    superpose e12 e10
  have e22 (X0 X1 X2 : G) : (M.op X1 X0) = (D.op (M.op X2 X1) (M.op (M.op X0 X0) (M.op X0 X0))) :=
    superpose e8 e16
  have e23 (X0 X1 X2 X3 : G) : (D.op (M.op X0 X1) X2) = (D.op (M.op X3 X1) X2) :=
    superpose e16 e16
  have e33 (X0 X1 X2 : G) : (M.op X2 X2) = (D.op X1 (D.op (M.op X0 X1) X2)) :=
    superpose e16 e10
  have e48 (X0 X1 X2 : G) : (M.op X1 X1) = (D.op (D.op X2 X0) (D.op X0 X1)) :=
    superpose e20 e10
  have e97 (X0 X1 X2 X3 : G) : (D.op (M.op X0 X1) (M.op (M.op X2 X1) X3)) = X3 :=
    superpose e23 e10
  have e234 (X0 X1 X2 : G) : (D.op X2 X0) = (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) :=
    superpose e10 e33
  have e515 (X0 X1 X2 X3 X4 : G) : (D.op X3 X2) = (M.op (D.op X4 X3) (D.op (D.op X0 X1) (D.op X1 X2))) :=
    superpose e48 e20
  have e521 (X0 X1 X2 : G) : (D.op X2 (D.op (D.op X0 X1) (D.op X1 X2))) = X2 :=
    superpose e48 e10
  have e679 (X0 X1 X2 X3 X4 : G) : (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) = (D.op (D.op X3 (M.op X4 X2)) X0) :=
    superpose e97 e48
  have e681 (X0 X2 X3 X4 : G) : (D.op X2 X0) = (D.op (D.op X3 (M.op X4 X2)) X0) :=
    superpose e234 e679
  have e872 (X0 X1 X2 X3 X4 : G) : (M.op X3 X2) = (D.op (M.op X4 X3) (M.op (D.op (D.op X0 X1) (D.op X1 X2)) (D.op (D.op X0 X1) (D.op X1 X2)))) :=
    superpose e48 e22
  have e918 (X1 X2 X3 X4 : G) : (M.op X3 X2) = (D.op (M.op X4 X3) (D.op (D.op X1 X2) X2)) :=
    superpose e515 e872
  have e2443 (X0 X1 X2 X3 : G) : (D.op (D.op X3 X0) X0) = (M.op (D.op (D.op X1 X2) (D.op X2 X0)) (D.op (D.op X1 X2) (D.op X2 X0))) :=
    superpose e521 e48
  have e2459 (X0 X2 X3 : G) : (D.op (D.op X3 X0) X0) = (D.op (D.op X2 X0) X0) :=
    superpose e515 e2443
  have e3729 (X0 X1 X2 X3 : G) : (D.op (M.op X1 X1) X2) = (D.op (D.op X3 (D.op X0 X1)) X2) :=
    superpose e20 e681
  have e5536 (X0 : G) : sK2 ≠ (D.op sK3 (D.op (D.op sK4 (D.op sK1 sK3)) (D.op (D.op X0 sK2) sK2))) :=
    superpose e2459 e11
  have e5564 (X0 : G) : sK2 ≠ (D.op sK3 (D.op (M.op sK3 sK3) (D.op (D.op X0 sK2) sK2))) :=
    superpose e3729 e5536
  have e5582 : sK2 ≠ (D.op sK3 (M.op sK3 sK2)) :=
    superpose e918 e5564
  subsumption e5582 e10

/-- The image identity recovers E1586 under actual left division. -/
private theorem reverse {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (hM : @satisfies _ G M leftImage1586) : @Equation1586 G D := by
  have h := (leftImage1586_iff M).mp hM
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 X3 X4 : G) : (M.op X3 (M.op (M.op X4 (M.op X1 X3)) (M.op (M.op X0 X2) X2))) = X2 :=
    mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 :=
    hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 :=
    hd.2 ..
  have e11 : sK0 ≠ (D.op (D.op sK1 sK2) (D.op sK2 (D.op sK0 sK0))) :=
    mod_symm hn
  have e12 (X0 X1 X2 X3 X4 : G) : (M.op (D.op X1 X0) (M.op (M.op X2 X0) (M.op (M.op X3 X4) X4))) = X4 :=
    superpose e9 e8
  have e15 (X0 X1 X2 X3 X4 : G) : (D.op X4 X0) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (D.op X4 X0)))) :=
    superpose e9 e8
  have e18 (X0 X1 X2 X3 X4 : G) : (D.op X1 X0) = (M.op (M.op X2 (M.op X3 X1)) (M.op (M.op X4 X0) X0)) :=
    superpose e8 e10
  have e32 (X0 X1 X2 X3 X4 : G) : (M.op (M.op X3 X2) (M.op (M.op X4 X0) X0)) = (D.op (D.op X1 X2) X0) :=
    superpose e12 e10
  have e116 (X0 X1 X2 X6 : G) : (D.op X1 X2) = (M.op (D.op X0 X1) (M.op (M.op X6 X2) X2)) :=
    superpose e18 e18
  have e132 (X0 X1 X2 X3 : G) : (M.op (D.op X2 (M.op X3 X0)) (D.op X0 X1)) = X1 :=
    superpose e18 e12
  have e146 (X0 X1 X2 X3 X4 : G) : (M.op (M.op X4 X1) X1) = (D.op (M.op X2 (M.op X3 X0)) (D.op X0 X1)) :=
    superpose e18 e10
  have e159 (X0 X1 X4 X5 : G) : (M.op (D.op X1 X0) (D.op (D.op X4 X0) X5)) = X5 :=
    superpose e132 e132
  have e200 (X0 X1 X2 X6 : G) : (M.op (D.op X0 X1) (M.op (M.op X6 X2) X2)) = (D.op (M.op X1 (D.op X0 X1)) X2) :=
    superpose e15 e18
  have e222 (X0 X1 X2 : G) : (D.op X1 X2) = (D.op (M.op X1 (D.op X0 X1)) X2) :=
    superpose e116 e200
  have e230 (X0 X1 X2 : G) : (M.op (M.op X0 (D.op X2 X0)) (D.op X0 X1)) = X1 :=
    superpose e222 e9
  have e586 (X0 X1 X2 X3 : G) : (D.op (D.op X1 X2) X0) = (D.op (D.op X3 X2) X0) :=
    superpose e159 e10
  have e2262 (X0 X1 X2 X3 : G) : (D.op (M.op X0 (M.op X1 X2)) (D.op X2 (D.op X3 X3))) = X3 :=
    superpose e146 e230
  have e2450 (X0 : G) : sK0 ≠ (D.op (D.op X0 sK2) (D.op sK2 (D.op sK0 sK0))) :=
    superpose e586 e11
  have e2631 (X0 X1 X2 : G) : sK0 ≠ (D.op (M.op (M.op X0 X1) (M.op (M.op X2 sK2) sK2)) (D.op sK2 (D.op sK0 sK0))) :=
    superpose e32 e2450
  subsumption e2631 e2262

end Eq1586Image

namespace Catalogue

/-- E1586's exact left-division image is E148963 on arbitrary carriers. -/
@[parastrophe_result] theorem left_characterizes1586_all_long :
    Characterizes .all Law1586 .left leftImage1586 := by
  apply characterizes_of_division
  · intro G M _ h
    refine fun y => ⟨Eq1586Image.left_injective M h y, ?_⟩
    intro x
    exact ⟨_, ((leftImage1586_iff M).mp h x y y y y).symm⟩
  · intro G M D _ hd h
    exact Eq1586Image.forward M D hd ((@Law1586.models_iff G M).mp h)
  · intro G M D _ hd h
    exact (@Law1586.models_iff G D).mpr (Eq1586Image.reverse M D hd h)

/-- The inverse parastrophe is the five-operation term
`(x*(x*x))*((x*y)*y)` in the new image operation. -/
theorem leftImage1586_term_all :
    UniformTermWitness .all leftImage1586 .left
      ((Lf 0 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ ((Lf 0 ⋆ Lf 1) ⋆ Lf 1)) := by
  intro G M _ h
  have hi := Eq1586Image.left_injective M h
  have he (x y : G) := ((leftImage1586_iff M).mp h y x x x x).symm
  constructor
  · exact he
  · intro x y
    exact hi x (he x (M.op x y))

/-- The exact image correspondence preserves labelled and unlabelled model
counts on every carrier, including infinite carriers. -/
theorem sameFineSpectrum1586_leftImage : SameFineSpectrum .all Law1586 leftImage1586 := by
  apply characterizes_sameFineSpectrum left_characterizes1586_all_long
  intro G M _ h
  have hm := (@Law1586.models_iff G M).mp h
  have h1525 := (@Law1525.models_iff G M).mpr (fun x y => hm x y y)
  exact sideQuasigroup_of_division (left_term1525_all_inverse G M trivial h1525)

end Catalogue
end Parastrophes

import equational_theories.Parastrophes.TranslationChains
import equational_theories.Superposition

/-!
# The eight-operation left-division image of E703

Write `p(x) = L_x^5(x)`. The image is characterized by
`x = y * (y * (p(x) * x))`, on arbitrary carriers.
In both identities the common inverse of all squared translations has cube one.
Consequently every translation has sixth power one, so five divisions recover
one multiplication. No finiteness or computational certificates are needed.
-/
namespace Parastrophes
open Law FreeMagma

def rowFive {G : Type*} (M : Magma G) (x z : G) : G :=
  M.op x (M.op x (M.op x (M.op x (M.op x z))))

/-- E26546951 in the canonical extended numbering. -/
def leftImage703 : NatMagmaLaw :=
  ⟨Lf 0, Lf 1 ⋆ (Lf 1 ⋆
    ((Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))))) ⋆ Lf 0))⟩

theorem leftImage703_iff {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage703 ↔
      ∀ x y, x = M.op y (M.op y (M.op (rowFive M x x) x)) := by
  constructor
  · intro h x y
    exact h (fun n => if n = 0 then x else y)
  · intro h v
    exact h (v 0) (v 1)

namespace Eq703Image

/-- A common inverse of squared translations, whose cube is one, gives
an explicit sixth-power bound on every row. -/
theorem row_six {G : Type} (M : Magma G) (c : G → G)
    (h : ∀ x y, M.op y (M.op y (c x)) = x)
    (hc : ∀ x, c (c (c x)) = x) (y x : G) :
    M.op y (rowFive M y x) = x := by
  have hs (y x : G) : M.op y (M.op y x) = c (c x) := by
    have he := h (c (c x)) y
    rw [hc] at he
    exact he
  change M.op y (M.op y (M.op y (M.op y (M.op y (M.op y x))))) = x
  rw [hs, hs, hs, hc, hc]

theorem leftQuasigroup {G : Type} (M : Magma G)
    (h6 : ∀ y x, M.op y (rowFive M y x) = x) : IsSideQuasigroup .left M := by
  intro y
  refine ⟨?_, fun x => ⟨rowFive M y x, h6 y x⟩⟩
  intro a b hab
  have he := congrArg (rowFive M y) hab
  change M.op y (rowFive M y a) = M.op y (rowFive M y b) at he
  simpa only [h6] using he

theorem two_divisions {G : Type} (M D : Magma G) (c : G → G)
    (hd : IsDivision .left M D)
    (h : ∀ x y, M.op y (M.op y (c x)) = x) (y x : G) :
    D.op y (D.op y x) = c x := by
  have he := congrArg (fun z => D.op y (D.op y z)) (h x y)
  simpa only [hd.2] using he.symm

theorem five_divisions {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D)
    (h6 : ∀ y x, M.op y (rowFive M y x) = x) (y x : G) :
    rowFive D y x = M.op y x := by
  have he := congrArg (rowFive D y) (h6 y x)
  simpa only [rowFive, hd.2] using he.symm

/-- Reindex the common square by the row used in the inner division. -/
theorem cancel_common {G : Type} (M D : Magma G) (c : G → G)
    (hd : IsDivision .left M D)
    (h : ∀ x y, M.op y (M.op y (c x)) = x)
    (x y a : G) (ha : c x = M.op a x) :
    D.op y (D.op y (D.op a x)) = x := by
  calc
    D.op y (D.op y (D.op a x)) = D.op a (D.op a (D.op a x)) :=
      (two_divisions M D c hd h y _).trans (two_divisions M D c hd h a _).symm
    _ = D.op a (c x) := congrArg (D.op a) (two_divisions M D c hd h a x)
    _ = x := by rw [ha, hd.2]

/-- The ordinary cubic map in E703 has cube one. -/
theorem cube_of703 {G : Type} (M : Magma G) (c : G → G)
    (h : ∀ x y, M.op y (M.op y (c x)) = x)
    (hd : ∀ x, c x = M.op (M.op x x) x) : ∀ x, c (c (c x)) = x := by
  have e10 (x : G) : M.op (M.op (c x) (c x)) (c (c x)) = x := superpose hd h
  have e11 (x : G) : c x = M.op (M.op (c x) (c x)) x := superpose e10 h
  have e12 (x : G) : M.op (M.op (c (c x)) (c (c x))) (c (c x)) = x :=
    superpose e11 h
  exact fun x => (hd (c (c x))).trans (e12 x)

/-- The longer image identity has the same cube-one property. Naming the
common map keeps the equational derivation small. -/
theorem cube_of_image {G : Type} (M : Magma G) (c : G → G)
    (h : ∀ x y, M.op y (M.op y (c x)) = x)
    (hd : ∀ x, c x = M.op (rowFive M x x) x) : ∀ x, c (c (c x)) = x := by
  have e10 (x : G) : c (c x) = M.op (M.op (c x) (M.op (c x) (M.op (c x) x))) (c x) :=
    by simpa only [rowFive, h] using hd (c x)
  have e11 (x : G) : M.op (rowFive M (c x) (c x)) (c (c x)) = x :=
    superpose hd h
  have e12 (x : G) : M.op (M.op (c x) (M.op (c x) (M.op (c x) x))) (c (c x)) = x :=
    by simpa only [rowFive, h] using e11 x
  have e13 (x : G) : c x = M.op (M.op (c (c x)) x) (c (c (c x))) :=
    superpose h e12
  have e15 (x : G) : c (c x) = M.op (M.op (c (c x)) x) (c x) :=
    superpose e13 h
  have e16 (x : G) : c (c (c x)) = M.op (M.op (c (c x)) x) (c (c x)) :=
    superpose h e10
  have e18 (x : G) : M.op (M.op (c (c x)) x) (c (c x)) = x :=
    superpose e15 h
  exact fun x => (e16 x).trans (e18 x)

end Eq703Image

namespace Catalogue

/-- The eight-operation identity exactly characterizes E703's left-division
image, including on infinite carriers. -/
@[parastrophe_result] theorem left_characterizes703_all_long :
    Characterizes .all Law703 .left leftImage703 := by
  apply characterizes_of_division
  · intro G M _ hM
    let c (x : G) := M.op (rowFive M x x) x
    have h : ∀ x y, M.op y (M.op y (c x)) = x :=
      fun x y => ((leftImage703_iff M).mp hM x y).symm
    exact Eq703Image.leftQuasigroup M
      (Eq703Image.row_six M c h (Eq703Image.cube_of_image M c h (fun _ => rfl)))
  · intro G M D _ hd hM
    let c (x : G) := M.op (M.op x x) x
    have h : ∀ x y, M.op y (M.op y (c x)) = x :=
      fun x y => ((@Law703.models_iff G M).mp hM x y).symm
    have h6 := Eq703Image.row_six M c h
      (Eq703Image.cube_of703 M c h (fun _ => rfl))
    apply (leftImage703_iff D).mpr
    intro x y
    rw [Eq703Image.five_divisions M D hd h6]
    exact (Eq703Image.cancel_common M D c hd h x y (M.op x x) rfl).symm
  · intro G M D _ hd hM
    let c (x : G) := M.op (rowFive M x x) x
    have h : ∀ x y, M.op y (M.op y (c x)) = x :=
      fun x y => ((leftImage703_iff M).mp hM x y).symm
    have h6 := Eq703Image.row_six M c h
      (Eq703Image.cube_of_image M c h (fun _ => rfl))
    apply (@Law703.models_iff G D).mpr
    intro x y
    have he : rowFive M x x = D.op x x := by
      have he := congrArg (D.op x) (h6 x x)
      simpa only [hd.2] using he
    exact (Eq703Image.cancel_common M D c hd h x y (D.op x x)
      (congrArg (fun a => M.op a x) he)).symm

/-- A small counterexample explains why the longer image identity is needed:
E703 itself is not preserved by left division. -/
@[implicit_reducible] private def nonself703 : Magma (Fin 9) :=
  ⟨fun x y => (![
    ![3, 6, 5, 2, 0, 7, 8, 4, 1],
    ![8, 0, 6, 4, 5, 3, 7, 1, 2],
    ![4, 6, 3, 7, 2, 0, 8, 5, 1],
    ![7, 6, 0, 4, 5, 3, 8, 2, 1],
    ![6, 7, 1, 4, 5, 3, 2, 8, 0],
    ![8, 0, 6, 4, 5, 3, 7, 1, 2],
    ![7, 5, 0, 1, 6, 8, 3, 2, 4],
    ![1, 2, 8, 4, 5, 3, 0, 6, 7],
    ![8, 0, 6, 4, 5, 3, 7, 1, 2]] : Fin 9 → Fin 9 → Fin 9) x y⟩

theorem not_characterizes_self703_fin :
    ¬ Characterizes .fin Law703 .left Law703 := by
  intro hc
  let M := nonself703
  let D : Magma (Fin 9) := ⟨fun x y => rowFive M x y⟩
  have hm : @satisfies _ (Fin 9) M Law703 := (@Law703.models_iff (Fin 9) M).mpr (by decide)
  have hd : IsDivision .left M D := by constructor <;> decide
  have hD := (hc (Fin 9) D (inferInstance : Finite (Fin 9))).mpr ⟨M, hm, hd⟩
  have he := (@Law703.models_iff (Fin 9) D).mp hD 0 0
  exact (by decide : (0 : Fin 9) ≠ 1) he

end Catalogue
end Parastrophes

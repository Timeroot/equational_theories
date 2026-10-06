import equational_theories.Spectrum.Equation667Twelve.Encoding
import equational_theories.Spectrum.FiniteSearch.Pinned

namespace Spectrum.E667.Twelve
open RightIdentityTwelve (Holds)
open Spectrum.FiniteSearch

private def growingData : Array (Fin 12 × Fin 12) :=
  #[(0,0), (0,1), (1,0), (1,1), (0,2), (1,2), (2,0), (2,1), (2,2), (0,3), (1,3), (2,3), (3,0), (3,1), (3,2), (3,3), (0,4), (1,4), (2,4), (3,4), (4,0), (4,1), (4,2), (4,3), (4,4), (0,5), (1,5), (2,5), (3,5), (4,5), (5,0), (5,1), (5,2), (5,3), (5,4), (5,5), (0,6), (1,6), (2,6), (3,6), (4,6), (5,6), (6,0), (6,1), (6,2), (6,3), (6,4), (6,5), (6,6), (0,7), (1,7), (2,7), (3,7), (4,7), (5,7), (6,7), (7,0), (7,1), (7,2), (7,3), (7,4), (7,5), (7,6), (7,7), (0,8), (1,8), (2,8), (3,8), (4,8), (5,8), (6,8), (7,8), (8,0), (8,1), (8,2), (8,3), (8,4), (8,5), (8,6), (8,7), (8,8), (0,9), (1,9), (2,9), (3,9), (4,9), (5,9), (6,9), (7,9), (8,9), (9,0), (9,1), (9,2), (9,3), (9,4), (9,5), (9,6), (9,7), (9,8), (9,9), (0,10), (1,10), (2,10), (3,10), (4,10), (5,10), (6,10), (7,10), (8,10), (9,10), (10,0), (10,1), (10,2), (10,3), (10,4), (10,5), (10,6), (10,7), (10,8), (10,9), (10,10), (0,11), (1,11), (2,11), (3,11), (4,11), (5,11), (6,11), (7,11), (8,11), (9,11), (10,11), (11,0), (11,1), (11,2), (11,3), (11,4), (11,5), (11,6), (11,7), (11,8), (11,9), (11,10), (11,11)]

def growingCells (i : Fin 144) : Fin 12 × Fin 12 := growingData[i.val]!
def rowCells (i : Fin 12) : Fin 12 × Fin 12 := (0,i)
def threeUnits : List Entry := [(0,0,2),(1,1,2),(2,2,0)]
def fourUnits : List Entry := [(0,0,2),(1,1,2),(2,2,3)]
def threeFormula : Std.Sat.CNF ℕ := natFormula 3 rowCells threeUnits
def fourFormula : Std.Sat.CNF ℕ := natFormula 4 growingCells fourUnits

theorem no_three (hn : threeFormula.Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f)
    (a b c : Fin 12) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : f a a = c) (hb : f b b = c) (hc : f c c = a) : False := by
  let v : Fin 3 → Fin 12 := ![a,b,c]
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v]
  obtain ⟨e,he⟩ := exists_perm_initial (by decide : 3 ≤ 12) v hv
  have hea : e a = 0 := by simpa [v] using he 0
  have heb : e b = 1 := by simpa [v] using he 1
  have hec : e c = 2 := by simpa [v] using he 2
  have hsa : e.symm 0 = a := by apply e.injective; simp [hea]
  have hsb : e.symm 1 = b := by apply e.injective; simp [heb]
  have hsc : e.symm 2 = c := by apply e.injective; simp [hec]
  apply no_model 3 rowCells threeUnits (by simp [threeUnits]) hn (relabel f e)
    (RightIdentityTwelve.holds_relabel h e)
  simp [UnitsHold,threeUnits,relabel,hsa,hsb,hsc,ha,hb,hc,hea,hec]

theorem no_four (hn : fourFormula.Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f)
    (a b c d : Fin 12) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : f a a = c) (hb : f b b = c) (hc : f c c = d) : False := by
  let v : Fin 4 → Fin 12 := ![a,b,c,d]
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v]
  obtain ⟨e,he⟩ := exists_perm_initial (by decide : 4 ≤ 12) v hv
  have hea : e a = 0 := by simpa [v] using he 0
  have heb : e b = 1 := by simpa [v] using he 1
  have hec : e c = 2 := by simpa [v] using he 2
  have hed : e d = 3 := by simpa [v] using he 3
  have hsa : e.symm 0 = a := by apply e.injective; simp [hea]
  have hsb : e.symm 1 = b := by apply e.injective; simp [heb]
  have hsc : e.symm 2 = c := by apply e.injective; simp [hec]
  apply no_model 4 growingCells fourUnits (by simp [fourUnits]) hn (relabel f e)
    (RightIdentityTwelve.holds_relabel h e)
  simp [UnitsHold,fourUnits,relabel,hsa,hsb,hsc,ha,hb,hc,hec,hed]

spectrum_assert no_three complete
spectrum_assert no_four complete
end Spectrum.E667.Twelve

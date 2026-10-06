import equational_theories.Spectrum.Equation467.OrderSixteen.Rows
namespace Spectrum.E467.OrderSixteen
abbrev Ref := Fin 112

def refCase (r : Ref) : Case := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66][r.val]!
def refValue (r : Ref) : Option Point := #[none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none][r.val]!
def selectRef (i : Case) (v : Point) : Ref :=
  let starts := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,63,79,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111]
  ⟨(starts[i.val]! + if 47 ≤ i.val ∧ i.val < 50 then v.val else 0)%112,
    Nat.mod_lt _ (by decide)⟩
@[spectrum_native]
theorem select_checked : ∀ (i : Case) (v : Point),
    refCase (selectRef i v) = i ∧
    (refValue (selectRef i v) = none ∨ refValue (selectRef i v) = some v) := by
  native_decide
end Spectrum.E467.OrderSixteen

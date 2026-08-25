import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `PSL7` on `Fin 7`

One class of `Definability/ExactAut7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`168` group `⟨(0 1 3 2 5 4 6), (0 1 3 6 4 2 5)⟩` -/

/-- The `168` elements of the group: `()`, `(3 4)(5 6)`, `(3 5)(4 6)`, `(3 6)(4 5)`, `(1 2)(4 5)`,
`(1 2)(3 4 6 5)`, `(1 2)(3 5 6 4)`, `(1 2)(3 6)`, `(1 3)(2 6)`, `(1 3 2 6)(4 5)`, `(1 3 4)(2 6 5)`,
`(1 3 5)(2 6 4)`, `(1 4 3)(2 5 6)`, `(1 4 6)(2 5 3)`, `(1 4)(2 5)`, `(1 4 2 5)(3 6)`, `(1 5 3)(2 4
6)`, `(1 5 6)(2 4 3)`, `(1 5)(2 4)`, `(1 5 2 4)(3 6)`, `(1 6 2 3)(4 5)`, `(1 6)(2 3)`, `(1 6 5)(2 3
4)`, `(1 6 4)(2 3 5)`, `(0 1)(5 6)`, `(0 1)(3 4)`, `(0 1)(3 5 4 6)`, `(0 1)(3 6 4 5)`, `(0 1 2)(4 6
5)`, `(0 1 2)(3 4 5)`, `(0 1 2)(3 5 6)`, `(0 1 2)(3 6 4)`, `(0 1 3)(2 5 6)`, `(0 1 3 2 5 4 6)`, `(0
1 3 4)(2 5)`, `(0 1 3 6 4 2 5)`, `(0 1 4 3)(2 6)`, `(0 1 4 5 3 2 6)`, `(0 1 4)(2 6 5)`, `(0 1 4 2 6
3 5)`, `(0 1 5 4 6 2 3)`, `(0 1 5 6)(2 3)`, `(0 1 5)(2 3 4)`, `(0 1 5 2 3 6 4)`, `(0 1 6 2 4 5 3)`,
`(0 1 6)(2 4 3)`, `(0 1 6 5)(2 4)`, `(0 1 6 3 5 2 4)`, `(0 2 1)(4 5 6)`, `(0 2 1)(3 4 6)`, `(0 2
1)(3 5 4)`, `(0 2 1)(3 6 5)`, `(0 2)(4 6)`, `(0 2)(3 4 5 6)`, `(0 2)(3 5)`, `(0 2)(3 6 5 4)`, `(0 2
4 5 6 1 3)`, `(0 2 4 6)(1 3)`, `(0 2 4)(1 3 5)`, `(0 2 4 1 3 6 5)`, `(0 2 3)(1 4 6)`, `(0 2 3 1 4 5
6)`, `(0 2 3 5)(1 4)`, `(0 2 3 6 5 1 4)`, `(0 2 6 1 5 4 3)`, `(0 2 6)(1 5 3)`, `(0 2 6 4)(1 5)`, `(0
2 6 3 4 1 5)`, `(0 2 5 3)(1 6)`, `(0 2 5 4 3 1 6)`, `(0 2 5)(1 6 4)`, `(0 2 5 1 6 3 4)`, `(0 3 1)(2
6 5)`, `(0 3 2 6 4 5 1)`, `(0 3 4 1)(2 6)`, `(0 3 5 4 2 6 1)`, `(0 3)(2 5)`, `(0 3 2 5)(4 6)`, `(0 3
4)(2 5 6)`, `(0 3 6)(2 5 4)`, `(0 3)(1 2 4 5)`, `(0 3 1 2 4 6 5)`, `(0 3 5 6 1 2 4)`, `(0 3 6)(1 2
4)`, `(0 3)(1 4)`, `(0 3 1 4)(5 6)`, `(0 3 5)(1 4 6)`, `(0 3 6)(1 4 5)`, `(0 3)(1 5 4 2)`, `(0 3 2 1
5 6 4)`, `(0 3 4 6 2 1 5)`, `(0 3 6)(1 5 2)`, `(0 3 1 6 5 4 2)`, `(0 3 2)(1 6 4)`, `(0 3 4 5 1 6
2)`, `(0 3 5 2)(1 6)`, `(0 4 3 1)(2 5)`, `(0 4 6 3 2 5 1)`, `(0 4 1)(2 5 6)`, `(0 4 2 5 3 6 1)`, `(0
4 3)(2 6 5)`, `(0 4 5)(2 6 3)`, `(0 4)(2 6)`, `(0 4 2 6)(3 5)`, `(0 4 6 5 1 2 3)`, `(0 4 5)(1 2 3)`,
`(0 4 1 2 3 5 6)`, `(0 4)(1 2 3 6)`, `(0 4 1 3)(5 6)`, `(0 4)(1 3)`, `(0 4 6)(1 3 5)`, `(0 4 5)(1 3
6)`, `(0 4 2)(1 5 3)`, `(0 4 1 5 6 3 2)`, `(0 4 6 2)(1 5)`, `(0 4 3 6 1 5 2)`, `(0 4 2 1 6 5 3)`,
`(0 4)(1 6 3 2)`, `(0 4 5)(1 6 2)`, `(0 4 3 5 2 1 6)`, `(0 5 2 4 6 3 1)`, `(0 5 1)(2 4 3)`, `(0 5 6
1)(2 4)`, `(0 5 3 6 2 4 1)`, `(0 5 2 3)(4 6)`, `(0 5)(2 3)`, `(0 5 6)(2 3 4)`, `(0 5 4)(2 3 6)`, `(0
5 1 2 6 4 3)`, `(0 5)(1 2 6 3)`, `(0 5 4)(1 2 6)`, `(0 5 3 4 1 2 6)`, `(0 5 6 4 2 1 3)`, `(0 5 4)(1
3 2)`, `(0 5 2 1 3 4 6)`, `(0 5)(1 3 6 2)`, `(0 5 6 3 1 4 2)`, `(0 5 3 2)(1 4)`, `(0 5 2)(1 4 6)`,
`(0 5 1 4 3 6 2)`, `(0 5 3)(1 6 4)`, `(0 5 4)(1 6 3)`, `(0 5)(1 6)`, `(0 5 1 6)(3 4)`, `(0 6 4 5 2 3
1)`, `(0 6 5 1)(2 3)`, `(0 6 1)(2 3 4)`, `(0 6 2 3 5 4 1)`, `(0 6 3)(2 4 5)`, `(0 6 5)(2 4 3)`, `(0
6)(2 4)`, `(0 6 2 4)(3 5)`, `(0 6 3)(1 2 5)`, `(0 6 4 3 1 2 5)`, `(0 6)(1 2 5 4)`, `(0 6 1 2 5 3
4)`, `(0 6 4 2)(1 3)`, `(0 6 5 4 1 3 2)`, `(0 6 1 3 4 5 2)`, `(0 6 2)(1 3 5)`, `(0 6 3)(1 4 2)`, `(0
6 5 3 2 1 4)`, `(0 6)(1 4 5 2)`, `(0 6 2 1 4 3 5)`, `(0 6 3)(1 5 4)`, `(0 6 4)(1 5 3)`, `(0 6)(1
5)`, `(0 6 1 5)(3 4)`. -/
def pEPSL70 : Fin 7 → Fin 7 := id
def pEPSL71 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
def pEPSL72 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 6 | 5 => 3 | 6 => 4
def pEPSL73 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 5 | 5 => 4 | 6 => 3
def pEPSL74 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6
def pEPSL75 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 6 | 5 => 3 | 6 => 5
def pEPSL76 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 6 | 6 => 4
def pEPSL77 : Fin 7 → Fin 7 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 6 | 4 => 4 | 5 => 5 | 6 => 3
def pEPSL78 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 2
def pEPSL79 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 1
def pEPSL710 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 4 | 4 => 1 | 5 => 2 | 6 => 5
def pEPSL711 : Fin 7 → Fin 7 | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 5 | 4 => 2 | 5 => 1 | 6 => 4
def pEPSL712 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 2
def pEPSL713 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 2 | 4 => 6 | 5 => 3 | 6 => 1
def pEPSL714 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 2 | 6 => 6
def pEPSL715 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 2 | 5 => 1 | 6 => 3
def pEPSL716 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 1 | 4 => 6 | 5 => 3 | 6 => 2
def pEPSL717 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 1
def pEPSL718 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 1 | 6 => 6
def pEPSL719 : Fin 7 → Fin 7 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 6 | 4 => 1 | 5 => 2 | 6 => 3
def pEPSL720 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 2
def pEPSL721 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 1
def pEPSL722 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 1 | 6 => 5
def pEPSL723 : Fin 7 → Fin 7 | 0 => 0 | 1 => 6 | 2 => 3 | 3 => 5 | 4 => 1 | 5 => 2 | 6 => 4
def pEPSL724 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5
def pEPSL725 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6
def pEPSL726 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 6 | 5 => 4 | 6 => 3
def pEPSL727 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 6 | 4 => 5 | 5 => 3 | 6 => 4
def pEPSL728 : Fin 7 → Fin 7 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 6 | 5 => 4 | 6 => 5
def pEPSL729 : Fin 7 → Fin 7 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 3 | 6 => 6
def pEPSL730 : Fin 7 → Fin 7 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 5 | 4 => 4 | 5 => 6 | 6 => 3
def pEPSL731 : Fin 7 → Fin 7 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 6 | 4 => 3 | 5 => 5 | 6 => 4
def pEPSL732 : Fin 7 → Fin 7 | 0 => 1 | 1 => 3 | 2 => 5 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 2
def pEPSL733 : Fin 7 → Fin 7 | 0 => 1 | 1 => 3 | 2 => 5 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 0
def pEPSL734 : Fin 7 → Fin 7 | 0 => 1 | 1 => 3 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 2 | 6 => 6
def pEPSL735 : Fin 7 → Fin 7 | 0 => 1 | 1 => 3 | 2 => 5 | 3 => 6 | 4 => 2 | 5 => 0 | 6 => 4
def pEPSL736 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 6 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 2
def pEPSL737 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 6 | 3 => 2 | 4 => 5 | 5 => 3 | 6 => 0
def pEPSL738 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 6 | 3 => 3 | 4 => 0 | 5 => 2 | 6 => 5
def pEPSL739 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 6 | 3 => 5 | 4 => 2 | 5 => 0 | 6 => 3
def pEPSL740 : Fin 7 → Fin 7 | 0 => 1 | 1 => 5 | 2 => 3 | 3 => 0 | 4 => 6 | 5 => 4 | 6 => 2
def pEPSL741 : Fin 7 → Fin 7 | 0 => 1 | 1 => 5 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 0
def pEPSL742 : Fin 7 → Fin 7 | 0 => 1 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 0 | 6 => 6
def pEPSL743 : Fin 7 → Fin 7 | 0 => 1 | 1 => 5 | 2 => 3 | 3 => 6 | 4 => 0 | 5 => 2 | 6 => 4
def pEPSL744 : Fin 7 → Fin 7 | 0 => 1 | 1 => 6 | 2 => 4 | 3 => 0 | 4 => 5 | 5 => 3 | 6 => 2
def pEPSL745 : Fin 7 → Fin 7 | 0 => 1 | 1 => 6 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 0
def pEPSL746 : Fin 7 → Fin 7 | 0 => 1 | 1 => 6 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 0 | 6 => 5
def pEPSL747 : Fin 7 → Fin 7 | 0 => 1 | 1 => 6 | 2 => 4 | 3 => 5 | 4 => 0 | 5 => 2 | 6 => 3
def pEPSL748 : Fin 7 → Fin 7 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 6 | 6 => 4
def pEPSL749 : Fin 7 → Fin 7 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 6 | 5 => 5 | 6 => 3
def pEPSL750 : Fin 7 → Fin 7 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 4 | 6 => 6
def pEPSL751 : Fin 7 → Fin 7 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 6 | 4 => 4 | 5 => 3 | 6 => 5
def pEPSL752 : Fin 7 → Fin 7 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 6 | 5 => 5 | 6 => 4
def pEPSL753 : Fin 7 → Fin 7 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 3
def pEPSL754 : Fin 7 → Fin 7 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 5 | 4 => 4 | 5 => 3 | 6 => 6
def pEPSL755 : Fin 7 → Fin 7 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 6 | 4 => 3 | 5 => 4 | 6 => 5
def pEPSL756 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 5 | 5 => 6 | 6 => 1
def pEPSL757 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 6 | 5 => 5 | 6 => 0
def pEPSL758 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 0 | 5 => 1 | 6 => 6
def pEPSL759 : Fin 7 → Fin 7 | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 6 | 4 => 1 | 5 => 0 | 6 => 5
def pEPSL760 : Fin 7 → Fin 7 | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 6 | 5 => 5 | 6 => 1
def pEPSL761 : Fin 7 → Fin 7 | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 6 | 6 => 0
def pEPSL762 : Fin 7 → Fin 7 | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 5 | 4 => 1 | 5 => 0 | 6 => 6
def pEPSL763 : Fin 7 → Fin 7 | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 6 | 4 => 0 | 5 => 1 | 6 => 5
def pEPSL764 : Fin 7 → Fin 7 | 0 => 2 | 1 => 5 | 2 => 6 | 3 => 0 | 4 => 3 | 5 => 4 | 6 => 1
def pEPSL765 : Fin 7 → Fin 7 | 0 => 2 | 1 => 5 | 2 => 6 | 3 => 1 | 4 => 4 | 5 => 3 | 6 => 0
def pEPSL766 : Fin 7 → Fin 7 | 0 => 2 | 1 => 5 | 2 => 6 | 3 => 3 | 4 => 0 | 5 => 1 | 6 => 4
def pEPSL767 : Fin 7 → Fin 7 | 0 => 2 | 1 => 5 | 2 => 6 | 3 => 4 | 4 => 1 | 5 => 0 | 6 => 3
def pEPSL768 : Fin 7 → Fin 7 | 0 => 2 | 1 => 6 | 2 => 5 | 3 => 0 | 4 => 4 | 5 => 3 | 6 => 1
def pEPSL769 : Fin 7 → Fin 7 | 0 => 2 | 1 => 6 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 4 | 6 => 0
def pEPSL770 : Fin 7 → Fin 7 | 0 => 2 | 1 => 6 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 0 | 6 => 4
def pEPSL771 : Fin 7 → Fin 7 | 0 => 2 | 1 => 6 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 1 | 6 => 3
def pEPSL772 : Fin 7 → Fin 7 | 0 => 3 | 1 => 0 | 2 => 6 | 3 => 1 | 4 => 4 | 5 => 2 | 6 => 5
def pEPSL773 : Fin 7 → Fin 7 | 0 => 3 | 1 => 0 | 2 => 6 | 3 => 2 | 4 => 5 | 5 => 1 | 6 => 4
def pEPSL774 : Fin 7 → Fin 7 | 0 => 3 | 1 => 0 | 2 => 6 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 2
def pEPSL775 : Fin 7 → Fin 7 | 0 => 3 | 1 => 0 | 2 => 6 | 3 => 5 | 4 => 2 | 5 => 4 | 6 => 1
def pEPSL776 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 5 | 3 => 0 | 4 => 4 | 5 => 2 | 6 => 6
def pEPSL777 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 5 | 3 => 2 | 4 => 6 | 5 => 0 | 6 => 4
def pEPSL778 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 2
def pEPSL779 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 5 | 3 => 6 | 4 => 2 | 5 => 4 | 6 => 0
def pEPSL780 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 5 | 5 => 1 | 6 => 6
def pEPSL781 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 6 | 5 => 0 | 6 => 5
def pEPSL782 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 5 | 4 => 0 | 5 => 6 | 6 => 1
def pEPSL783 : Fin 7 → Fin 7 | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 6 | 4 => 1 | 5 => 5 | 6 => 0
def pEPSL784 : Fin 7 → Fin 7 | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6
def pEPSL785 : Fin 7 → Fin 7 | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 5
def pEPSL786 : Fin 7 → Fin 7 | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 6 | 5 => 0 | 6 => 1
def pEPSL787 : Fin 7 → Fin 7 | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 6 | 4 => 5 | 5 => 1 | 6 => 0
def pEPSL788 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 4 | 6 => 6
def pEPSL789 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 4
def pEPSL790 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 1 | 3 => 4 | 4 => 6 | 5 => 0 | 6 => 2
def pEPSL791 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 1 | 3 => 6 | 4 => 4 | 5 => 2 | 6 => 0
def pEPSL792 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 4 | 6 => 5
def pEPSL793 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 4
def pEPSL794 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 1 | 6 => 2
def pEPSL795 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 0 | 3 => 5 | 4 => 4 | 5 => 2 | 6 => 1
def pEPSL796 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 2 | 6 => 6
def pEPSL797 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 5 | 3 => 2 | 4 => 6 | 5 => 1 | 6 => 3
def pEPSL798 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 2
def pEPSL799 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 5 | 3 => 6 | 4 => 2 | 5 => 3 | 6 => 1
def pEPSL7100 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 6 | 3 => 0 | 4 => 3 | 5 => 2 | 6 => 5
def pEPSL7101 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 6 | 3 => 2 | 4 => 5 | 5 => 0 | 6 => 3
def pEPSL7102 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 6 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 2
def pEPSL7103 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 6 | 3 => 5 | 4 => 2 | 5 => 3 | 6 => 0
def pEPSL7104 : Fin 7 → Fin 7 | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 6 | 5 => 1 | 6 => 5
def pEPSL7105 : Fin 7 → Fin 7 | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 0 | 6 => 6
def pEPSL7106 : Fin 7 → Fin 7 | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 5 | 4 => 1 | 5 => 6 | 6 => 0
def pEPSL7107 : Fin 7 → Fin 7 | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 6 | 4 => 0 | 5 => 5 | 6 => 1
def pEPSL7108 : Fin 7 → Fin 7 | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 5
def pEPSL7109 : Fin 7 → Fin 7 | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6
def pEPSL7110 : Fin 7 → Fin 7 | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 5 | 4 => 6 | 5 => 1 | 6 => 0
def pEPSL7111 : Fin 7 → Fin 7 | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 6 | 4 => 5 | 5 => 0 | 6 => 1
def pEPSL7112 : Fin 7 → Fin 7 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3 | 6 => 6
def pEPSL7113 : Fin 7 → Fin 7 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 3
def pEPSL7114 : Fin 7 → Fin 7 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 6 | 5 => 1 | 6 => 2
def pEPSL7115 : Fin 7 → Fin 7 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 6 | 4 => 3 | 5 => 2 | 6 => 1
def pEPSL7116 : Fin 7 → Fin 7 | 0 => 4 | 1 => 6 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 3 | 6 => 5
def pEPSL7117 : Fin 7 → Fin 7 | 0 => 4 | 1 => 6 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 3
def pEPSL7118 : Fin 7 → Fin 7 | 0 => 4 | 1 => 6 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 0 | 6 => 2
def pEPSL7119 : Fin 7 → Fin 7 | 0 => 4 | 1 => 6 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 2 | 6 => 0
def pEPSL7120 : Fin 7 → Fin 7 | 0 => 5 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 6 | 5 => 2 | 6 => 3
def pEPSL7121 : Fin 7 → Fin 7 | 0 => 5 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 1 | 6 => 6
def pEPSL7122 : Fin 7 → Fin 7 | 0 => 5 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 1
def pEPSL7123 : Fin 7 → Fin 7 | 0 => 5 | 1 => 0 | 2 => 4 | 3 => 6 | 4 => 1 | 5 => 3 | 6 => 2
def pEPSL7124 : Fin 7 → Fin 7 | 0 => 5 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 6 | 5 => 2 | 6 => 4
def pEPSL7125 : Fin 7 → Fin 7 | 0 => 5 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 0 | 6 => 6
def pEPSL7126 : Fin 7 → Fin 7 | 0 => 5 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 0
def pEPSL7127 : Fin 7 → Fin 7 | 0 => 5 | 1 => 1 | 2 => 3 | 3 => 6 | 4 => 0 | 5 => 4 | 6 => 2
def pEPSL7128 : Fin 7 → Fin 7 | 0 => 5 | 1 => 2 | 2 => 6 | 3 => 0 | 4 => 3 | 5 => 1 | 6 => 4
def pEPSL7129 : Fin 7 → Fin 7 | 0 => 5 | 1 => 2 | 2 => 6 | 3 => 1 | 4 => 4 | 5 => 0 | 6 => 3
def pEPSL7130 : Fin 7 → Fin 7 | 0 => 5 | 1 => 2 | 2 => 6 | 3 => 3 | 4 => 0 | 5 => 4 | 6 => 1
def pEPSL7131 : Fin 7 → Fin 7 | 0 => 5 | 1 => 2 | 2 => 6 | 3 => 4 | 4 => 1 | 5 => 3 | 6 => 0
def pEPSL7132 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 4
def pEPSL7133 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 4 | 6 => 6
def pEPSL7134 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 6 | 5 => 2 | 6 => 0
def pEPSL7135 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 1 | 3 => 6 | 4 => 4 | 5 => 0 | 6 => 2
def pEPSL7136 : Fin 7 → Fin 7 | 0 => 5 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 3
def pEPSL7137 : Fin 7 → Fin 7 | 0 => 5 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 3 | 6 => 6
def pEPSL7138 : Fin 7 → Fin 7 | 0 => 5 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 6 | 5 => 2 | 6 => 1
def pEPSL7139 : Fin 7 → Fin 7 | 0 => 5 | 1 => 4 | 2 => 0 | 3 => 6 | 4 => 3 | 5 => 1 | 6 => 2
def pEPSL7140 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 3 | 6 => 4
def pEPSL7141 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 4 | 6 => 3
def pEPSL7142 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 0 | 6 => 1
def pEPSL7143 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 1 | 6 => 0
def pEPSL7144 : Fin 7 → Fin 7 | 0 => 6 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 2 | 6 => 4
def pEPSL7145 : Fin 7 → Fin 7 | 0 => 6 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 1 | 6 => 5
def pEPSL7146 : Fin 7 → Fin 7 | 0 => 6 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 1
def pEPSL7147 : Fin 7 → Fin 7 | 0 => 6 | 1 => 0 | 2 => 3 | 3 => 5 | 4 => 1 | 5 => 4 | 6 => 2
def pEPSL7148 : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 5 | 5 => 2 | 6 => 3
def pEPSL7149 : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 0 | 6 => 5
def pEPSL7150 : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 0
def pEPSL7151 : Fin 7 → Fin 7 | 0 => 6 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 0 | 5 => 3 | 6 => 2
def pEPSL7152 : Fin 7 → Fin 7 | 0 => 6 | 1 => 2 | 2 => 5 | 3 => 0 | 4 => 4 | 5 => 1 | 6 => 3
def pEPSL7153 : Fin 7 → Fin 7 | 0 => 6 | 1 => 2 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 0 | 6 => 4
def pEPSL7154 : Fin 7 → Fin 7 | 0 => 6 | 1 => 2 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 4 | 6 => 0
def pEPSL7155 : Fin 7 → Fin 7 | 0 => 6 | 1 => 2 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 3 | 6 => 1
def pEPSL7156 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 4
def pEPSL7157 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 4 | 6 => 5
def pEPSL7158 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 2 | 6 => 1
def pEPSL7159 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 0 | 3 => 5 | 4 => 4 | 5 => 1 | 6 => 2
def pEPSL7160 : Fin 7 → Fin 7 | 0 => 6 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 3
def pEPSL7161 : Fin 7 → Fin 7 | 0 => 6 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 3 | 6 => 5
def pEPSL7162 : Fin 7 → Fin 7 | 0 => 6 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 2 | 6 => 0
def pEPSL7163 : Fin 7 → Fin 7 | 0 => 6 | 1 => 4 | 2 => 1 | 3 => 5 | 4 => 3 | 5 => 0 | 6 => 2
def pEPSL7164 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 4 | 6 => 3
def pEPSL7165 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 3 | 6 => 4
def pEPSL7166 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 1 | 6 => 0
def pEPSL7167 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 0 | 6 => 1

def permEPSL7 : Fin 168 → Fin 7 → Fin 7
  | 0 => pEPSL70
  | 1 => pEPSL71
  | 2 => pEPSL72
  | 3 => pEPSL73
  | 4 => pEPSL74
  | 5 => pEPSL75
  | 6 => pEPSL76
  | 7 => pEPSL77
  | 8 => pEPSL78
  | 9 => pEPSL79
  | 10 => pEPSL710
  | 11 => pEPSL711
  | 12 => pEPSL712
  | 13 => pEPSL713
  | 14 => pEPSL714
  | 15 => pEPSL715
  | 16 => pEPSL716
  | 17 => pEPSL717
  | 18 => pEPSL718
  | 19 => pEPSL719
  | 20 => pEPSL720
  | 21 => pEPSL721
  | 22 => pEPSL722
  | 23 => pEPSL723
  | 24 => pEPSL724
  | 25 => pEPSL725
  | 26 => pEPSL726
  | 27 => pEPSL727
  | 28 => pEPSL728
  | 29 => pEPSL729
  | 30 => pEPSL730
  | 31 => pEPSL731
  | 32 => pEPSL732
  | 33 => pEPSL733
  | 34 => pEPSL734
  | 35 => pEPSL735
  | 36 => pEPSL736
  | 37 => pEPSL737
  | 38 => pEPSL738
  | 39 => pEPSL739
  | 40 => pEPSL740
  | 41 => pEPSL741
  | 42 => pEPSL742
  | 43 => pEPSL743
  | 44 => pEPSL744
  | 45 => pEPSL745
  | 46 => pEPSL746
  | 47 => pEPSL747
  | 48 => pEPSL748
  | 49 => pEPSL749
  | 50 => pEPSL750
  | 51 => pEPSL751
  | 52 => pEPSL752
  | 53 => pEPSL753
  | 54 => pEPSL754
  | 55 => pEPSL755
  | 56 => pEPSL756
  | 57 => pEPSL757
  | 58 => pEPSL758
  | 59 => pEPSL759
  | 60 => pEPSL760
  | 61 => pEPSL761
  | 62 => pEPSL762
  | 63 => pEPSL763
  | 64 => pEPSL764
  | 65 => pEPSL765
  | 66 => pEPSL766
  | 67 => pEPSL767
  | 68 => pEPSL768
  | 69 => pEPSL769
  | 70 => pEPSL770
  | 71 => pEPSL771
  | 72 => pEPSL772
  | 73 => pEPSL773
  | 74 => pEPSL774
  | 75 => pEPSL775
  | 76 => pEPSL776
  | 77 => pEPSL777
  | 78 => pEPSL778
  | 79 => pEPSL779
  | 80 => pEPSL780
  | 81 => pEPSL781
  | 82 => pEPSL782
  | 83 => pEPSL783
  | 84 => pEPSL784
  | 85 => pEPSL785
  | 86 => pEPSL786
  | 87 => pEPSL787
  | 88 => pEPSL788
  | 89 => pEPSL789
  | 90 => pEPSL790
  | 91 => pEPSL791
  | 92 => pEPSL792
  | 93 => pEPSL793
  | 94 => pEPSL794
  | 95 => pEPSL795
  | 96 => pEPSL796
  | 97 => pEPSL797
  | 98 => pEPSL798
  | 99 => pEPSL799
  | 100 => pEPSL7100
  | 101 => pEPSL7101
  | 102 => pEPSL7102
  | 103 => pEPSL7103
  | 104 => pEPSL7104
  | 105 => pEPSL7105
  | 106 => pEPSL7106
  | 107 => pEPSL7107
  | 108 => pEPSL7108
  | 109 => pEPSL7109
  | 110 => pEPSL7110
  | 111 => pEPSL7111
  | 112 => pEPSL7112
  | 113 => pEPSL7113
  | 114 => pEPSL7114
  | 115 => pEPSL7115
  | 116 => pEPSL7116
  | 117 => pEPSL7117
  | 118 => pEPSL7118
  | 119 => pEPSL7119
  | 120 => pEPSL7120
  | 121 => pEPSL7121
  | 122 => pEPSL7122
  | 123 => pEPSL7123
  | 124 => pEPSL7124
  | 125 => pEPSL7125
  | 126 => pEPSL7126
  | 127 => pEPSL7127
  | 128 => pEPSL7128
  | 129 => pEPSL7129
  | 130 => pEPSL7130
  | 131 => pEPSL7131
  | 132 => pEPSL7132
  | 133 => pEPSL7133
  | 134 => pEPSL7134
  | 135 => pEPSL7135
  | 136 => pEPSL7136
  | 137 => pEPSL7137
  | 138 => pEPSL7138
  | 139 => pEPSL7139
  | 140 => pEPSL7140
  | 141 => pEPSL7141
  | 142 => pEPSL7142
  | 143 => pEPSL7143
  | 144 => pEPSL7144
  | 145 => pEPSL7145
  | 146 => pEPSL7146
  | 147 => pEPSL7147
  | 148 => pEPSL7148
  | 149 => pEPSL7149
  | 150 => pEPSL7150
  | 151 => pEPSL7151
  | 152 => pEPSL7152
  | 153 => pEPSL7153
  | 154 => pEPSL7154
  | 155 => pEPSL7155
  | 156 => pEPSL7156
  | 157 => pEPSL7157
  | 158 => pEPSL7158
  | 159 => pEPSL7159
  | 160 => pEPSL7160
  | 161 => pEPSL7161
  | 162 => pEPSL7162
  | 163 => pEPSL7163
  | 164 => pEPSL7164
  | 165 => pEPSL7165
  | 166 => pEPSL7166
  | _ => pEPSL7167

def permEinvPSL7 : Fin 168 → Fin 7 → Fin 7
  | 0 => pEPSL70
  | 1 => pEPSL71
  | 2 => pEPSL72
  | 3 => pEPSL73
  | 4 => pEPSL74
  | 5 => pEPSL76
  | 6 => pEPSL75
  | 7 => pEPSL77
  | 8 => pEPSL78
  | 9 => pEPSL720
  | 10 => pEPSL712
  | 11 => pEPSL716
  | 12 => pEPSL710
  | 13 => pEPSL723
  | 14 => pEPSL714
  | 15 => pEPSL719
  | 16 => pEPSL711
  | 17 => pEPSL722
  | 18 => pEPSL718
  | 19 => pEPSL715
  | 20 => pEPSL79
  | 21 => pEPSL721
  | 22 => pEPSL717
  | 23 => pEPSL713
  | 24 => pEPSL724
  | 25 => pEPSL725
  | 26 => pEPSL727
  | 27 => pEPSL726
  | 28 => pEPSL748
  | 29 => pEPSL750
  | 30 => pEPSL751
  | 31 => pEPSL749
  | 32 => pEPSL772
  | 33 => pEPSL7144
  | 34 => pEPSL796
  | 35 => pEPSL7120
  | 36 => pEPSL774
  | 37 => pEPSL7147
  | 38 => pEPSL798
  | 39 => pEPSL7123
  | 40 => pEPSL773
  | 41 => pEPSL7145
  | 42 => pEPSL7121
  | 43 => pEPSL797
  | 44 => pEPSL775
  | 45 => pEPSL7146
  | 46 => pEPSL7122
  | 47 => pEPSL799
  | 48 => pEPSL728
  | 49 => pEPSL731
  | 50 => pEPSL729
  | 51 => pEPSL730
  | 52 => pEPSL752
  | 53 => pEPSL755
  | 54 => pEPSL754
  | 55 => pEPSL753
  | 56 => pEPSL792
  | 57 => pEPSL7156
  | 58 => pEPSL7112
  | 59 => pEPSL7136
  | 60 => pEPSL793
  | 61 => pEPSL7157
  | 62 => pEPSL7137
  | 63 => pEPSL7113
  | 64 => pEPSL794
  | 65 => pEPSL7159
  | 66 => pEPSL7114
  | 67 => pEPSL7139
  | 68 => pEPSL795
  | 69 => pEPSL7158
  | 70 => pEPSL7138
  | 71 => pEPSL7115
  | 72 => pEPSL732
  | 73 => pEPSL740
  | 74 => pEPSL736
  | 75 => pEPSL744
  | 76 => pEPSL776
  | 77 => pEPSL7124
  | 78 => pEPSL7100
  | 79 => pEPSL7148
  | 80 => pEPSL788
  | 81 => pEPSL7132
  | 82 => pEPSL7116
  | 83 => pEPSL7160
  | 84 => pEPSL784
  | 85 => pEPSL7108
  | 86 => pEPSL7140
  | 87 => pEPSL7164
  | 88 => pEPSL780
  | 89 => pEPSL7104
  | 90 => pEPSL7128
  | 91 => pEPSL7152
  | 92 => pEPSL756
  | 93 => pEPSL760
  | 94 => pEPSL764
  | 95 => pEPSL768
  | 96 => pEPSL734
  | 97 => pEPSL743
  | 98 => pEPSL738
  | 99 => pEPSL747
  | 100 => pEPSL778
  | 101 => pEPSL7127
  | 102 => pEPSL7102
  | 103 => pEPSL7151
  | 104 => pEPSL789
  | 105 => pEPSL7133
  | 106 => pEPSL7161
  | 107 => pEPSL7117
  | 108 => pEPSL785
  | 109 => pEPSL7109
  | 110 => pEPSL7165
  | 111 => pEPSL7141
  | 112 => pEPSL758
  | 113 => pEPSL763
  | 114 => pEPSL766
  | 115 => pEPSL771
  | 116 => pEPSL782
  | 117 => pEPSL7107
  | 118 => pEPSL7130
  | 119 => pEPSL7155
  | 120 => pEPSL735
  | 121 => pEPSL742
  | 122 => pEPSL746
  | 123 => pEPSL739
  | 124 => pEPSL777
  | 125 => pEPSL7125
  | 126 => pEPSL7149
  | 127 => pEPSL7101
  | 128 => pEPSL790
  | 129 => pEPSL7135
  | 130 => pEPSL7118
  | 131 => pEPSL7163
  | 132 => pEPSL781
  | 133 => pEPSL7105
  | 134 => pEPSL7153
  | 135 => pEPSL7129
  | 136 => pEPSL759
  | 137 => pEPSL762
  | 138 => pEPSL770
  | 139 => pEPSL767
  | 140 => pEPSL786
  | 141 => pEPSL7111
  | 142 => pEPSL7142
  | 143 => pEPSL7167
  | 144 => pEPSL733
  | 145 => pEPSL741
  | 146 => pEPSL745
  | 147 => pEPSL737
  | 148 => pEPSL779
  | 149 => pEPSL7126
  | 150 => pEPSL7150
  | 151 => pEPSL7103
  | 152 => pEPSL791
  | 153 => pEPSL7134
  | 154 => pEPSL7162
  | 155 => pEPSL7119
  | 156 => pEPSL757
  | 157 => pEPSL761
  | 158 => pEPSL769
  | 159 => pEPSL765
  | 160 => pEPSL783
  | 161 => pEPSL7106
  | 162 => pEPSL7154
  | 163 => pEPSL7131
  | 164 => pEPSL787
  | 165 => pEPSL7110
  | 166 => pEPSL7166
  | _ => pEPSL7143

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eEPSL7 (i : Fin 168) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permEPSL7 i) (permEinvPSL7 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 3)(4 6)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXPSL70 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 6 | 5 => 5 | 6 => 4
def pXPSL70inv : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 6 | 5 => 5 | 6 => 4

def permXPSL7 : Fin 1 → Fin 7 → Fin 7
  | 0 => pXPSL70

def permXinvPSL7 : Fin 1 → Fin 7 → Fin 7
  | 0 => pXPSL70inv

def eXPSL7 (i : Fin 1) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permXPSL7 i) (permXinvPSL7 i) (by revert i; decide)

/-- One representative per orbit of the group on the `49` cells; there are `2`, so an invariant
operation is `2` values. -/
def repPSL7 : Fin 2 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trPSL7 : Fin 7 → Fin 7 → Fin 2 × Fin 168
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 4)
  | 0, 3 => (1, 8)
  | 0, 4 => (1, 12)
  | 0, 5 => (1, 16)
  | 0, 6 => (1, 20)
  | 1, 0 => (1, 24)
  | 1, 1 => (0, 24)
  | 1, 2 => (1, 28)
  | 1, 3 => (1, 32)
  | 1, 4 => (1, 36)
  | 1, 5 => (1, 40)
  | 1, 6 => (1, 44)
  | 2, 0 => (1, 48)
  | 2, 1 => (1, 52)
  | 2, 2 => (0, 48)
  | 2, 3 => (1, 56)
  | 2, 4 => (1, 60)
  | 2, 5 => (1, 64)
  | 2, 6 => (1, 68)
  | 3, 0 => (1, 72)
  | 3, 1 => (1, 76)
  | 3, 2 => (1, 80)
  | 3, 3 => (0, 72)
  | 3, 4 => (1, 84)
  | 3, 5 => (1, 88)
  | 3, 6 => (1, 92)
  | 4, 0 => (1, 96)
  | 4, 1 => (1, 100)
  | 4, 2 => (1, 104)
  | 4, 3 => (1, 108)
  | 4, 4 => (0, 96)
  | 4, 5 => (1, 112)
  | 4, 6 => (1, 116)
  | 5, 0 => (1, 120)
  | 5, 1 => (1, 124)
  | 5, 2 => (1, 128)
  | 5, 3 => (1, 132)
  | 5, 4 => (1, 136)
  | 5, 5 => (0, 120)
  | 5, 6 => (1, 140)
  | 6, 0 => (1, 144)
  | 6, 1 => (1, 148)
  | 6, 2 => (1, 152)
  | 6, 3 => (1, 156)
  | 6, 4 => (1, 160)
  | 6, 5 => (1, 164)
  | 6, 6 => (0, 144)

/-- The `24` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxPSL70 : Fin 24 → Fin 168
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 9
  | 10 => 10
  | 11 => 11
  | 12 => 12
  | 13 => 13
  | 14 => 14
  | 15 => 15
  | 16 => 16
  | 17 => 17
  | 18 => 18
  | 19 => 19
  | 20 => 20
  | 21 => 21
  | 22 => 22
  | _ => 23
def valPSL70 : Fin 1 → Fin 7
  | 0 => 0

/-- The `4` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxPSL71 : Fin 4 → Fin 168
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valPSL71 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The `2` orbit values named by the family's arguments. -/
def decPSL7 (a : Fin 1) (b : Fin 3) : Fin 2 → Fin 7
  | 0 => valPSL70 a
  | 1 => valPSL71 b

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabPSL7_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabPSL7 (a : Fin 1) (b : Fin 3) : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => valPSL70 a
  | 0, 1 => valPSL71 b
  | 0, 2 => pEPSL74 (valPSL71 b)
  | 0, 3 => pEPSL78 (valPSL71 b)
  | 0, 4 => pEPSL712 (valPSL71 b)
  | 0, 5 => pEPSL716 (valPSL71 b)
  | 0, 6 => pEPSL720 (valPSL71 b)
  | 1, 0 => pEPSL724 (valPSL71 b)
  | 1, 1 => pEPSL724 (valPSL70 a)
  | 1, 2 => pEPSL728 (valPSL71 b)
  | 1, 3 => pEPSL732 (valPSL71 b)
  | 1, 4 => pEPSL736 (valPSL71 b)
  | 1, 5 => pEPSL740 (valPSL71 b)
  | 1, 6 => pEPSL744 (valPSL71 b)
  | 2, 0 => pEPSL748 (valPSL71 b)
  | 2, 1 => pEPSL752 (valPSL71 b)
  | 2, 2 => pEPSL748 (valPSL70 a)
  | 2, 3 => pEPSL756 (valPSL71 b)
  | 2, 4 => pEPSL760 (valPSL71 b)
  | 2, 5 => pEPSL764 (valPSL71 b)
  | 2, 6 => pEPSL768 (valPSL71 b)
  | 3, 0 => pEPSL772 (valPSL71 b)
  | 3, 1 => pEPSL776 (valPSL71 b)
  | 3, 2 => pEPSL780 (valPSL71 b)
  | 3, 3 => pEPSL772 (valPSL70 a)
  | 3, 4 => pEPSL784 (valPSL71 b)
  | 3, 5 => pEPSL788 (valPSL71 b)
  | 3, 6 => pEPSL792 (valPSL71 b)
  | 4, 0 => pEPSL796 (valPSL71 b)
  | 4, 1 => pEPSL7100 (valPSL71 b)
  | 4, 2 => pEPSL7104 (valPSL71 b)
  | 4, 3 => pEPSL7108 (valPSL71 b)
  | 4, 4 => pEPSL796 (valPSL70 a)
  | 4, 5 => pEPSL7112 (valPSL71 b)
  | 4, 6 => pEPSL7116 (valPSL71 b)
  | 5, 0 => pEPSL7120 (valPSL71 b)
  | 5, 1 => pEPSL7124 (valPSL71 b)
  | 5, 2 => pEPSL7128 (valPSL71 b)
  | 5, 3 => pEPSL7132 (valPSL71 b)
  | 5, 4 => pEPSL7136 (valPSL71 b)
  | 5, 5 => pEPSL7120 (valPSL70 a)
  | 5, 6 => pEPSL7140 (valPSL71 b)
  | 6, 0 => pEPSL7144 (valPSL71 b)
  | 6, 1 => pEPSL7148 (valPSL71 b)
  | 6, 2 => pEPSL7152 (valPSL71 b)
  | 6, 3 => pEPSL7156 (valPSL71 b)
  | 6, 4 => pEPSL7160 (valPSL71 b)
  | 6, 5 => pEPSL7164 (valPSL71 b)
  | 6, 6 => pEPSL7144 (valPSL70 a)

theorem tabPSL7_eq_transport (a : Fin 1) (b : Fin 3) :
    tabPSL7 a b = Magma.transport permEPSL7 trPSL7 (decPSL7 a b) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `1` magmas on `Fin 7` whose automorphism group is exactly this group, listed under one
index. Of the `3` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memPSL7 : Fin 1 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabPSL7 0 2

/-- Which of the `1` members a given invariant tuple is, so that `mem_of_isExactPSL7` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrPSL7 : Array Nat := #[
  0, 0, 0]

/-- The arguments as one mixed-radix index, which is how `rankArrPSL7` is addressed. -/
def encTPSL7 (a : Fin 1) (b : Fin 3) : Nat :=
  a.1 * 3 +
    b.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankPSL7 (a : Fin 1) (b : Fin 3) : Fin 1 :=
  ⟨min (rankArrPSL7.getD (encTPSL7 a b) 0) 0, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactPSL7 (i : Fin 1) : Magma (Fin 7) := Magma.mk (memPSL7 i)

theorem exactPSL7_isEndo (i : Fin 1) (j : Fin 168) : (exactPSL7 i).IsEndo ⇑(eEPSL7 j) := by
  simp only [eEPSL7, coe_permOf]; revert i j; native_decide

theorem exactPSL7_not_isEndo (i : Fin 1) (j : Fin 1) : ¬ (exactPSL7 i).IsEndo ⇑(eXPSL7 j) := by
  simp only [eXPSL7, coe_permOf]; revert i j; native_decide

/-- `rankPSL7` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memPSL7` for the index would be a comparison per tuple and
member. -/
theorem mem_rankPSL7 (a : Fin 1) (b : Fin 3)
    (h : Magma.isExact (tabPSL7 a b) permEPSL7 permXPSL7 = true) :
    memPSL7 (rankPSL7 a b) = tabPSL7 a b := by
  revert h; revert a b; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `1` listed
members. -/
theorem mem_of_isExactPSL7 (a : Fin 1) (b : Fin 3)
    (h : Magma.isExact (tabPSL7 a b) permEPSL7 permXPSL7 = true) :
    ∃ i, memPSL7 i = tabPSL7 a b :=
  ⟨_, mem_rankPSL7 a b h⟩

/-- A magma on `Fin 7` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactPSL7`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactPSL7` turns that into a member index. -/
theorem exists_exactPSL7 {M : Magma (Fin 7)} (hE : ∀ i, M.IsEndo ⇑(eEPSL7 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXPSL7 i)) : ∃ i, exactPSL7 i = M := by
  simp only [eEPSL7, coe_permOf] at hE
  simp only [eXPSL7, coe_permOf] at hX
  have hop : M.op = Magma.transport permEPSL7 trPSL7 (fun i ↦ M.op (repPSL7 i).1 (repPSL7 i).2) :=
    Magma.op_eq_transport (rep := repPSL7) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permEPSL7) (idx := stabIdxPSL70) (a := (repPSL7 0).1) (b := (repPSL7 0).2)
    (val := valPSL70) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permEPSL7) (idx := stabIdxPSL71) (a := (repPSL7 1).1) (b := (repPSL7 1).2)
    (val := valPSL71) hE (by decide) (by decide)
  have hdec : decPSL7 a b = fun i ↦ M.op (repPSL7 i).1 (repPSL7 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
  have key : tabPSL7 a b = M.op := by
    rw [tabPSL7_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabPSL7 a b) permEPSL7 permXPSL7 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactPSL7 a b hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose automorphism
group is exactly the order-`168` group of `Magma.permEPSL7`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactPSL7 {L L' : Law.NatMagmaLaw} {i : Fin 1}
    (hsrc : @satisfies _ (Fin 7) (Magma.exactPSL7 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.exactPSL7 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactPSL7 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactPSL7
    (fun k ↦ (Magma.exactPSL7_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactPSL7_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw

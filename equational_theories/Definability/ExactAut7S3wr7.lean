import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `S3wr7` on `Fin 7`

One class of `Definability/ExactAut7.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`72` group `⟨(0 1 4)(3 5 6), (0 1 4)(3 6 5), (0 3)(1 5)(4 6), (0 3)(1 5 4 6)⟩` -/

/-- The `72` elements of the group: `()`, `(5 6)`, `(3 5)`, `(3 5 6)`, `(3 6 5)`, `(3 6)`, `(1 4)`,
`(1 4)(5 6)`, `(1 4)(3 5)`, `(1 4)(3 5 6)`, `(1 4)(3 6 5)`, `(1 4)(3 6)`, `(0 1)`, `(0 1)(5 6)`, `(0
1)(3 5)`, `(0 1)(3 5 6)`, `(0 1)(3 6 5)`, `(0 1)(3 6)`, `(0 1 4)`, `(0 1 4)(5 6)`, `(0 1 4)(3 5)`,
`(0 1 4)(3 5 6)`, `(0 1 4)(3 6 5)`, `(0 1 4)(3 6)`, `(0 3)(1 5)(4 6)`, `(0 3)(1 5 4 6)`, `(0 3 1
5)(4 6)`, `(0 3 1 5 4 6)`, `(0 3 4 6 1 5)`, `(0 3 4 6)(1 5)`, `(0 3)(1 6 4 5)`, `(0 3)(1 6)(4 5)`,
`(0 3 1 6 4 5)`, `(0 3 1 6)(4 5)`, `(0 3 4 5)(1 6)`, `(0 3 4 5 1 6)`, `(0 4 1)`, `(0 4 1)(5 6)`, `(0
4 1)(3 5)`, `(0 4 1)(3 5 6)`, `(0 4 1)(3 6 5)`, `(0 4 1)(3 6)`, `(0 4)`, `(0 4)(5 6)`, `(0 4)(3 5)`,
`(0 4)(3 5 6)`, `(0 4)(3 6 5)`, `(0 4)(3 6)`, `(0 5 1 3)(4 6)`, `(0 5 4 6 1 3)`, `(0 5)(1 3)(4 6)`,
`(0 5 4 6)(1 3)`, `(0 5)(1 3 4 6)`, `(0 5 1 3 4 6)`, `(0 5 1 6 4 3)`, `(0 5 4 3)(1 6)`, `(0 5)(1 6 4
3)`, `(0 5 4 3 1 6)`, `(0 5)(1 6)(3 4)`, `(0 5 1 6)(3 4)`, `(0 6 4 5 1 3)`, `(0 6 1 3)(4 5)`, `(0 6
4 5)(1 3)`, `(0 6)(1 3)(4 5)`, `(0 6 1 3 4 5)`, `(0 6)(1 3 4 5)`, `(0 6 4 3)(1 5)`, `(0 6 1 5 4 3)`,
`(0 6 4 3 1 5)`, `(0 6)(1 5 4 3)`, `(0 6 1 5)(3 4)`, `(0 6)(1 5)(3 4)`. -/
def pES3wr70 : Fin 7 → Fin 7 := id
def pES3wr71 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5
def pES3wr72 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3 | 6 => 6
def pES3wr73 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 6 | 6 => 3
def pES3wr74 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 4 | 5 => 3 | 6 => 5
def pES3wr75 : Fin 7 → Fin 7 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 4 | 5 => 5 | 6 => 3
def pES3wr76 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6
def pES3wr77 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5
def pES3wr78 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 1 | 5 => 3 | 6 => 6
def pES3wr79 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 1 | 5 => 6 | 6 => 3
def pES3wr710 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 6 | 4 => 1 | 5 => 3 | 6 => 5
def pES3wr711 : Fin 7 → Fin 7 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 6 | 4 => 1 | 5 => 5 | 6 => 3
def pES3wr712 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6
def pES3wr713 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5
def pES3wr714 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3 | 6 => 6
def pES3wr715 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 6 | 6 => 3
def pES3wr716 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 6 | 4 => 4 | 5 => 3 | 6 => 5
def pES3wr717 : Fin 7 → Fin 7 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 6 | 4 => 4 | 5 => 5 | 6 => 3
def pES3wr718 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 6
def pES3wr719 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 5
def pES3wr720 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 0 | 5 => 3 | 6 => 6
def pES3wr721 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 0 | 5 => 6 | 6 => 3
def pES3wr722 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 6 | 4 => 0 | 5 => 3 | 6 => 5
def pES3wr723 : Fin 7 → Fin 7 | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 6 | 4 => 0 | 5 => 5 | 6 => 3
def pES3wr724 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 2 | 3 => 0 | 4 => 6 | 5 => 1 | 6 => 4
def pES3wr725 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 2 | 3 => 0 | 4 => 6 | 5 => 4 | 6 => 1
def pES3wr726 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 0 | 6 => 4
def pES3wr727 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 4 | 6 => 0
def pES3wr728 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 2 | 3 => 4 | 4 => 6 | 5 => 0 | 6 => 1
def pES3wr729 : Fin 7 → Fin 7 | 0 => 3 | 1 => 5 | 2 => 2 | 3 => 4 | 4 => 6 | 5 => 1 | 6 => 0
def pES3wr730 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 1 | 6 => 4
def pES3wr731 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 4 | 6 => 1
def pES3wr732 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 0 | 6 => 4
def pES3wr733 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 0
def pES3wr734 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 0 | 6 => 1
def pES3wr735 : Fin 7 → Fin 7 | 0 => 3 | 1 => 6 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 1 | 6 => 0
def pES3wr736 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6
def pES3wr737 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5
def pES3wr738 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 1 | 5 => 3 | 6 => 6
def pES3wr739 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 5 | 4 => 1 | 5 => 6 | 6 => 3
def pES3wr740 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 6 | 4 => 1 | 5 => 3 | 6 => 5
def pES3wr741 : Fin 7 → Fin 7 | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 6 | 4 => 1 | 5 => 5 | 6 => 3
def pES3wr742 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 6
def pES3wr743 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 5
def pES3wr744 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 0 | 5 => 3 | 6 => 6
def pES3wr745 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 0 | 5 => 6 | 6 => 3
def pES3wr746 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 0 | 5 => 3 | 6 => 5
def pES3wr747 : Fin 7 → Fin 7 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 0 | 5 => 5 | 6 => 3
def pES3wr748 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 6 | 5 => 1 | 6 => 4
def pES3wr749 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 6 | 5 => 4 | 6 => 1
def pES3wr750 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 0 | 6 => 4
def pES3wr751 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 4 | 6 => 0
def pES3wr752 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 6 | 5 => 0 | 6 => 1
def pES3wr753 : Fin 7 → Fin 7 | 0 => 5 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 6 | 5 => 1 | 6 => 0
def pES3wr754 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 1 | 6 => 4
def pES3wr755 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 4 | 6 => 1
def pES3wr756 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 0 | 6 => 4
def pES3wr757 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 4 | 6 => 0
def pES3wr758 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 0 | 6 => 1
def pES3wr759 : Fin 7 → Fin 7 | 0 => 5 | 1 => 6 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 1 | 6 => 0
def pES3wr760 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 1 | 6 => 4
def pES3wr761 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 5 | 5 => 4 | 6 => 1
def pES3wr762 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 0 | 6 => 4
def pES3wr763 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 0
def pES3wr764 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 0 | 6 => 1
def pES3wr765 : Fin 7 → Fin 7 | 0 => 6 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 1 | 6 => 0
def pES3wr766 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 1 | 6 => 4
def pES3wr767 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 4 | 6 => 1
def pES3wr768 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 0 | 6 => 4
def pES3wr769 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 4 | 6 => 0
def pES3wr770 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 0 | 6 => 1
def pES3wr771 : Fin 7 → Fin 7 | 0 => 6 | 1 => 5 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 1 | 6 => 0

def permES3wr7 : Fin 72 → Fin 7 → Fin 7
  | 0 => pES3wr70
  | 1 => pES3wr71
  | 2 => pES3wr72
  | 3 => pES3wr73
  | 4 => pES3wr74
  | 5 => pES3wr75
  | 6 => pES3wr76
  | 7 => pES3wr77
  | 8 => pES3wr78
  | 9 => pES3wr79
  | 10 => pES3wr710
  | 11 => pES3wr711
  | 12 => pES3wr712
  | 13 => pES3wr713
  | 14 => pES3wr714
  | 15 => pES3wr715
  | 16 => pES3wr716
  | 17 => pES3wr717
  | 18 => pES3wr718
  | 19 => pES3wr719
  | 20 => pES3wr720
  | 21 => pES3wr721
  | 22 => pES3wr722
  | 23 => pES3wr723
  | 24 => pES3wr724
  | 25 => pES3wr725
  | 26 => pES3wr726
  | 27 => pES3wr727
  | 28 => pES3wr728
  | 29 => pES3wr729
  | 30 => pES3wr730
  | 31 => pES3wr731
  | 32 => pES3wr732
  | 33 => pES3wr733
  | 34 => pES3wr734
  | 35 => pES3wr735
  | 36 => pES3wr736
  | 37 => pES3wr737
  | 38 => pES3wr738
  | 39 => pES3wr739
  | 40 => pES3wr740
  | 41 => pES3wr741
  | 42 => pES3wr742
  | 43 => pES3wr743
  | 44 => pES3wr744
  | 45 => pES3wr745
  | 46 => pES3wr746
  | 47 => pES3wr747
  | 48 => pES3wr748
  | 49 => pES3wr749
  | 50 => pES3wr750
  | 51 => pES3wr751
  | 52 => pES3wr752
  | 53 => pES3wr753
  | 54 => pES3wr754
  | 55 => pES3wr755
  | 56 => pES3wr756
  | 57 => pES3wr757
  | 58 => pES3wr758
  | 59 => pES3wr759
  | 60 => pES3wr760
  | 61 => pES3wr761
  | 62 => pES3wr762
  | 63 => pES3wr763
  | 64 => pES3wr764
  | 65 => pES3wr765
  | 66 => pES3wr766
  | 67 => pES3wr767
  | 68 => pES3wr768
  | 69 => pES3wr769
  | 70 => pES3wr770
  | _ => pES3wr771

def permEinvS3wr7 : Fin 72 → Fin 7 → Fin 7
  | 0 => pES3wr70
  | 1 => pES3wr71
  | 2 => pES3wr72
  | 3 => pES3wr74
  | 4 => pES3wr73
  | 5 => pES3wr75
  | 6 => pES3wr76
  | 7 => pES3wr77
  | 8 => pES3wr78
  | 9 => pES3wr710
  | 10 => pES3wr79
  | 11 => pES3wr711
  | 12 => pES3wr712
  | 13 => pES3wr713
  | 14 => pES3wr714
  | 15 => pES3wr716
  | 16 => pES3wr715
  | 17 => pES3wr717
  | 18 => pES3wr736
  | 19 => pES3wr737
  | 20 => pES3wr738
  | 21 => pES3wr740
  | 22 => pES3wr739
  | 23 => pES3wr741
  | 24 => pES3wr724
  | 25 => pES3wr730
  | 26 => pES3wr748
  | 27 => pES3wr760
  | 28 => pES3wr754
  | 29 => pES3wr766
  | 30 => pES3wr725
  | 31 => pES3wr731
  | 32 => pES3wr749
  | 33 => pES3wr761
  | 34 => pES3wr755
  | 35 => pES3wr767
  | 36 => pES3wr718
  | 37 => pES3wr719
  | 38 => pES3wr720
  | 39 => pES3wr722
  | 40 => pES3wr721
  | 41 => pES3wr723
  | 42 => pES3wr742
  | 43 => pES3wr743
  | 44 => pES3wr744
  | 45 => pES3wr746
  | 46 => pES3wr745
  | 47 => pES3wr747
  | 48 => pES3wr726
  | 49 => pES3wr732
  | 50 => pES3wr750
  | 51 => pES3wr762
  | 52 => pES3wr756
  | 53 => pES3wr768
  | 54 => pES3wr728
  | 55 => pES3wr734
  | 56 => pES3wr752
  | 57 => pES3wr764
  | 58 => pES3wr758
  | 59 => pES3wr770
  | 60 => pES3wr727
  | 61 => pES3wr733
  | 62 => pES3wr751
  | 63 => pES3wr763
  | 64 => pES3wr757
  | 65 => pES3wr769
  | 66 => pES3wr729
  | 67 => pES3wr735
  | 68 => pES3wr753
  | 69 => pES3wr765
  | 70 => pES3wr759
  | _ => pES3wr771

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eES3wr7 (i : Fin 72) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permES3wr7 i) (permEinvS3wr7 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 3)(4 6)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXS3wr70 : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 6 | 5 => 5 | 6 => 4
def pXS3wr70inv : Fin 7 → Fin 7 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 6 | 5 => 5 | 6 => 4

def permXS3wr7 : Fin 1 → Fin 7 → Fin 7
  | 0 => pXS3wr70

def permXinvS3wr7 : Fin 1 → Fin 7 → Fin 7
  | 0 => pXS3wr70inv

def eXS3wr7 (i : Fin 1) : Equiv.Perm (Fin 7) :=
  Magma.permOf (permXS3wr7 i) (permXinvS3wr7 i) (by revert i; decide)

/-- One representative per orbit of the group on the `49` cells; there are `6`, so an invariant
operation is `6` values. -/
def repS3wr7 : Fin 6 → Fin 7 × Fin 7
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)
  | 4 => (2, 0)
  | 5 => (2, 2)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trS3wr7 : Fin 7 → Fin 7 → Fin 6 × Fin 72
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (2, 0)
  | 0, 3 => (3, 0)
  | 0, 4 => (1, 6)
  | 0, 5 => (3, 2)
  | 0, 6 => (3, 4)
  | 1, 0 => (1, 12)
  | 1, 1 => (0, 12)
  | 1, 2 => (2, 12)
  | 1, 3 => (3, 12)
  | 1, 4 => (1, 18)
  | 1, 5 => (3, 14)
  | 1, 6 => (3, 16)
  | 2, 0 => (4, 0)
  | 2, 1 => (4, 12)
  | 2, 2 => (5, 0)
  | 2, 3 => (4, 24)
  | 2, 4 => (4, 36)
  | 2, 5 => (4, 48)
  | 2, 6 => (4, 60)
  | 3, 0 => (3, 24)
  | 3, 1 => (3, 26)
  | 3, 2 => (2, 24)
  | 3, 3 => (0, 24)
  | 3, 4 => (3, 28)
  | 3, 5 => (1, 24)
  | 3, 6 => (1, 30)
  | 4, 0 => (1, 36)
  | 4, 1 => (1, 42)
  | 4, 2 => (2, 36)
  | 4, 3 => (3, 36)
  | 4, 4 => (0, 36)
  | 4, 5 => (3, 38)
  | 4, 6 => (3, 40)
  | 5, 0 => (3, 48)
  | 5, 1 => (3, 50)
  | 5, 2 => (2, 48)
  | 5, 3 => (1, 48)
  | 5, 4 => (3, 52)
  | 5, 5 => (0, 48)
  | 5, 6 => (1, 54)
  | 6, 0 => (3, 60)
  | 6, 1 => (3, 62)
  | 6, 2 => (2, 60)
  | 6, 3 => (1, 60)
  | 6, 4 => (3, 64)
  | 6, 5 => (1, 66)
  | 6, 6 => (0, 60)

/-- The `12` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS3wr70 : Fin 12 → Fin 72
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
def valS3wr70 : Fin 2 → Fin 7
  | 0 => 0
  | 1 => 2

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `2`, `4`, so the orbit is indexed by `Fin 4` instead. -/
def stabIdxS3wr71 : Fin 6 → Fin 72
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def valS3wr71 : Fin 4 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4

/-- The `12` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS3wr72 : Fin 12 → Fin 72
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
def valS3wr72 : Fin 2 → Fin 7
  | 0 => 0
  | 1 => 2

/-- The `4` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `2`, `3`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS3wr73 : Fin 4 → Fin 72
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
def valS3wr73 : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 2
  | 2 => 3

/-- The `12` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be one of `0`, `2`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS3wr74 : Fin 12 → Fin 72
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
def valS3wr74 : Fin 2 → Fin 7
  | 0 => 0
  | 1 => 2

/-- The `72` group elements fixing both coordinates of orbit `5`'s representative, and hence its
value: that value must be `2`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxS3wr75 : Fin 72 → Fin 72
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
  | 23 => 23
  | 24 => 24
  | 25 => 25
  | 26 => 26
  | 27 => 27
  | 28 => 28
  | 29 => 29
  | 30 => 30
  | 31 => 31
  | 32 => 32
  | 33 => 33
  | 34 => 34
  | 35 => 35
  | 36 => 36
  | 37 => 37
  | 38 => 38
  | 39 => 39
  | 40 => 40
  | 41 => 41
  | 42 => 42
  | 43 => 43
  | 44 => 44
  | 45 => 45
  | 46 => 46
  | 47 => 47
  | 48 => 48
  | 49 => 49
  | 50 => 50
  | 51 => 51
  | 52 => 52
  | 53 => 53
  | 54 => 54
  | 55 => 55
  | 56 => 56
  | 57 => 57
  | 58 => 58
  | 59 => 59
  | 60 => 60
  | 61 => 61
  | 62 => 62
  | 63 => 63
  | 64 => 64
  | 65 => 65
  | 66 => 66
  | 67 => 67
  | 68 => 68
  | 69 => 69
  | 70 => 70
  | _ => 71
def valS3wr75 : Fin 1 → Fin 7
  | 0 => 2

/-- The `6` orbit values named by the family's arguments. -/
def decS3wr7 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 3) (e : Fin 2) (f : Fin 1) : Fin 6 → Fin 7
  | 0 => valS3wr70 a
  | 1 => valS3wr71 b
  | 2 => valS3wr72 c
  | 3 => valS3wr73 d
  | 4 => valS3wr74 e
  | 5 => valS3wr75 f

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabS3wr7_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabS3wr7 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 3) (e : Fin 2) (f : Fin 1)
    : Fin 7 → Fin 7 → Fin 7
  | 0, 0 => valS3wr70 a
  | 0, 1 => valS3wr71 b
  | 0, 2 => valS3wr72 c
  | 0, 3 => valS3wr73 d
  | 0, 4 => pES3wr76 (valS3wr71 b)
  | 0, 5 => pES3wr72 (valS3wr73 d)
  | 0, 6 => pES3wr74 (valS3wr73 d)
  | 1, 0 => pES3wr712 (valS3wr71 b)
  | 1, 1 => pES3wr712 (valS3wr70 a)
  | 1, 2 => pES3wr712 (valS3wr72 c)
  | 1, 3 => pES3wr712 (valS3wr73 d)
  | 1, 4 => pES3wr718 (valS3wr71 b)
  | 1, 5 => pES3wr714 (valS3wr73 d)
  | 1, 6 => pES3wr716 (valS3wr73 d)
  | 2, 0 => valS3wr74 e
  | 2, 1 => pES3wr712 (valS3wr74 e)
  | 2, 2 => valS3wr75 f
  | 2, 3 => pES3wr724 (valS3wr74 e)
  | 2, 4 => pES3wr736 (valS3wr74 e)
  | 2, 5 => pES3wr748 (valS3wr74 e)
  | 2, 6 => pES3wr760 (valS3wr74 e)
  | 3, 0 => pES3wr724 (valS3wr73 d)
  | 3, 1 => pES3wr726 (valS3wr73 d)
  | 3, 2 => pES3wr724 (valS3wr72 c)
  | 3, 3 => pES3wr724 (valS3wr70 a)
  | 3, 4 => pES3wr728 (valS3wr73 d)
  | 3, 5 => pES3wr724 (valS3wr71 b)
  | 3, 6 => pES3wr730 (valS3wr71 b)
  | 4, 0 => pES3wr736 (valS3wr71 b)
  | 4, 1 => pES3wr742 (valS3wr71 b)
  | 4, 2 => pES3wr736 (valS3wr72 c)
  | 4, 3 => pES3wr736 (valS3wr73 d)
  | 4, 4 => pES3wr736 (valS3wr70 a)
  | 4, 5 => pES3wr738 (valS3wr73 d)
  | 4, 6 => pES3wr740 (valS3wr73 d)
  | 5, 0 => pES3wr748 (valS3wr73 d)
  | 5, 1 => pES3wr750 (valS3wr73 d)
  | 5, 2 => pES3wr748 (valS3wr72 c)
  | 5, 3 => pES3wr748 (valS3wr71 b)
  | 5, 4 => pES3wr752 (valS3wr73 d)
  | 5, 5 => pES3wr748 (valS3wr70 a)
  | 5, 6 => pES3wr754 (valS3wr71 b)
  | 6, 0 => pES3wr760 (valS3wr73 d)
  | 6, 1 => pES3wr762 (valS3wr73 d)
  | 6, 2 => pES3wr760 (valS3wr72 c)
  | 6, 3 => pES3wr760 (valS3wr71 b)
  | 6, 4 => pES3wr764 (valS3wr73 d)
  | 6, 5 => pES3wr766 (valS3wr71 b)
  | 6, 6 => pES3wr760 (valS3wr70 a)

theorem tabS3wr7_eq_transport (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 3) (e : Fin 2)
    (f : Fin 1) :
    tabS3wr7 a b c d e f = Magma.transport permES3wr7 trS3wr7 (decS3wr7 a b c d e f) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `72` magmas on `Fin 7` whose automorphism group is exactly this group, listed under one
index. Of the `96` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memRowS3wr70 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS3wr7 0 0 0 1 0 0
  | 1 => tabS3wr7 0 0 0 1 1 0
  | 2 => tabS3wr7 0 0 0 2 0 0
  | 3 => tabS3wr7 0 0 0 2 1 0
  | 4 => tabS3wr7 0 0 1 1 0 0
  | 5 => tabS3wr7 0 0 1 1 1 0
  | 6 => tabS3wr7 0 0 1 2 0 0
  | 7 => tabS3wr7 0 0 1 2 1 0
  | _ => tabS3wr7 0 1 0 0 0 0
def memRowS3wr71 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS3wr7 0 1 0 0 1 0
  | 1 => tabS3wr7 0 1 0 1 0 0
  | 2 => tabS3wr7 0 1 0 1 1 0
  | 3 => tabS3wr7 0 1 1 0 0 0
  | 4 => tabS3wr7 0 1 1 0 1 0
  | 5 => tabS3wr7 0 1 1 1 0 0
  | 6 => tabS3wr7 0 1 1 1 1 0
  | 7 => tabS3wr7 0 2 0 0 0 0
  | _ => tabS3wr7 0 2 0 0 1 0
def memRowS3wr72 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS3wr7 0 2 0 2 0 0
  | 1 => tabS3wr7 0 2 0 2 1 0
  | 2 => tabS3wr7 0 2 1 0 0 0
  | 3 => tabS3wr7 0 2 1 0 1 0
  | 4 => tabS3wr7 0 2 1 2 0 0
  | 5 => tabS3wr7 0 2 1 2 1 0
  | 6 => tabS3wr7 0 3 0 0 0 0
  | 7 => tabS3wr7 0 3 0 0 1 0
  | _ => tabS3wr7 0 3 0 1 0 0
def memRowS3wr73 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS3wr7 0 3 0 1 1 0
  | 1 => tabS3wr7 0 3 0 2 0 0
  | 2 => tabS3wr7 0 3 0 2 1 0
  | 3 => tabS3wr7 0 3 1 0 0 0
  | 4 => tabS3wr7 0 3 1 0 1 0
  | 5 => tabS3wr7 0 3 1 1 0 0
  | 6 => tabS3wr7 0 3 1 1 1 0
  | 7 => tabS3wr7 0 3 1 2 0 0
  | _ => tabS3wr7 0 3 1 2 1 0
def memRowS3wr74 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS3wr7 1 0 0 1 0 0
  | 1 => tabS3wr7 1 0 0 1 1 0
  | 2 => tabS3wr7 1 0 0 2 0 0
  | 3 => tabS3wr7 1 0 0 2 1 0
  | 4 => tabS3wr7 1 0 1 1 0 0
  | 5 => tabS3wr7 1 0 1 1 1 0
  | 6 => tabS3wr7 1 0 1 2 0 0
  | 7 => tabS3wr7 1 0 1 2 1 0
  | _ => tabS3wr7 1 1 0 0 0 0
def memRowS3wr75 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS3wr7 1 1 0 0 1 0
  | 1 => tabS3wr7 1 1 0 1 0 0
  | 2 => tabS3wr7 1 1 0 1 1 0
  | 3 => tabS3wr7 1 1 1 0 0 0
  | 4 => tabS3wr7 1 1 1 0 1 0
  | 5 => tabS3wr7 1 1 1 1 0 0
  | 6 => tabS3wr7 1 1 1 1 1 0
  | 7 => tabS3wr7 1 2 0 0 0 0
  | _ => tabS3wr7 1 2 0 0 1 0
def memRowS3wr76 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS3wr7 1 2 0 2 0 0
  | 1 => tabS3wr7 1 2 0 2 1 0
  | 2 => tabS3wr7 1 2 1 0 0 0
  | 3 => tabS3wr7 1 2 1 0 1 0
  | 4 => tabS3wr7 1 2 1 2 0 0
  | 5 => tabS3wr7 1 2 1 2 1 0
  | 6 => tabS3wr7 1 3 0 0 0 0
  | 7 => tabS3wr7 1 3 0 0 1 0
  | _ => tabS3wr7 1 3 0 1 0 0
def memRowS3wr77 : Fin 9 → Fin 7 → Fin 7 → Fin 7
  | 0 => tabS3wr7 1 3 0 1 1 0
  | 1 => tabS3wr7 1 3 0 2 0 0
  | 2 => tabS3wr7 1 3 0 2 1 0
  | 3 => tabS3wr7 1 3 1 0 0 0
  | 4 => tabS3wr7 1 3 1 0 1 0
  | 5 => tabS3wr7 1 3 1 1 0 0
  | 6 => tabS3wr7 1 3 1 1 1 0
  | 7 => tabS3wr7 1 3 1 2 0 0
  | _ => tabS3wr7 1 3 1 2 1 0
def memS3wr7 (i : Fin 72) : Fin 7 → Fin 7 → Fin 7 :=
  match (i.1 / 9 : Nat) with
  | 0 => memRowS3wr70 ⟨i.1 % 9, by omega⟩
  | 1 => memRowS3wr71 ⟨i.1 % 9, by omega⟩
  | 2 => memRowS3wr72 ⟨i.1 % 9, by omega⟩
  | 3 => memRowS3wr73 ⟨i.1 % 9, by omega⟩
  | 4 => memRowS3wr74 ⟨i.1 % 9, by omega⟩
  | 5 => memRowS3wr75 ⟨i.1 % 9, by omega⟩
  | 6 => memRowS3wr76 ⟨i.1 % 9, by omega⟩
  | _ => memRowS3wr77 ⟨i.1 % 9, by omega⟩

/-- Which of the `72` members a given invariant tuple is, so that `mem_of_isExactS3wr7` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrS3wr7 : Array Nat := #[
  0, 0, 0, 1, 2, 3, 0, 0, 4, 5, 6, 7, 8, 9, 10, 11, 0, 0, 12, 13, 14, 15, 0, 0, 16, 17, 0, 0, 18,
  19, 20, 21, 0, 0, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 0, 0, 36, 37, 38, 39,
  0, 0, 40, 41, 42, 43, 44, 45, 46, 47, 0, 0, 48, 49, 50, 51, 0, 0, 52, 53, 0, 0, 54, 55, 56, 57,
  0, 0, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71]

/-- The arguments as one mixed-radix index, which is how `rankArrS3wr7` is addressed. -/
def encTS3wr7 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 3) (e : Fin 2) (f : Fin 1) : Nat :=
  a.1 * 48 +
    b.1 * 12 +
    c.1 * 6 +
    d.1 * 2 +
    e.1 +
    f.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankS3wr7 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 3) (e : Fin 2) (f : Fin 1) : Fin 72 :=
  ⟨min (rankArrS3wr7.getD (encTS3wr7 a b c d e f) 0) 71, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactS3wr7 (i : Fin 72) : Magma (Fin 7) := Magma.mk (memS3wr7 i)

theorem exactS3wr7_isEndo (i : Fin 72) (j : Fin 72) : (exactS3wr7 i).IsEndo ⇑(eES3wr7 j) := by
  simp only [eES3wr7, coe_permOf]; revert i j; native_decide

theorem exactS3wr7_not_isEndo (i : Fin 72) (j : Fin 1) : ¬ (exactS3wr7 i).IsEndo ⇑(eXS3wr7 j) := by
  simp only [eXS3wr7, coe_permOf]; revert i j; native_decide

/-- `rankS3wr7` really does name the member a tuple is. Deciding this is one array read and one
table comparison per tuple, where searching `memS3wr7` for the index would be a comparison per tuple
and member. -/
theorem mem_rankS3wr7 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 3) (e : Fin 2) (f : Fin 1)
    (h : Magma.isExact (tabS3wr7 a b c d e f) permES3wr7 permXS3wr7 = true) :
    memS3wr7 (rankS3wr7 a b c d e f) = tabS3wr7 a b c d e f := by
  revert h; revert a b c d e f; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `72` listed
members. -/
theorem mem_of_isExactS3wr7 (a : Fin 2) (b : Fin 4) (c : Fin 2) (d : Fin 3) (e : Fin 2) (f : Fin 1)
    (h : Magma.isExact (tabS3wr7 a b c d e f) permES3wr7 permXS3wr7 = true) :
    ∃ i, memS3wr7 i = tabS3wr7 a b c d e f :=
  ⟨_, mem_rankS3wr7 a b c d e f h⟩

/-- A magma on `Fin 7` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactS3wr7`. Its values at the orbit representatives name an invariant
tuple, and `mem_of_isExactS3wr7` turns that into a member index. -/
theorem exists_exactS3wr7 {M : Magma (Fin 7)} (hE : ∀ i, M.IsEndo ⇑(eES3wr7 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXS3wr7 i)) : ∃ i, exactS3wr7 i = M := by
  simp only [eES3wr7, coe_permOf] at hE
  simp only [eXS3wr7, coe_permOf] at hX
  have hop : M.op =
      Magma.transport permES3wr7 trS3wr7 (fun i ↦ M.op (repS3wr7 i).1 (repS3wr7 i).2) :=
    Magma.op_eq_transport (rep := repS3wr7) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permES3wr7) (idx := stabIdxS3wr70) (a := (repS3wr7 0).1) (b := (repS3wr7 0).2)
    (val := valS3wr70) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permES3wr7) (idx := stabIdxS3wr71) (a := (repS3wr7 1).1) (b := (repS3wr7 1).2)
    (val := valS3wr71) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permES3wr7) (idx := stabIdxS3wr72) (a := (repS3wr7 2).1) (b := (repS3wr7 2).2)
    (val := valS3wr72) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permES3wr7) (idx := stabIdxS3wr73) (a := (repS3wr7 3).1) (b := (repS3wr7 3).2)
    (val := valS3wr73) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permES3wr7) (idx := stabIdxS3wr74) (a := (repS3wr7 4).1) (b := (repS3wr7 4).2)
    (val := valS3wr74) hE (by decide) (by decide)
  obtain ⟨f, hf⟩ := Magma.exists_val_of_isEndo
    (E := permES3wr7) (idx := stabIdxS3wr75) (a := (repS3wr7 5).1) (b := (repS3wr7 5).2)
    (val := valS3wr75) hE (by decide) (by decide)
  have hdec : decS3wr7 a b c d e f = fun i ↦ M.op (repS3wr7 i).1 (repS3wr7 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have key : tabS3wr7 a b c d e f = M.op := by
    rw [tabS3wr7_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabS3wr7 a b c d e f) permES3wr7 permXS3wr7 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactS3wr7 a b c d e f hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 7`.** If `L'` has a model on `Fin 7` whose automorphism
group is exactly the order-`72` group of `Magma.permES3wr7`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactS3wr7 {L L' : Law.NatMagmaLaw} {i : Fin 72}
    (hsrc : @satisfies _ (Fin 7) (Magma.exactS3wr7 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 7) (Magma.exactS3wr7 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactS3wr7 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactS3wr7
    (fun k ↦ (Magma.exactS3wr7_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactS3wr7_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw

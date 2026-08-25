import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `S3wr6` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`72` group `⟨(0 1)(2 3)(4 5), (0 1)(2 3 4 5), (0 1 3 2)(4 5)⟩` -/

/-- The `72` elements of the group: `()`, `(3 5)`, `(2 4)`, `(2 4)(3 5)`, `(1 2)`, `(1 2)(3 5)`, `(1
2 4)`, `(1 2 4)(3 5)`, `(1 4 2)`, `(1 4 2)(3 5)`, `(1 4)`, `(1 4)(3 5)`, `(0 1)(2 3)(4 5)`, `(0 1)(2
3 4 5)`, `(0 1)(2 5 4 3)`, `(0 1)(2 5)(3 4)`, `(0 1 3 2)(4 5)`, `(0 1 3 4 5 2)`, `(0 1 3 2 5 4)`,
`(0 1 3 4)(2 5)`, `(0 1 5 4 3 2)`, `(0 1 5 2)(3 4)`, `(0 1 5 4)(2 3)`, `(0 1 5 2 3 4)`, `(0 2 3 1)(4
5)`, `(0 2 3 4 5 1)`, `(0 2 5 4 3 1)`, `(0 2 5 1)(3 4)`, `(0 2)(1 3)(4 5)`, `(0 2)(1 3 4 5)`, `(0 2
5 4)(1 3)`, `(0 2 5 1 3 4)`, `(0 2)(1 5 4 3)`, `(0 2)(1 5)(3 4)`, `(0 2 3 1 5 4)`, `(0 2 3 4)(1 5)`,
`(0 3)`, `(0 3 5)`, `(0 3)(2 4)`, `(0 3 5)(2 4)`, `(0 3)(1 2)`, `(0 3 5)(1 2)`, `(0 3)(1 2 4)`, `(0
3 5)(1 2 4)`, `(0 3)(1 4 2)`, `(0 3 5)(1 4 2)`, `(0 3)(1 4)`, `(0 3 5)(1 4)`, `(0 4 5 2 3 1)`, `(0 4
5 1)(2 3)`, `(0 4 3 1)(2 5)`, `(0 4 3 2 5 1)`, `(0 4 5 2)(1 3)`, `(0 4 5 1 3 2)`, `(0 4)(1 3)(2 5)`,
`(0 4)(1 3 2 5)`, `(0 4 3 1 5 2)`, `(0 4 3 2)(1 5)`, `(0 4)(1 5 2 3)`, `(0 4)(1 5)(2 3)`, `(0 5 3)`,
`(0 5)`, `(0 5 3)(2 4)`, `(0 5)(2 4)`, `(0 5 3)(1 2)`, `(0 5)(1 2)`, `(0 5 3)(1 2 4)`, `(0 5)(1 2
4)`, `(0 5 3)(1 4 2)`, `(0 5)(1 4 2)`, `(0 5 3)(1 4)`, `(0 5)(1 4)`. -/
def pES3wr60 : Fin 6 → Fin 6 := id
def pES3wr61 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 3
def pES3wr62 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5
def pES3wr63 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3
def pES3wr64 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5
def pES3wr65 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 3
def pES3wr66 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5
def pES3wr67 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 5 | 4 => 1 | 5 => 3
def pES3wr68 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5
def pES3wr69 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 5 | 4 => 2 | 5 => 3
def pES3wr610 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5
def pES3wr611 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 1 | 5 => 3
def pES3wr612 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def pES3wr613 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 2
def pES3wr614 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 2 | 4 => 3 | 5 => 4
def pES3wr615 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2
def pES3wr616 : Fin 6 → Fin 6 | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 5 | 5 => 4
def pES3wr617 : Fin 6 → Fin 6 | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 2
def pES3wr618 : Fin 6 → Fin 6 | 0 => 1 | 1 => 3 | 2 => 5 | 3 => 2 | 4 => 0 | 5 => 4
def pES3wr619 : Fin 6 → Fin 6 | 0 => 1 | 1 => 3 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 2
def pES3wr620 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 4
def pES3wr621 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 2
def pES3wr622 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 4
def pES3wr623 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 2
def pES3wr624 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 4
def pES3wr625 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 1
def pES3wr626 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 4
def pES3wr627 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 1
def pES3wr628 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 4
def pES3wr629 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 5 | 5 => 1
def pES3wr630 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 0 | 5 => 4
def pES3wr631 : Fin 6 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 1
def pES3wr632 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 4
def pES3wr633 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 1
def pES3wr634 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 4
def pES3wr635 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 1
def pES3wr636 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5
def pES3wr637 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 4 | 5 => 0
def pES3wr638 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5
def pES3wr639 : Fin 6 → Fin 6 | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 0
def pES3wr640 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5
def pES3wr641 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 0
def pES3wr642 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5
def pES3wr643 : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 5 | 4 => 1 | 5 => 0
def pES3wr644 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5
def pES3wr645 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 5 | 4 => 2 | 5 => 0
def pES3wr646 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5
def pES3wr647 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 1 | 5 => 0
def pES3wr648 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 2
def pES3wr649 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 1
def pES3wr650 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 2
def pES3wr651 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 5 | 3 => 2 | 4 => 3 | 5 => 1
def pES3wr652 : Fin 6 → Fin 6 | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 2
def pES3wr653 : Fin 6 → Fin 6 | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 5 | 5 => 1
def pES3wr654 : Fin 6 → Fin 6 | 0 => 4 | 1 => 3 | 2 => 5 | 3 => 1 | 4 => 0 | 5 => 2
def pES3wr655 : Fin 6 → Fin 6 | 0 => 4 | 1 => 3 | 2 => 5 | 3 => 2 | 4 => 0 | 5 => 1
def pES3wr656 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 2
def pES3wr657 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 1
def pES3wr658 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 2
def pES3wr659 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 1
def pES3wr660 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 3
def pES3wr661 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 0
def pES3wr662 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 3
def pES3wr663 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 0
def pES3wr664 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 3
def pES3wr665 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 0
def pES3wr666 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 3
def pES3wr667 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 0
def pES3wr668 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 3
def pES3wr669 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 0
def pES3wr670 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 3
def pES3wr671 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 0

def permES3wr6 : Fin 72 → Fin 6 → Fin 6
  | 0 => pES3wr60
  | 1 => pES3wr61
  | 2 => pES3wr62
  | 3 => pES3wr63
  | 4 => pES3wr64
  | 5 => pES3wr65
  | 6 => pES3wr66
  | 7 => pES3wr67
  | 8 => pES3wr68
  | 9 => pES3wr69
  | 10 => pES3wr610
  | 11 => pES3wr611
  | 12 => pES3wr612
  | 13 => pES3wr613
  | 14 => pES3wr614
  | 15 => pES3wr615
  | 16 => pES3wr616
  | 17 => pES3wr617
  | 18 => pES3wr618
  | 19 => pES3wr619
  | 20 => pES3wr620
  | 21 => pES3wr621
  | 22 => pES3wr622
  | 23 => pES3wr623
  | 24 => pES3wr624
  | 25 => pES3wr625
  | 26 => pES3wr626
  | 27 => pES3wr627
  | 28 => pES3wr628
  | 29 => pES3wr629
  | 30 => pES3wr630
  | 31 => pES3wr631
  | 32 => pES3wr632
  | 33 => pES3wr633
  | 34 => pES3wr634
  | 35 => pES3wr635
  | 36 => pES3wr636
  | 37 => pES3wr637
  | 38 => pES3wr638
  | 39 => pES3wr639
  | 40 => pES3wr640
  | 41 => pES3wr641
  | 42 => pES3wr642
  | 43 => pES3wr643
  | 44 => pES3wr644
  | 45 => pES3wr645
  | 46 => pES3wr646
  | 47 => pES3wr647
  | 48 => pES3wr648
  | 49 => pES3wr649
  | 50 => pES3wr650
  | 51 => pES3wr651
  | 52 => pES3wr652
  | 53 => pES3wr653
  | 54 => pES3wr654
  | 55 => pES3wr655
  | 56 => pES3wr656
  | 57 => pES3wr657
  | 58 => pES3wr658
  | 59 => pES3wr659
  | 60 => pES3wr660
  | 61 => pES3wr661
  | 62 => pES3wr662
  | 63 => pES3wr663
  | 64 => pES3wr664
  | 65 => pES3wr665
  | 66 => pES3wr666
  | 67 => pES3wr667
  | 68 => pES3wr668
  | 69 => pES3wr669
  | 70 => pES3wr670
  | _ => pES3wr671

def permEinvS3wr6 : Fin 72 → Fin 6 → Fin 6
  | 0 => pES3wr60
  | 1 => pES3wr61
  | 2 => pES3wr62
  | 3 => pES3wr63
  | 4 => pES3wr64
  | 5 => pES3wr65
  | 6 => pES3wr68
  | 7 => pES3wr69
  | 8 => pES3wr66
  | 9 => pES3wr67
  | 10 => pES3wr610
  | 11 => pES3wr611
  | 12 => pES3wr612
  | 13 => pES3wr614
  | 14 => pES3wr613
  | 15 => pES3wr615
  | 16 => pES3wr624
  | 17 => pES3wr626
  | 18 => pES3wr648
  | 19 => pES3wr650
  | 20 => pES3wr625
  | 21 => pES3wr627
  | 22 => pES3wr649
  | 23 => pES3wr651
  | 24 => pES3wr616
  | 25 => pES3wr620
  | 26 => pES3wr617
  | 27 => pES3wr621
  | 28 => pES3wr628
  | 29 => pES3wr632
  | 30 => pES3wr652
  | 31 => pES3wr656
  | 32 => pES3wr629
  | 33 => pES3wr633
  | 34 => pES3wr653
  | 35 => pES3wr657
  | 36 => pES3wr636
  | 37 => pES3wr660
  | 38 => pES3wr638
  | 39 => pES3wr662
  | 40 => pES3wr640
  | 41 => pES3wr664
  | 42 => pES3wr644
  | 43 => pES3wr668
  | 44 => pES3wr642
  | 45 => pES3wr666
  | 46 => pES3wr646
  | 47 => pES3wr670
  | 48 => pES3wr618
  | 49 => pES3wr622
  | 50 => pES3wr619
  | 51 => pES3wr623
  | 52 => pES3wr630
  | 53 => pES3wr634
  | 54 => pES3wr654
  | 55 => pES3wr658
  | 56 => pES3wr631
  | 57 => pES3wr635
  | 58 => pES3wr655
  | 59 => pES3wr659
  | 60 => pES3wr637
  | 61 => pES3wr661
  | 62 => pES3wr639
  | 63 => pES3wr663
  | 64 => pES3wr641
  | 65 => pES3wr665
  | 66 => pES3wr645
  | 67 => pES3wr669
  | 68 => pES3wr643
  | 69 => pES3wr667
  | 70 => pES3wr647
  | _ => pES3wr671

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eES3wr6 (i : Fin 72) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permES3wr6 i) (permEinvS3wr6 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 5)(2 3 4)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXS3wr60 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 0
def pXS3wr60inv : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 0

def permXS3wr6 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXS3wr60

def permXinvS3wr6 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXS3wr60inv

def eXS3wr6 (i : Fin 1) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXS3wr6 i) (permXinvS3wr6 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `3`, so an invariant
operation is `3` values. -/
def repS3wr6 : Fin 3 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trS3wr6 : Fin 6 → Fin 6 → Fin 3 × Fin 72
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 4)
  | 0, 3 => (2, 0)
  | 0, 4 => (1, 8)
  | 0, 5 => (2, 1)
  | 1, 0 => (1, 12)
  | 1, 1 => (0, 12)
  | 1, 2 => (2, 12)
  | 1, 3 => (1, 16)
  | 1, 4 => (2, 13)
  | 1, 5 => (1, 20)
  | 2, 0 => (1, 24)
  | 2, 1 => (2, 24)
  | 2, 2 => (0, 24)
  | 2, 3 => (1, 28)
  | 2, 4 => (2, 25)
  | 2, 5 => (1, 32)
  | 3, 0 => (2, 36)
  | 3, 1 => (1, 36)
  | 3, 2 => (1, 40)
  | 3, 3 => (0, 36)
  | 3, 4 => (1, 44)
  | 3, 5 => (2, 37)
  | 4, 0 => (1, 48)
  | 4, 1 => (2, 48)
  | 4, 2 => (2, 49)
  | 4, 3 => (1, 52)
  | 4, 4 => (0, 48)
  | 4, 5 => (1, 56)
  | 5, 0 => (2, 60)
  | 5, 1 => (1, 60)
  | 5, 2 => (1, 64)
  | 5, 3 => (2, 61)
  | 5, 4 => (1, 68)
  | 5, 5 => (0, 60)

/-- The `12` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be `0`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxS3wr60 : Fin 12 → Fin 72
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
def valS3wr60 : Fin 1 → Fin 6
  | 0 => 0

/-- The `4` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS3wr61 : Fin 4 → Fin 72
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
def valS3wr61 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 1

/-- The `6` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, `5`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS3wr62 : Fin 6 → Fin 72
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 10
def valS3wr62 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 5

/-- The `3` orbit values named by the family's arguments. -/
def decS3wr6 (a : Fin 1) (b : Fin 2) (c : Fin 3) : Fin 3 → Fin 6
  | 0 => valS3wr60 a
  | 1 => valS3wr61 b
  | 2 => valS3wr62 c

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabS3wr6_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabS3wr6 (a : Fin 1) (b : Fin 2) (c : Fin 3) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valS3wr60 a
  | 0, 1 => valS3wr61 b
  | 0, 2 => pES3wr64 (valS3wr61 b)
  | 0, 3 => valS3wr62 c
  | 0, 4 => pES3wr68 (valS3wr61 b)
  | 0, 5 => pES3wr61 (valS3wr62 c)
  | 1, 0 => pES3wr612 (valS3wr61 b)
  | 1, 1 => pES3wr612 (valS3wr60 a)
  | 1, 2 => pES3wr612 (valS3wr62 c)
  | 1, 3 => pES3wr616 (valS3wr61 b)
  | 1, 4 => pES3wr613 (valS3wr62 c)
  | 1, 5 => pES3wr620 (valS3wr61 b)
  | 2, 0 => pES3wr624 (valS3wr61 b)
  | 2, 1 => pES3wr624 (valS3wr62 c)
  | 2, 2 => pES3wr624 (valS3wr60 a)
  | 2, 3 => pES3wr628 (valS3wr61 b)
  | 2, 4 => pES3wr625 (valS3wr62 c)
  | 2, 5 => pES3wr632 (valS3wr61 b)
  | 3, 0 => pES3wr636 (valS3wr62 c)
  | 3, 1 => pES3wr636 (valS3wr61 b)
  | 3, 2 => pES3wr640 (valS3wr61 b)
  | 3, 3 => pES3wr636 (valS3wr60 a)
  | 3, 4 => pES3wr644 (valS3wr61 b)
  | 3, 5 => pES3wr637 (valS3wr62 c)
  | 4, 0 => pES3wr648 (valS3wr61 b)
  | 4, 1 => pES3wr648 (valS3wr62 c)
  | 4, 2 => pES3wr649 (valS3wr62 c)
  | 4, 3 => pES3wr652 (valS3wr61 b)
  | 4, 4 => pES3wr648 (valS3wr60 a)
  | 4, 5 => pES3wr656 (valS3wr61 b)
  | 5, 0 => pES3wr660 (valS3wr62 c)
  | 5, 1 => pES3wr660 (valS3wr61 b)
  | 5, 2 => pES3wr664 (valS3wr61 b)
  | 5, 3 => pES3wr661 (valS3wr62 c)
  | 5, 4 => pES3wr668 (valS3wr61 b)
  | 5, 5 => pES3wr660 (valS3wr60 a)

theorem tabS3wr6_eq_transport (a : Fin 1) (b : Fin 2) (c : Fin 3) :
    tabS3wr6 a b c = Magma.transport permES3wr6 trS3wr6 (decS3wr6 a b c) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `4` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `6` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memS3wr6 : Fin 4 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabS3wr6 0 0 1
  | 1 => tabS3wr6 0 0 2
  | 2 => tabS3wr6 0 1 0
  | 3 => tabS3wr6 0 1 2

/-- Which of the `4` members a given invariant tuple is, so that `mem_of_isExactS3wr6` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrS3wr6 : Array Nat := #[
  0, 0, 1, 2, 0, 3]

/-- The arguments as one mixed-radix index, which is how `rankArrS3wr6` is addressed. -/
def encTS3wr6 (a : Fin 1) (b : Fin 2) (c : Fin 3) : Nat :=
  a.1 * 6 +
    b.1 * 3 +
    c.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankS3wr6 (a : Fin 1) (b : Fin 2) (c : Fin 3) : Fin 4 :=
  ⟨min (rankArrS3wr6.getD (encTS3wr6 a b c) 0) 3, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactS3wr6 (i : Fin 4) : Magma (Fin 6) := Magma.mk (memS3wr6 i)

theorem exactS3wr6_isEndo (i : Fin 4) (j : Fin 72) : (exactS3wr6 i).IsEndo ⇑(eES3wr6 j) := by
  simp only [eES3wr6, coe_permOf]; revert i j; native_decide

theorem exactS3wr6_not_isEndo (i : Fin 4) (j : Fin 1) : ¬ (exactS3wr6 i).IsEndo ⇑(eXS3wr6 j) := by
  simp only [eXS3wr6, coe_permOf]; revert i j; native_decide

/-- `rankS3wr6` really does name the member a tuple is. Deciding this is one array read and one
table comparison per tuple, where searching `memS3wr6` for the index would be a comparison per tuple
and member. -/
theorem mem_rankS3wr6 (a : Fin 1) (b : Fin 2) (c : Fin 3)
    (h : Magma.isExact (tabS3wr6 a b c) permES3wr6 permXS3wr6 = true) :
    memS3wr6 (rankS3wr6 a b c) = tabS3wr6 a b c := by
  revert h; revert a b c; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `4` listed
members. -/
theorem mem_of_isExactS3wr6 (a : Fin 1) (b : Fin 2) (c : Fin 3)
    (h : Magma.isExact (tabS3wr6 a b c) permES3wr6 permXS3wr6 = true) :
    ∃ i, memS3wr6 i = tabS3wr6 a b c :=
  ⟨_, mem_rankS3wr6 a b c h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactS3wr6`. Its values at the orbit representatives name an invariant
tuple, and `mem_of_isExactS3wr6` turns that into a member index. -/
theorem exists_exactS3wr6 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eES3wr6 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXS3wr6 i)) : ∃ i, exactS3wr6 i = M := by
  simp only [eES3wr6, coe_permOf] at hE
  simp only [eXS3wr6, coe_permOf] at hX
  have hop : M.op =
      Magma.transport permES3wr6 trS3wr6 (fun i ↦ M.op (repS3wr6 i).1 (repS3wr6 i).2) :=
    Magma.op_eq_transport (rep := repS3wr6) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permES3wr6) (idx := stabIdxS3wr60) (a := (repS3wr6 0).1) (b := (repS3wr6 0).2)
    (val := valS3wr60) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permES3wr6) (idx := stabIdxS3wr61) (a := (repS3wr6 1).1) (b := (repS3wr6 1).2)
    (val := valS3wr61) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permES3wr6) (idx := stabIdxS3wr62) (a := (repS3wr6 2).1) (b := (repS3wr6 2).2)
    (val := valS3wr62) hE (by decide) (by decide)
  have hdec : decS3wr6 a b c = fun i ↦ M.op (repS3wr6 i).1 (repS3wr6 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have key : tabS3wr6 a b c = M.op := by
    rw [tabS3wr6_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabS3wr6 a b c) permES3wr6 permXS3wr6 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactS3wr6 a b c hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`72` group of `Magma.permES3wr6`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactS3wr6 {L L' : Law.NatMagmaLaw} {i : Fin 4}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactS3wr6 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactS3wr6 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactS3wr6 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactS3wr6
    (fun k ↦ (Magma.exactS3wr6_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactS3wr6_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw

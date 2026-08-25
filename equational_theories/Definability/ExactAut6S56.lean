import equational_theories.Definability.ExactAut

/-!
# The exact-automorphism class `S56` on `Fin 6`

One class of `Definability/ExactAut6.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

-- `rankArr` is one list literal per invariant tuple, and the elaborator walks it as deeply as it
-- is long
set_option maxRecDepth 100000

open Law Law.MagmaLaw

namespace Magma

/-! ### The order-`120` group `⟨(0 1)(2 4 5), (0 1 2)(4 5)⟩` -/

/-- The `120` elements of the group: `()`, `(4 5)`, `(2 4)`, `(2 4 5)`, `(2 5 4)`, `(2 5)`, `(1 2)`,
`(1 2)(4 5)`, `(1 2 4)`, `(1 2 4 5)`, `(1 2 5 4)`, `(1 2 5)`, `(1 4 2)`, `(1 4 5 2)`, `(1 4)`, `(1 4
5)`, `(1 4)(2 5)`, `(1 4 2 5)`, `(1 5 4 2)`, `(1 5 2)`, `(1 5 4)`, `(1 5)`, `(1 5 2 4)`, `(1 5)(2
4)`, `(0 1)`, `(0 1)(4 5)`, `(0 1)(2 4)`, `(0 1)(2 4 5)`, `(0 1)(2 5 4)`, `(0 1)(2 5)`, `(0 1 2)`,
`(0 1 2)(4 5)`, `(0 1 2 4)`, `(0 1 2 4 5)`, `(0 1 2 5 4)`, `(0 1 2 5)`, `(0 1 4 2)`, `(0 1 4 5 2)`,
`(0 1 4)`, `(0 1 4 5)`, `(0 1 4)(2 5)`, `(0 1 4 2 5)`, `(0 1 5 4 2)`, `(0 1 5 2)`, `(0 1 5 4)`, `(0
1 5)`, `(0 1 5 2 4)`, `(0 1 5)(2 4)`, `(0 2 1)`, `(0 2 1)(4 5)`, `(0 2 4 1)`, `(0 2 4 5 1)`, `(0 2 5
4 1)`, `(0 2 5 1)`, `(0 2)`, `(0 2)(4 5)`, `(0 2 4)`, `(0 2 4 5)`, `(0 2 5 4)`, `(0 2 5)`, `(0 2)(1
4)`, `(0 2)(1 4 5)`, `(0 2 1 4)`, `(0 2 1 4 5)`, `(0 2 5 1 4)`, `(0 2 5)(1 4)`, `(0 2)(1 5 4)`, `(0
2)(1 5)`, `(0 2 1 5 4)`, `(0 2 1 5)`, `(0 2 4)(1 5)`, `(0 2 4 1 5)`, `(0 4 2 1)`, `(0 4 5 2 1)`, `(0
4 1)`, `(0 4 5 1)`, `(0 4 1)(2 5)`, `(0 4 2 5 1)`, `(0 4 2)`, `(0 4 5 2)`, `(0 4)`, `(0 4 5)`, `(0
4)(2 5)`, `(0 4 2 5)`, `(0 4 1 2)`, `(0 4 5 1 2)`, `(0 4)(1 2)`, `(0 4 5)(1 2)`, `(0 4)(1 2 5)`, `(0
4 1 2 5)`, `(0 4 1 5 2)`, `(0 4 2)(1 5)`, `(0 4)(1 5 2)`, `(0 4 2 1 5)`, `(0 4)(1 5)`, `(0 4 1 5)`,
`(0 5 4 2 1)`, `(0 5 2 1)`, `(0 5 4 1)`, `(0 5 1)`, `(0 5 2 4 1)`, `(0 5 1)(2 4)`, `(0 5 4 2)`, `(0
5 2)`, `(0 5 4)`, `(0 5)`, `(0 5 2 4)`, `(0 5)(2 4)`, `(0 5 4 1 2)`, `(0 5 1 2)`, `(0 5 4)(1 2)`,
`(0 5)(1 2)`, `(0 5 1 2 4)`, `(0 5)(1 2 4)`, `(0 5 2)(1 4)`, `(0 5 1 4 2)`, `(0 5 2 1 4)`, `(0 5)(1
4 2)`, `(0 5 1 4)`, `(0 5)(1 4)`. -/
def pES560 : Fin 6 → Fin 6 := id
def pES561 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pES562 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5
def pES563 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 5 | 5 => 2
def pES564 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 2 | 5 => 4
def pES565 : Fin 6 → Fin 6 | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 4 | 5 => 2
def pES566 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5
def pES567 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4
def pES568 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5
def pES569 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 5 | 5 => 1
def pES5610 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 4
def pES5611 : Fin 6 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 3 | 4 => 4 | 5 => 1
def pES5612 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5
def pES5613 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 2
def pES5614 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5
def pES5615 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 1
def pES5616 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 2
def pES5617 : Fin 6 → Fin 6 | 0 => 0 | 1 => 4 | 2 => 5 | 3 => 3 | 4 => 2 | 5 => 1
def pES5618 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 4
def pES5619 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 2
def pES5620 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 4
def pES5621 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 1
def pES5622 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 2
def pES5623 : Fin 6 → Fin 6 | 0 => 0 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 1
def pES5624 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
def pES5625 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4
def pES5626 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5
def pES5627 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 5 | 5 => 2
def pES5628 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 3 | 4 => 2 | 5 => 4
def pES5629 : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 3 | 4 => 4 | 5 => 2
def pES5630 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5
def pES5631 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 4
def pES5632 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5
def pES5633 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 5 | 5 => 0
def pES5634 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 5 | 3 => 3 | 4 => 0 | 5 => 4
def pES5635 : Fin 6 → Fin 6 | 0 => 1 | 1 => 2 | 2 => 5 | 3 => 3 | 4 => 4 | 5 => 0
def pES5636 : Fin 6 → Fin 6 | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 5
def pES5637 : Fin 6 → Fin 6 | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 2
def pES5638 : Fin 6 → Fin 6 | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5
def pES5639 : Fin 6 → Fin 6 | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 0
def pES5640 : Fin 6 → Fin 6 | 0 => 1 | 1 => 4 | 2 => 5 | 3 => 3 | 4 => 0 | 5 => 2
def pES5641 : Fin 6 → Fin 6 | 0 => 1 | 1 => 4 | 2 => 5 | 3 => 3 | 4 => 2 | 5 => 0
def pES5642 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 4
def pES5643 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 2
def pES5644 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 4
def pES5645 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 0
def pES5646 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 2
def pES5647 : Fin 6 → Fin 6 | 0 => 1 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 0
def pES5648 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5
def pES5649 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4
def pES5650 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5
def pES5651 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 5 | 5 => 1
def pES5652 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 4
def pES5653 : Fin 6 → Fin 6 | 0 => 2 | 1 => 0 | 2 => 5 | 3 => 3 | 4 => 4 | 5 => 1
def pES5654 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5
def pES5655 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 4
def pES5656 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5
def pES5657 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 5 | 5 => 0
def pES5658 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 0 | 5 => 4
def pES5659 : Fin 6 → Fin 6 | 0 => 2 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 4 | 5 => 0
def pES5660 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 5
def pES5661 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 1
def pES5662 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 5
def pES5663 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 0
def pES5664 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 5 | 3 => 3 | 4 => 0 | 5 => 1
def pES5665 : Fin 6 → Fin 6 | 0 => 2 | 1 => 4 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 0
def pES5666 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 4
def pES5667 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 1
def pES5668 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 4
def pES5669 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 0
def pES5670 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 1
def pES5671 : Fin 6 → Fin 6 | 0 => 2 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 0
def pES5672 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5
def pES5673 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 2
def pES5674 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5
def pES5675 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 1
def pES5676 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 2
def pES5677 : Fin 6 → Fin 6 | 0 => 4 | 1 => 0 | 2 => 5 | 3 => 3 | 4 => 2 | 5 => 1
def pES5678 : Fin 6 → Fin 6 | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 5
def pES5679 : Fin 6 → Fin 6 | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 2
def pES5680 : Fin 6 → Fin 6 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5
def pES5681 : Fin 6 → Fin 6 | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 0
def pES5682 : Fin 6 → Fin 6 | 0 => 4 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 0 | 5 => 2
def pES5683 : Fin 6 → Fin 6 | 0 => 4 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 2 | 5 => 0
def pES5684 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 5
def pES5685 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 5 | 5 => 1
def pES5686 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 5
def pES5687 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 0
def pES5688 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 5 | 3 => 3 | 4 => 0 | 5 => 1
def pES5689 : Fin 6 → Fin 6 | 0 => 4 | 1 => 2 | 2 => 5 | 3 => 3 | 4 => 1 | 5 => 0
def pES5690 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 2
def pES5691 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 1
def pES5692 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 2
def pES5693 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 0
def pES5694 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 1
def pES5695 : Fin 6 → Fin 6 | 0 => 4 | 1 => 5 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 0
def pES5696 : Fin 6 → Fin 6 | 0 => 5 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 4
def pES5697 : Fin 6 → Fin 6 | 0 => 5 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 2
def pES5698 : Fin 6 → Fin 6 | 0 => 5 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 4
def pES5699 : Fin 6 → Fin 6 | 0 => 5 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 1
def pES56100 : Fin 6 → Fin 6 | 0 => 5 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 2
def pES56101 : Fin 6 → Fin 6 | 0 => 5 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 1
def pES56102 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 4
def pES56103 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 2
def pES56104 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 4
def pES56105 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 0
def pES56106 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 2
def pES56107 : Fin 6 → Fin 6 | 0 => 5 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 0
def pES56108 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 4
def pES56109 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 1
def pES56110 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 4
def pES56111 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 0
def pES56112 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 1
def pES56113 : Fin 6 → Fin 6 | 0 => 5 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 0
def pES56114 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 2
def pES56115 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 1
def pES56116 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 2
def pES56117 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 0
def pES56118 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 1
def pES56119 : Fin 6 → Fin 6 | 0 => 5 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 0

def permES56 : Fin 120 → Fin 6 → Fin 6
  | 0 => pES560
  | 1 => pES561
  | 2 => pES562
  | 3 => pES563
  | 4 => pES564
  | 5 => pES565
  | 6 => pES566
  | 7 => pES567
  | 8 => pES568
  | 9 => pES569
  | 10 => pES5610
  | 11 => pES5611
  | 12 => pES5612
  | 13 => pES5613
  | 14 => pES5614
  | 15 => pES5615
  | 16 => pES5616
  | 17 => pES5617
  | 18 => pES5618
  | 19 => pES5619
  | 20 => pES5620
  | 21 => pES5621
  | 22 => pES5622
  | 23 => pES5623
  | 24 => pES5624
  | 25 => pES5625
  | 26 => pES5626
  | 27 => pES5627
  | 28 => pES5628
  | 29 => pES5629
  | 30 => pES5630
  | 31 => pES5631
  | 32 => pES5632
  | 33 => pES5633
  | 34 => pES5634
  | 35 => pES5635
  | 36 => pES5636
  | 37 => pES5637
  | 38 => pES5638
  | 39 => pES5639
  | 40 => pES5640
  | 41 => pES5641
  | 42 => pES5642
  | 43 => pES5643
  | 44 => pES5644
  | 45 => pES5645
  | 46 => pES5646
  | 47 => pES5647
  | 48 => pES5648
  | 49 => pES5649
  | 50 => pES5650
  | 51 => pES5651
  | 52 => pES5652
  | 53 => pES5653
  | 54 => pES5654
  | 55 => pES5655
  | 56 => pES5656
  | 57 => pES5657
  | 58 => pES5658
  | 59 => pES5659
  | 60 => pES5660
  | 61 => pES5661
  | 62 => pES5662
  | 63 => pES5663
  | 64 => pES5664
  | 65 => pES5665
  | 66 => pES5666
  | 67 => pES5667
  | 68 => pES5668
  | 69 => pES5669
  | 70 => pES5670
  | 71 => pES5671
  | 72 => pES5672
  | 73 => pES5673
  | 74 => pES5674
  | 75 => pES5675
  | 76 => pES5676
  | 77 => pES5677
  | 78 => pES5678
  | 79 => pES5679
  | 80 => pES5680
  | 81 => pES5681
  | 82 => pES5682
  | 83 => pES5683
  | 84 => pES5684
  | 85 => pES5685
  | 86 => pES5686
  | 87 => pES5687
  | 88 => pES5688
  | 89 => pES5689
  | 90 => pES5690
  | 91 => pES5691
  | 92 => pES5692
  | 93 => pES5693
  | 94 => pES5694
  | 95 => pES5695
  | 96 => pES5696
  | 97 => pES5697
  | 98 => pES5698
  | 99 => pES5699
  | 100 => pES56100
  | 101 => pES56101
  | 102 => pES56102
  | 103 => pES56103
  | 104 => pES56104
  | 105 => pES56105
  | 106 => pES56106
  | 107 => pES56107
  | 108 => pES56108
  | 109 => pES56109
  | 110 => pES56110
  | 111 => pES56111
  | 112 => pES56112
  | 113 => pES56113
  | 114 => pES56114
  | 115 => pES56115
  | 116 => pES56116
  | 117 => pES56117
  | 118 => pES56118
  | _ => pES56119

def permEinvS56 : Fin 120 → Fin 6 → Fin 6
  | 0 => pES560
  | 1 => pES561
  | 2 => pES562
  | 3 => pES564
  | 4 => pES563
  | 5 => pES565
  | 6 => pES566
  | 7 => pES567
  | 8 => pES5612
  | 9 => pES5618
  | 10 => pES5613
  | 11 => pES5619
  | 12 => pES568
  | 13 => pES5610
  | 14 => pES5614
  | 15 => pES5620
  | 16 => pES5616
  | 17 => pES5622
  | 18 => pES569
  | 19 => pES5611
  | 20 => pES5615
  | 21 => pES5621
  | 22 => pES5617
  | 23 => pES5623
  | 24 => pES5624
  | 25 => pES5625
  | 26 => pES5626
  | 27 => pES5628
  | 28 => pES5627
  | 29 => pES5629
  | 30 => pES5648
  | 31 => pES5649
  | 32 => pES5672
  | 33 => pES5696
  | 34 => pES5673
  | 35 => pES5697
  | 36 => pES5650
  | 37 => pES5652
  | 38 => pES5674
  | 39 => pES5698
  | 40 => pES5676
  | 41 => pES56100
  | 42 => pES5651
  | 43 => pES5653
  | 44 => pES5675
  | 45 => pES5699
  | 46 => pES5677
  | 47 => pES56101
  | 48 => pES5630
  | 49 => pES5631
  | 50 => pES5636
  | 51 => pES5642
  | 52 => pES5637
  | 53 => pES5643
  | 54 => pES5654
  | 55 => pES5655
  | 56 => pES5678
  | 57 => pES56102
  | 58 => pES5679
  | 59 => pES56103
  | 60 => pES5660
  | 61 => pES5666
  | 62 => pES5684
  | 63 => pES56108
  | 64 => pES5690
  | 65 => pES56114
  | 66 => pES5661
  | 67 => pES5667
  | 68 => pES5685
  | 69 => pES56109
  | 70 => pES5691
  | 71 => pES56115
  | 72 => pES5632
  | 73 => pES5634
  | 74 => pES5638
  | 75 => pES5644
  | 76 => pES5640
  | 77 => pES5646
  | 78 => pES5656
  | 79 => pES5658
  | 80 => pES5680
  | 81 => pES56104
  | 82 => pES5682
  | 83 => pES56106
  | 84 => pES5662
  | 85 => pES5668
  | 86 => pES5686
  | 87 => pES56110
  | 88 => pES5692
  | 89 => pES56116
  | 90 => pES5664
  | 91 => pES5670
  | 92 => pES5688
  | 93 => pES56112
  | 94 => pES5694
  | 95 => pES56118
  | 96 => pES5633
  | 97 => pES5635
  | 98 => pES5639
  | 99 => pES5645
  | 100 => pES5641
  | 101 => pES5647
  | 102 => pES5657
  | 103 => pES5659
  | 104 => pES5681
  | 105 => pES56105
  | 106 => pES5683
  | 107 => pES56107
  | 108 => pES5663
  | 109 => pES5669
  | 110 => pES5687
  | 111 => pES56111
  | 112 => pES5693
  | 113 => pES56117
  | 114 => pES5665
  | 115 => pES5671
  | 116 => pES5689
  | 117 => pES56113
  | 118 => pES5695
  | _ => pES56119

/-- The group as permutations. `Magma.IsEndo.of_definable` needs invertibility; `Magma.permOf`
supplies it without putting a coercion on the hot path. -/
def eES56 (i : Fin 120) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permES56 i) (permEinvS56 i) (by revert i; decide)

/-- The permutation that must *not* be an automorphism: `(0 3)(1 4 2)`. Every subgroup properly
containing the group above contains it, so a magma admitting the group and not this has that group
as its automorphism group exactly. -/
def pXS560 : Fin 6 → Fin 6 | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5
def pXS560inv : Fin 6 → Fin 6 | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5

def permXS56 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXS560

def permXinvS56 : Fin 1 → Fin 6 → Fin 6
  | 0 => pXS560inv

def eXS56 (i : Fin 1) : Equiv.Perm (Fin 6) :=
  Magma.permOf (permXS56 i) (permXinvS56 i) (by revert i; decide)

/-- One representative per orbit of the group on the `36` cells; there are `5`, so an invariant
operation is `5` values. -/
def repS56 : Fin 5 → Fin 6 × Fin 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 3)
  | 3 => (3, 0)
  | 4 => (3, 3)

/-- For each cell, its orbit and a group element carrying that orbit's representative to it. -/
def trS56 : Fin 6 → Fin 6 → Fin 5 × Fin 120
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 0)
  | 0, 2 => (1, 6)
  | 0, 3 => (2, 0)
  | 0, 4 => (1, 12)
  | 0, 5 => (1, 18)
  | 1, 0 => (1, 24)
  | 1, 1 => (0, 24)
  | 1, 2 => (1, 30)
  | 1, 3 => (2, 24)
  | 1, 4 => (1, 36)
  | 1, 5 => (1, 42)
  | 2, 0 => (1, 48)
  | 2, 1 => (1, 54)
  | 2, 2 => (0, 48)
  | 2, 3 => (2, 48)
  | 2, 4 => (1, 60)
  | 2, 5 => (1, 66)
  | 3, 0 => (3, 0)
  | 3, 1 => (3, 24)
  | 3, 2 => (3, 48)
  | 3, 3 => (4, 0)
  | 3, 4 => (3, 72)
  | 3, 5 => (3, 96)
  | 4, 0 => (1, 72)
  | 4, 1 => (1, 78)
  | 4, 2 => (1, 84)
  | 4, 3 => (2, 72)
  | 4, 4 => (0, 72)
  | 4, 5 => (1, 90)
  | 5, 0 => (1, 96)
  | 5, 1 => (1, 102)
  | 5, 2 => (1, 108)
  | 5, 3 => (2, 96)
  | 5, 4 => (1, 114)
  | 5, 5 => (0, 96)

/-- The `24` group elements fixing both coordinates of orbit `0`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS560 : Fin 24 → Fin 120
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
def valS560 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The `6` group elements fixing both coordinates of orbit `1`'s representative, and hence its
value: that value must be one of `0`, `1`, `3`, so the orbit is indexed by `Fin 3` instead. -/
def stabIdxS561 : Fin 6 → Fin 120
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
def valS561 : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 3

/-- The `24` group elements fixing both coordinates of orbit `2`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS562 : Fin 24 → Fin 120
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
def valS562 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The `24` group elements fixing both coordinates of orbit `3`'s representative, and hence its
value: that value must be one of `0`, `3`, so the orbit is indexed by `Fin 2` instead. -/
def stabIdxS563 : Fin 24 → Fin 120
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
def valS563 : Fin 2 → Fin 6
  | 0 => 0
  | 1 => 3

/-- The `120` group elements fixing both coordinates of orbit `4`'s representative, and hence its
value: that value must be `3`, so the orbit is indexed by `Fin 1` instead. -/
def stabIdxS564 : Fin 120 → Fin 120
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
  | 71 => 71
  | 72 => 72
  | 73 => 73
  | 74 => 74
  | 75 => 75
  | 76 => 76
  | 77 => 77
  | 78 => 78
  | 79 => 79
  | 80 => 80
  | 81 => 81
  | 82 => 82
  | 83 => 83
  | 84 => 84
  | 85 => 85
  | 86 => 86
  | 87 => 87
  | 88 => 88
  | 89 => 89
  | 90 => 90
  | 91 => 91
  | 92 => 92
  | 93 => 93
  | 94 => 94
  | 95 => 95
  | 96 => 96
  | 97 => 97
  | 98 => 98
  | 99 => 99
  | 100 => 100
  | 101 => 101
  | 102 => 102
  | 103 => 103
  | 104 => 104
  | 105 => 105
  | 106 => 106
  | 107 => 107
  | 108 => 108
  | 109 => 109
  | 110 => 110
  | 111 => 111
  | 112 => 112
  | 113 => 113
  | 114 => 114
  | 115 => 115
  | 116 => 116
  | 117 => 117
  | 118 => 118
  | _ => 119
def valS564 : Fin 1 → Fin 6
  | 0 => 3

/-- The `5` orbit values named by the family's arguments. -/
def decS56 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1) : Fin 5 → Fin 6
  | 0 => valS560 a
  | 1 => valS561 b
  | 2 => valS562 c
  | 3 => valS563 d
  | 4 => valS564 e

/-- The invariant operation with those orbit values, written out cell by cell. This is
`Magma.transport` specialised (`tabS56_eq_transport`); writing it out is what keeps a lookup to a
single match. -/
def tabS56 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1) : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => valS560 a
  | 0, 1 => valS561 b
  | 0, 2 => pES566 (valS561 b)
  | 0, 3 => valS562 c
  | 0, 4 => pES5612 (valS561 b)
  | 0, 5 => pES5618 (valS561 b)
  | 1, 0 => pES5624 (valS561 b)
  | 1, 1 => pES5624 (valS560 a)
  | 1, 2 => pES5630 (valS561 b)
  | 1, 3 => pES5624 (valS562 c)
  | 1, 4 => pES5636 (valS561 b)
  | 1, 5 => pES5642 (valS561 b)
  | 2, 0 => pES5648 (valS561 b)
  | 2, 1 => pES5654 (valS561 b)
  | 2, 2 => pES5648 (valS560 a)
  | 2, 3 => pES5648 (valS562 c)
  | 2, 4 => pES5660 (valS561 b)
  | 2, 5 => pES5666 (valS561 b)
  | 3, 0 => valS563 d
  | 3, 1 => pES5624 (valS563 d)
  | 3, 2 => pES5648 (valS563 d)
  | 3, 3 => valS564 e
  | 3, 4 => pES5672 (valS563 d)
  | 3, 5 => pES5696 (valS563 d)
  | 4, 0 => pES5672 (valS561 b)
  | 4, 1 => pES5678 (valS561 b)
  | 4, 2 => pES5684 (valS561 b)
  | 4, 3 => pES5672 (valS562 c)
  | 4, 4 => pES5672 (valS560 a)
  | 4, 5 => pES5690 (valS561 b)
  | 5, 0 => pES5696 (valS561 b)
  | 5, 1 => pES56102 (valS561 b)
  | 5, 2 => pES56108 (valS561 b)
  | 5, 3 => pES5696 (valS562 c)
  | 5, 4 => pES56114 (valS561 b)
  | 5, 5 => pES5696 (valS560 a)

theorem tabS56_eq_transport (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1) :
    tabS56 a b c d e = Magma.transport permES56 trS56 (decS56 a b c d e) := by
  funext x y; fin_cases x <;> fin_cases y <;> rfl


/-- The `22` magmas on `Fin 6` whose automorphism group is exactly this group, listed under one
index. Of the `24` invariant tuples these are the ones the excluded permutations rule out; naming
only them keeps any exactness test off the hot path of a family scan. -/
def memS56 : Fin 22 → Fin 6 → Fin 6 → Fin 6
  | 0 => tabS56 0 0 0 0 0
  | 1 => tabS56 0 0 1 0 0
  | 2 => tabS56 0 0 1 1 0
  | 3 => tabS56 0 1 0 0 0
  | 4 => tabS56 0 1 0 1 0
  | 5 => tabS56 0 1 1 1 0
  | 6 => tabS56 0 2 0 0 0
  | 7 => tabS56 0 2 0 1 0
  | 8 => tabS56 0 2 1 0 0
  | 9 => tabS56 0 2 1 1 0
  | 10 => tabS56 1 0 0 0 0
  | 11 => tabS56 1 0 0 1 0
  | 12 => tabS56 1 0 1 0 0
  | 13 => tabS56 1 0 1 1 0
  | 14 => tabS56 1 1 0 0 0
  | 15 => tabS56 1 1 0 1 0
  | 16 => tabS56 1 1 1 0 0
  | 17 => tabS56 1 1 1 1 0
  | 18 => tabS56 1 2 0 0 0
  | 19 => tabS56 1 2 0 1 0
  | 20 => tabS56 1 2 1 0 0
  | _ => tabS56 1 2 1 1 0

/-- Which of the `22` members a given invariant tuple is, so that `mem_of_isExactS56` can name one
rather than search the list for it. Read only by `native_decide`. -/
def rankArrS56 : Array Nat := #[
  0, 0, 1, 2, 3, 4, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

/-- The arguments as one mixed-radix index, which is how `rankArrS56` is addressed. -/
def encTS56 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1) : Nat :=
  a.1 * 12 +
    b.1 * 4 +
    c.1 * 2 +
    d.1 +
    e.1

/-- The member index of the tuple the arguments name. The `min` is what makes the bound free; on a
tuple the table really names it changes nothing. -/
def rankS56 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1) : Fin 22 :=
  ⟨min (rankArrS56.getD (encTS56 a b c d e) 0) 21, by omega⟩


/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def exactS56 (i : Fin 22) : Magma (Fin 6) := Magma.mk (memS56 i)

theorem exactS56_isEndo (i : Fin 22) (j : Fin 120) : (exactS56 i).IsEndo ⇑(eES56 j) := by
  simp only [eES56, coe_permOf]; revert i j; native_decide

theorem exactS56_not_isEndo (i : Fin 22) (j : Fin 1) : ¬ (exactS56 i).IsEndo ⇑(eXS56 j) := by
  simp only [eXS56, coe_permOf]; revert i j; native_decide

/-- `rankS56` really does name the member a tuple is. Deciding this is one array read and one table
comparison per tuple, where searching `memS56` for the index would be a comparison per tuple and
member. -/
theorem mem_rankS56 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1)
    (h : Magma.isExact (tabS56 a b c d e) permES56 permXS56 = true) :
    memS56 (rankS56 a b c d e) = tabS56 a b c d e := by
  revert h; revert a b c d e; native_decide

/-- Every invariant tuple that really does have this automorphism group names one of the `22` listed
members. -/
theorem mem_of_isExactS56 (a : Fin 2) (b : Fin 3) (c d : Fin 2) (e : Fin 1)
    (h : Magma.isExact (tabS56 a b c d e) permES56 permXS56 = true) :
    ∃ i, memS56 i = tabS56 a b c d e :=
  ⟨_, mem_rankS56 a b c d e h⟩

/-- A magma on `Fin 6` admitting every element of the group and none of the excluded permutations
*is* a member of `Magma.exactS56`. Its values at the orbit representatives name an invariant tuple,
and `mem_of_isExactS56` turns that into a member index. -/
theorem exists_exactS56 {M : Magma (Fin 6)} (hE : ∀ i, M.IsEndo ⇑(eES56 i))
    (hX : ∀ i, ¬ M.IsEndo ⇑(eXS56 i)) : ∃ i, exactS56 i = M := by
  simp only [eES56, coe_permOf] at hE
  simp only [eXS56, coe_permOf] at hX
  have hop : M.op = Magma.transport permES56 trS56 (fun i ↦ M.op (repS56 i).1 (repS56 i).2) :=
    Magma.op_eq_transport (rep := repS56) hE (by decide)
  obtain ⟨a, ha⟩ := Magma.exists_val_of_isEndo
    (E := permES56) (idx := stabIdxS560) (a := (repS56 0).1) (b := (repS56 0).2)
    (val := valS560) hE (by decide) (by decide)
  obtain ⟨b, hb⟩ := Magma.exists_val_of_isEndo
    (E := permES56) (idx := stabIdxS561) (a := (repS56 1).1) (b := (repS56 1).2)
    (val := valS561) hE (by decide) (by decide)
  obtain ⟨c, hc⟩ := Magma.exists_val_of_isEndo
    (E := permES56) (idx := stabIdxS562) (a := (repS56 2).1) (b := (repS56 2).2)
    (val := valS562) hE (by decide) (by decide)
  obtain ⟨d, hd⟩ := Magma.exists_val_of_isEndo
    (E := permES56) (idx := stabIdxS563) (a := (repS56 3).1) (b := (repS56 3).2)
    (val := valS563) hE (by decide) (by decide)
  obtain ⟨e, he⟩ := Magma.exists_val_of_isEndo
    (E := permES56) (idx := stabIdxS564) (a := (repS56 4).1) (b := (repS56 4).2)
    (val := valS564) hE (by decide) (by decide)
  have hdec : decS56 a b c d e = fun i ↦ M.op (repS56 i).1 (repS56 i).2 := by
    funext i; fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
  have key : tabS56 a b c d e = M.op := by
    rw [tabS56_eq_transport, hdec, ← hop]
  have hok : Magma.isExact (tabS56 a b c d e) permES56 permXS56 = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨i, hi⟩ := mem_of_isExactS56 a b c d e hok
  exact ⟨i, (congrArg Magma.mk (hi.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`Aut` certificate on `Fin 6`.** If `L'` has a model on `Fin 6` whose automorphism
group is exactly the order-`120` group of `Magma.permES56`, and no such magma satisfies `L`, then
`L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_exactS56 {L L' : Law.NatMagmaLaw} {i : Fin 22}
    (hsrc : @satisfies _ (Fin 6) (Magma.exactS56 i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 6) (Magma.exactS56 j) L) :
    ¬ L.StructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.exactS56 i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_exactS56
    (fun k ↦ (Magma.exactS56_isEndo i k).of_definable hfwd)
    (fun k hn ↦ Magma.exactS56_not_isEndo i k (hn.of_definable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw

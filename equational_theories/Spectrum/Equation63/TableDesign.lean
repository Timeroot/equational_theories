import equational_theories.Spectrum.Equation63.FieldDesign
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

/-! Linear-size certificates for finite transversal designs. Sorting the pair
images checks bijectivity without comparing every pair of blocks. -/
namespace Spectrum.E63.TableDesign
open Classical
variable {I : Type*} {q : ℕ}

def pairCodes (coord : Fin (q*q) → I → Fin q) (i j : I) : List Nat :=
  (List.finRange (q*q)).map fun t => q*(coord t i).val+(coord t j).val

def Checked (coord : Fin (q*q) → I → Fin q) : Prop :=
  ∀ i j, i ≠ j → (pairCodes coord i j).mergeSort (fun a b => a ≤ b) = List.range (q*q)

theorem pair_injective (coord : Fin (q*q) → I → Fin q) (h : Checked coord)
    (i j : I) (hij : i ≠ j) : Function.Injective (fun t => (coord t i,coord t j)) := by
  have hn : (pairCodes coord i j).Nodup := by
    apply List.nodup_mergeSort.mp
    rw [h i j hij]
    exact List.nodup_range
  intro a b he
  apply List.inj_on_of_nodup_map hn (by simp) (by simp)
  have hi := congrArg Prod.fst he
  have hj := congrArg Prod.snd he
  dsimp only at hi hj
  simp only [hi,hj]

noncomputable def design (coord : Fin (q*q) → I → Fin q) (h : Checked coord) :
    Transversal I (Fin q) (Fin (q*q)) where
  coord := coord
  pair i j hij x y := by
    have hb := (Fintype.bijective_iff_injective_and_card
      (fun t => (coord t i,coord t j))).mpr
      ⟨pair_injective coord h i j hij,by simp⟩
    obtain ⟨t,ht⟩ := hb.surjective (x,y)
    refine ⟨t, ⟨congrArg Prod.fst ht,congrArg Prod.snd ht⟩, ?_⟩
    intro u hu
    exact hb.injective ((Prod.ext hu.1 hu.2).trans ht.symm)

end Spectrum.E63.TableDesign

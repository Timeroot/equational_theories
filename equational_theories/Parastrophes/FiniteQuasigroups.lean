import equational_theories.Definability.DivisionCover
import equational_theories.Spectrum.Equation667883Small.Basic
import equational_theories.Definability.E63Family
import equational_theories.Definability.QuasigroupCover
import equational_theories.Definability.QuasigroupInverse
import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.All
import equational_theories.Spectrum.SmallOrders.Chain
import equational_theories.Definability.Cancel1516

/-! Finite quasigroup results: a factor of a permutation of a finite set is a
permutation. The identities below exhibit both translations as such factors.
Finiteness is essential and is retained in every registered conclusion. -/
namespace Parastrophes

/-- Every factor of a three-factor identity on a finite set is bijective. -/
theorem bijective_middle {G : Type*} [Finite G] (f g h : G → G)
    (heq : ∀ x, f (g (h x)) = x) : Function.Bijective g := by
  have hi : Function.Injective h := by
    intro a b hab
    simpa only [heq] using congrArg (fun x => f (g x)) hab
  have hs := Finite.surjective_of_injective hi
  have hg : Function.Injective g := by
    intro a b hab
    obtain ⟨u, rfl⟩ := hs a
    obtain ⟨v, rfl⟩ := hs b
    exact congrArg h (by simpa only [heq] using congrArg f hab)
  exact ⟨hg, Finite.surjective_of_injective hg⟩

namespace Catalogue

/-- Both translations occur in the identity chain of E73. -/
@[parastrophe_result] theorem quasigroup73_fin : QuasigroupLaw .fin Law73 := by
  intro G M hG h
  letI : Finite G := hG
  have hE := (@Law73.models_iff G M).mp h
  constructor
  · intro y
    exact bijective_middle (fun z => z) (fun x => M.op y x)
      (fun x => (M.op y (M.op x y))) (fun x => (hE x y).symm)
  · intro y
    exact bijective_middle (fun z => (M.op y (M.op y z))) (fun x => M.op x y)
      (fun x => x) (fun x => (hE x y).symm)

/-- Both translations occur in the identity chain of E511. -/
@[parastrophe_result] theorem quasigroup511_fin : QuasigroupLaw .fin Law511 := by
  intro G M hG h
  letI : Finite G := hG
  have hE := (@Law511.models_iff G M).mp h
  constructor
  · intro y
    exact bijective_middle (fun z => z) (fun x => M.op y x)
      (fun x => (M.op y (M.op y (M.op x y)))) (fun x => (hE x y).symm)
  · intro y
    exact bijective_middle (fun z => (M.op y (M.op y (M.op y z)))) (fun x => M.op x y)
      (fun x => x) (fun x => (hE x y).symm)

/-- Both translations occur in the identity chain of E707. -/
@[parastrophe_result] theorem quasigroup707_fin : QuasigroupLaw .fin Law707 := by
  intro G M hG h
  letI : Finite G := hG
  have hE := (@Law707.models_iff G M).mp h
  constructor
  · intro y
    exact bijective_middle (fun z => z) (fun x => M.op y x)
      (fun x => (M.op y (M.op (M.op x y) y))) (fun x => (hE x y).symm)
  · intro y
    exact bijective_middle (fun z => (M.op y (M.op y z))) (fun x => M.op x y)
      (fun x => (M.op x y)) (fun x => (hE x y).symm)

/-- Both translations occur in the identity chain of E883. -/
@[parastrophe_result] theorem quasigroup883_fin : QuasigroupLaw .fin Law883 := by
  intro G M hG h
  letI : Finite G := hG
  have hE := (@Law883.models_iff G M).mp h
  constructor
  · intro y
    exact bijective_middle (fun z => z) (fun x => M.op y x)
      (fun x => (M.op (M.op x y) (M.op y y))) (fun x => (hE x y).symm)
  · intro y
    exact bijective_middle (fun z => (M.op y (M.op z (M.op y y)))) (fun x => M.op x y)
      (fun x => x) (fun x => (hE x y).symm)

/-- Both translations occur in the identity chain of E917. -/
@[parastrophe_result] theorem quasigroup917_fin : QuasigroupLaw .fin Law917 := by
  intro G M hG h
  letI : Finite G := hG
  have hE := (@Law917.models_iff G M).mp h
  constructor
  · intro y
    exact bijective_middle (fun z => z) (fun x => M.op y x)
      (fun x => (M.op (M.op y y) (M.op x y))) (fun x => (hE x y).symm)
  · intro y
    exact bijective_middle (fun z => (M.op y (M.op (M.op y y) z))) (fun x => M.op x y)
      (fun x => x) (fun x => (hE x y).symm)

/-- Both translations occur in the identity chain of E1113. -/
@[parastrophe_result] theorem quasigroup1113_fin : QuasigroupLaw .fin Law1113 := by
  intro G M hG h
  letI : Finite G := hG
  have hE := (@Law1113.models_iff G M).mp h
  constructor
  · intro y
    exact bijective_middle (fun z => z) (fun x => M.op y x)
      (fun x => (M.op (M.op y (M.op x y)) y)) (fun x => (hE x y).symm)
  · intro y
    exact bijective_middle (fun z => (M.op y z)) (fun x => M.op x y)
      (fun x => (M.op y (M.op x y))) (fun x => (hE x y).symm)

/-- The existing Latin-square reduction provides both translations of E1076. -/
@[parastrophe_result] theorem quasigroup1076_fin : QuasigroupLaw .fin Law1076 := by
  intro G M hG h
  letI : Finite G := hG
  have hh := (Spectrum.SmallOrders.holds_iff .e1076 M).mpr h
  exact ⟨Spectrum.SmallOrders.left_bijective hh,
    Spectrum.SmallOrders.right_bijective hh rfl⟩

/-- The existing Latin-square reduction provides both translations of E1083. -/
@[parastrophe_result] theorem quasigroup1083_fin : QuasigroupLaw .fin Law1083 := by
  intro G M hG h
  letI : Finite G := hG
  have hh := (Spectrum.SmallOrders.holds_iff .e1083 M).mpr h
  exact ⟨Spectrum.SmallOrders.left_bijective hh,
    Spectrum.SmallOrders.right_bijective hh rfl⟩

/-- The existing Latin-square reduction provides both translations of E1110. -/
@[parastrophe_result] theorem quasigroup1110_fin : QuasigroupLaw .fin Law1110 := by
  intro G M hG h
  letI : Finite G := hG
  have hh := (Spectrum.SmallOrders.holds_iff .e1110 M).mpr h
  exact ⟨Spectrum.SmallOrders.left_bijective hh,
    Spectrum.SmallOrders.right_bijective hh rfl⟩

/-- The existing Latin-square reduction provides both translations of E1286. -/
@[parastrophe_result] theorem quasigroup1286_fin : QuasigroupLaw .fin Law1286 := by
  intro G M hG h
  letI : Finite G := hG
  have hh := (Spectrum.SmallOrders.holds_iff .e1286 M).mpr h
  exact ⟨Spectrum.SmallOrders.left_bijective hh,
    Spectrum.SmallOrders.right_bijective hh rfl⟩

/-- Both finite cancellation theorems were already proved in Cancel1516. -/
@[parastrophe_result] theorem quasigroup1516_fin : QuasigroupLaw .fin Law1516 := by
  intro G M hG h
  letI : Finite G := hG
  constructor
  · intro x
    have hi := Law.MagmaLaw.cancelLeft_Equation1516 M h x
    exact ⟨hi, Finite.surjective_of_injective hi⟩
  · intro x
    have hi := Law.MagmaLaw.cancelRight_Equation1516 M h x
    exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- Register the cancellation proofs previously used only by division witnesses. -/
@[parastrophe_result] theorem quasigroup467_fin : QuasigroupLaw .fin Law467 := by
  intro G M hG h
  letI : Finite G := hG
  letI : Magma G := M
  have hh := (@Law467.models_iff G M).mp h
  constructor
  · intro x
    have hi := Law.MagmaLaw.inj467L hh x
    exact ⟨hi, Finite.surjective_of_injective hi⟩
  · intro x
    have hi := Law.MagmaLaw.inj467R hh x
    exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- Register the cancellation proofs previously used only by division witnesses. -/
@[parastrophe_result] theorem quasigroup873_fin : QuasigroupLaw .fin Law873 := by
  intro G M hG h
  letI : Finite G := hG
  letI : Magma G := M
  have hh := (@Law873.models_iff G M).mp h
  constructor
  · intro x
    have hi := Law.MagmaLaw.inj873L hh x
    exact ⟨hi, Finite.surjective_of_injective hi⟩
  · intro x
    have hi := Law.MagmaLaw.inj873R hh x
    exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- Existing finite cancellation proofs from DivisionCover. -/
@[parastrophe_result] theorem quasigroup115_fin : QuasigroupLaw .fin Law115 := by
  intro G M hG h
  letI : Finite G := hG
  letI : Magma G := M
  have hh := (@Law115.models_iff G M).mp h
  constructor
  · intro x
    have hi := Law.MagmaLaw.inj115L hh x
    exact ⟨hi, Finite.surjective_of_injective hi⟩
  · intro x
    have hi := Law.MagmaLaw.inj115R hh x
    exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- Existing finite cancellation proofs from DivisionCover. -/
@[parastrophe_result] theorem quasigroup464_fin : QuasigroupLaw .fin Law464 := by
  intro G M hG h
  letI : Finite G := hG
  letI : Magma G := M
  have hh := (@Law464.models_iff G M).mp h
  constructor
  · intro x
    have hi := Law.MagmaLaw.inj464L hh x
    exact ⟨hi, Finite.surjective_of_injective hi⟩
  · intro x
    have hi := Law.MagmaLaw.inj464R hh x
    exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- Existing finite cancellation proofs from DivisionCover. -/
@[parastrophe_result] theorem quasigroup1276_fin : QuasigroupLaw .fin Law1276 := by
  intro G M hG h
  letI : Finite G := hG
  letI : Magma G := M
  have hh := (@Law1276.models_iff G M).mp h
  constructor
  · intro x
    have hi := Law.MagmaLaw.inj1276L hh x
    exact ⟨hi, Finite.surjective_of_injective hi⟩
  · intro x
    have hi := Law.MagmaLaw.inj1276R hh x
    exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- The E667 spectrum proofs already establish both finite translations. -/
@[parastrophe_result] theorem quasigroup667_fin : QuasigroupLaw .fin Law667 := by
  intro G M hG h
  letI : Finite G := hG
  letI : Magma G := M
  have hh := (@Law667.models_iff G M).mp h
  exact ⟨fun x => ⟨Spectrum.E667883.left_injective667 hh x,
    Spectrum.E667883.left_surjective667 hh x⟩,
    fun x => ⟨Spectrum.E667883.right_injective667 hh x,
      Finite.surjective_of_injective (Spectrum.E667883.right_injective667 hh x)⟩⟩

/-- In finite E63, cancellation twice in one row also cancels every column. -/
@[parastrophe_result] theorem quasigroup63_fin : QuasigroupLaw .fin Law63 := by
  intro G M hG h
  letI : Finite G := hG
  letI : Magma G := M
  have hh := (@Law63.models_iff G M).mp h
  have hl (y : G) := E63Family.left_surjective_63 hh y
  have hi (y : G) := Finite.injective_iff_surjective.mpr (hl y)
  refine ⟨fun y => ⟨hi y, hl y⟩, fun y => ?_⟩
  have hr : Function.Injective (fun x => M.op x y) := by
    intro a b hab
    let c := M.op a y
    have ha : M.op c (M.op c a) = y := hi a (hh c a).symm
    have hb : M.op c (M.op c b) = y := hi b ((hh c b).symm.trans hab)
    exact hi c (hi c (ha.trans hb.symm))
  exact ⟨hr, Finite.surjective_of_injective hr⟩

end Catalogue
end Parastrophes

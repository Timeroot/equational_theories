import equational_theories.Definability.FiniteBridge
import equational_theories.Equations.All
import Mathlib.Tactic.FinCases

/-! A 32-element E1483 cover has only two automorphisms, so it cannot be
untwisted into E1485 by an automorphism of order dividing three. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1483.NoCubicUntwist

private def rows : Fin 32 → Nat := ![0xef79ce73bdef79ce73bde73bdef79ce73bdef79c, 0xfffdef7bfffffdef7bfff7bfffffdef7bfffffde, 0xef79ce73bdef79ce73bde73bdef79ce73bdef79c, 0xfffdef7bfffffdef7bfff7bfffffdef7bfffffde, 0xb5af7b5af7bded6bded6f7bfffffdef7bfffffde, 0xa52b5a52b5ad694ad694e73bdef79ce73bdef79c, 0xb5af7b5af7bded6bded6f7bfffffdef7bfffffde, 0xa52b5a52b5ad694ad694e73bdef79ce73bdef79c, 0x7bdcee73bd739efe73bd739efef79c739efef79c, 0x6b58cf7bff631adf7bff631adfffde631adfffde, 0x7bdcee73bd739efe73bd739efef79c739efef79c, 0x6b58cf7bff631adf7bff631adfffde631adfffde, 0x318e7b5af7318e7bded6739efef79c739efef79c, 0x210a5a52b5210a5ad694631adfffde631adfffde, 0x318e7b5af7318e7bded6739efef79c739efef79c, 0x210a5a52b5210a5ad694631adfffde631adfffde, 0xd6b7bdef5aef79ce73bdd6b7bdef5ae73bdef79c, 0xc6339ce718fffdef7bffc6339ce718f7bfffffde, 0xd6b7bdef5aef79ce73bdd6b7bdef5ae73bdef79c, 0xc6339ce718fffdef7bffc6339ce718f7bfffffde, 0x8c61084231ad694ad694d6b7bdef5af7bfffffde, 0x9ce5294a73bded6bded6c6339ce718e73bdef79c, 0x8c61084231ad694ad694d6b7bdef5af7bfffffde, 0x9ce5294a73bded6bded6c6339ce718e73bdef79c, 0x4a508ce718739eff7bff42129ce718739effffde, 0x5ad4adef5a631ade73bd5296bdef5a631adef79c, 0x4a508ce718739eff7bff42129ce718739effffde, 0x5ad4adef5a631ade73bd5296bdef5a631adef79c, 0x840094a73318e7ad69442129def5a739efef79c, 0x18c4284231210a5bded65296bce718631adfffde, 0x840094a73318e7ad69442129def5a739efef79c, 0x18c4284231210a5bded65296bce718631adfffde]

def operation (x y : Fin 32) : Fin 32 :=
  ⟨(rows x >>> (5 * y.val)) % 32, Nat.mod_lt _ (by decide)⟩

@[implicit_reducible] def source : Magma (Fin 32) := ⟨operation⟩

theorem law1483 : @Equation1483 (Fin 32) source := by decide +kernel

theorem not_law1485 : ¬ @Equation1485 (Fin 32) source := by
  intro h
  have bad := h 4 4 8
  exact (by decide +kernel : (4 : Fin 32) ≠ operation (operation 4 4) (operation 4 (operation 8 4))) bad

def flip (x : Fin 32) : Fin 32 := ⟨(x.val ^^^ 3) % 32, Nat.mod_lt _ (by decide)⟩
theorem flip_hom : ∀ x y, flip (operation x y) = operation (flip x) (flip y) := by
  decide +kernel
theorem flip_two : ∀ x, flip (flip x) = x := by decide +kernel

private def w27 (a _b : Fin 32) := a
private def w31 (_a b : Fin 32) := b
private def w11 (a b : Fin 32) := operation (w27 a b) (w31 a b)
private def w16 (a b : Fin 32) := operation (w31 a b) (w27 a b)
private def w3 (a b : Fin 32) := operation (w31 a b) (w31 a b)
private def w25 (a b : Fin 32) := operation (w31 a b) (w11 a b)
private def w22 (a b : Fin 32) := operation (w31 a b) (w16 a b)
private def w17 (a b : Fin 32) := operation (w31 a b) (w25 a b)
private def w4 (a b : Fin 32) := operation (w31 a b) (w22 a b)
private def w13 (a b : Fin 32) := operation (w31 a b) (w4 a b)
private def w30 (a b : Fin 32) := operation (w11 a b) (w27 a b)
private def w12 (a b : Fin 32) := operation (w11 a b) (w22 a b)
private def w26 (a b : Fin 32) := operation (w16 a b) (w31 a b)
private def w29 (a b : Fin 32) := operation (w16 a b) (w16 a b)
private def w10 (a b : Fin 32) := operation (w25 a b) (w29 a b)
private def w20 (a b : Fin 32) := operation (w22 a b) (w16 a b)
private def w21 (a b : Fin 32) := operation (w22 a b) (w22 a b)
private def w24 (a b : Fin 32) := operation (w17 a b) (w31 a b)
private def w23 (a b : Fin 32) := operation (w4 a b) (w25 a b)
private def w5 (a b : Fin 32) := operation (w13 a b) (w29 a b)
private def w18 (a b : Fin 32) := operation (w30 a b) (w27 a b)
private def w1 (a b : Fin 32) := operation (w30 a b) (w31 a b)
private def w19 (a b : Fin 32) := operation (w30 a b) (w25 a b)
private def w6 (a b : Fin 32) := operation (w30 a b) (w22 a b)
private def w15 (a b : Fin 32) := operation (w30 a b) (w4 a b)
private def w9 (a b : Fin 32) := operation (w30 a b) (w13 a b)
private def w0 (a b : Fin 32) := operation (w30 a b) (w29 a b)
private def w7 (a b : Fin 32) := operation (w30 a b) (w20 a b)
private def w28 (a b : Fin 32) := operation (w30 a b) (w1 a b)
private def w14 (a b : Fin 32) := operation (w30 a b) (w6 a b)
private def w8 (a b : Fin 32) := operation (w30 a b) (w15 a b)
private def w2 (a b : Fin 32) := operation (w29 a b) (w29 a b)

private def candidate (a b : Fin 32) : Fin 32 → Fin 32 :=
  ![w0 a b, w1 a b, w2 a b, w3 a b, w4 a b, w5 a b, w6 a b, w7 a b, w8 a b, w9 a b, w10 a b, w11 a b, w12 a b, w13 a b, w14 a b, w15 a b, w16 a b, w17 a b, w18 a b, w19 a b, w20 a b, w21 a b, w22 a b, w23 a b, w24 a b, w25 a b, w26 a b, w27 a b, w28 a b, w29 a b, w30 a b, w31 a b]

private theorem determined (f : Fin 32 → Fin 32)
    (hf : ∀ x y, f (operation x y) = operation (f x) (f y)) :
    f = candidate (f 27) (f 31) := by
  have h27 : f 27 = w27 (f 27) (f 31) := rfl
  have h31 : f 31 = w31 (f 27) (f 31) := rfl
  have h11 : f 11 = w11 (f 27) (f 31) := by
    change f (operation 27 31) = operation (w27 (f 27) (f 31)) (w31 (f 27) (f 31))
    exact (hf 27 31).trans (congrArg₂ operation h27 h31)
  have h16 : f 16 = w16 (f 27) (f 31) := by
    change f (operation 31 27) = operation (w31 (f 27) (f 31)) (w27 (f 27) (f 31))
    exact (hf 31 27).trans (congrArg₂ operation h31 h27)
  have h3 : f 3 = w3 (f 27) (f 31) := by
    change f (operation 31 31) = operation (w31 (f 27) (f 31)) (w31 (f 27) (f 31))
    exact (hf 31 31).trans (congrArg₂ operation h31 h31)
  have h25 : f 25 = w25 (f 27) (f 31) := by
    change f (operation 31 11) = operation (w31 (f 27) (f 31)) (w11 (f 27) (f 31))
    exact (hf 31 11).trans (congrArg₂ operation h31 h11)
  have h22 : f 22 = w22 (f 27) (f 31) := by
    change f (operation 31 16) = operation (w31 (f 27) (f 31)) (w16 (f 27) (f 31))
    exact (hf 31 16).trans (congrArg₂ operation h31 h16)
  have h17 : f 17 = w17 (f 27) (f 31) := by
    change f (operation 31 25) = operation (w31 (f 27) (f 31)) (w25 (f 27) (f 31))
    exact (hf 31 25).trans (congrArg₂ operation h31 h25)
  have h4 : f 4 = w4 (f 27) (f 31) := by
    change f (operation 31 22) = operation (w31 (f 27) (f 31)) (w22 (f 27) (f 31))
    exact (hf 31 22).trans (congrArg₂ operation h31 h22)
  have h13 : f 13 = w13 (f 27) (f 31) := by
    change f (operation 31 4) = operation (w31 (f 27) (f 31)) (w4 (f 27) (f 31))
    exact (hf 31 4).trans (congrArg₂ operation h31 h4)
  have h30 : f 30 = w30 (f 27) (f 31) := by
    change f (operation 11 27) = operation (w11 (f 27) (f 31)) (w27 (f 27) (f 31))
    exact (hf 11 27).trans (congrArg₂ operation h11 h27)
  have h12 : f 12 = w12 (f 27) (f 31) := by
    change f (operation 11 22) = operation (w11 (f 27) (f 31)) (w22 (f 27) (f 31))
    exact (hf 11 22).trans (congrArg₂ operation h11 h22)
  have h26 : f 26 = w26 (f 27) (f 31) := by
    change f (operation 16 31) = operation (w16 (f 27) (f 31)) (w31 (f 27) (f 31))
    exact (hf 16 31).trans (congrArg₂ operation h16 h31)
  have h29 : f 29 = w29 (f 27) (f 31) := by
    change f (operation 16 16) = operation (w16 (f 27) (f 31)) (w16 (f 27) (f 31))
    exact (hf 16 16).trans (congrArg₂ operation h16 h16)
  have h10 : f 10 = w10 (f 27) (f 31) := by
    change f (operation 25 29) = operation (w25 (f 27) (f 31)) (w29 (f 27) (f 31))
    exact (hf 25 29).trans (congrArg₂ operation h25 h29)
  have h20 : f 20 = w20 (f 27) (f 31) := by
    change f (operation 22 16) = operation (w22 (f 27) (f 31)) (w16 (f 27) (f 31))
    exact (hf 22 16).trans (congrArg₂ operation h22 h16)
  have h21 : f 21 = w21 (f 27) (f 31) := by
    change f (operation 22 22) = operation (w22 (f 27) (f 31)) (w22 (f 27) (f 31))
    exact (hf 22 22).trans (congrArg₂ operation h22 h22)
  have h24 : f 24 = w24 (f 27) (f 31) := by
    change f (operation 17 31) = operation (w17 (f 27) (f 31)) (w31 (f 27) (f 31))
    exact (hf 17 31).trans (congrArg₂ operation h17 h31)
  have h23 : f 23 = w23 (f 27) (f 31) := by
    change f (operation 4 25) = operation (w4 (f 27) (f 31)) (w25 (f 27) (f 31))
    exact (hf 4 25).trans (congrArg₂ operation h4 h25)
  have h5 : f 5 = w5 (f 27) (f 31) := by
    change f (operation 13 29) = operation (w13 (f 27) (f 31)) (w29 (f 27) (f 31))
    exact (hf 13 29).trans (congrArg₂ operation h13 h29)
  have h18 : f 18 = w18 (f 27) (f 31) := by
    change f (operation 30 27) = operation (w30 (f 27) (f 31)) (w27 (f 27) (f 31))
    exact (hf 30 27).trans (congrArg₂ operation h30 h27)
  have h1 : f 1 = w1 (f 27) (f 31) := by
    change f (operation 30 31) = operation (w30 (f 27) (f 31)) (w31 (f 27) (f 31))
    exact (hf 30 31).trans (congrArg₂ operation h30 h31)
  have h19 : f 19 = w19 (f 27) (f 31) := by
    change f (operation 30 25) = operation (w30 (f 27) (f 31)) (w25 (f 27) (f 31))
    exact (hf 30 25).trans (congrArg₂ operation h30 h25)
  have h6 : f 6 = w6 (f 27) (f 31) := by
    change f (operation 30 22) = operation (w30 (f 27) (f 31)) (w22 (f 27) (f 31))
    exact (hf 30 22).trans (congrArg₂ operation h30 h22)
  have h15 : f 15 = w15 (f 27) (f 31) := by
    change f (operation 30 4) = operation (w30 (f 27) (f 31)) (w4 (f 27) (f 31))
    exact (hf 30 4).trans (congrArg₂ operation h30 h4)
  have h9 : f 9 = w9 (f 27) (f 31) := by
    change f (operation 30 13) = operation (w30 (f 27) (f 31)) (w13 (f 27) (f 31))
    exact (hf 30 13).trans (congrArg₂ operation h30 h13)
  have h0 : f 0 = w0 (f 27) (f 31) := by
    change f (operation 30 29) = operation (w30 (f 27) (f 31)) (w29 (f 27) (f 31))
    exact (hf 30 29).trans (congrArg₂ operation h30 h29)
  have h7 : f 7 = w7 (f 27) (f 31) := by
    change f (operation 30 20) = operation (w30 (f 27) (f 31)) (w20 (f 27) (f 31))
    exact (hf 30 20).trans (congrArg₂ operation h30 h20)
  have h28 : f 28 = w28 (f 27) (f 31) := by
    change f (operation 30 1) = operation (w30 (f 27) (f 31)) (w1 (f 27) (f 31))
    exact (hf 30 1).trans (congrArg₂ operation h30 h1)
  have h14 : f 14 = w14 (f 27) (f 31) := by
    change f (operation 30 6) = operation (w30 (f 27) (f 31)) (w6 (f 27) (f 31))
    exact (hf 30 6).trans (congrArg₂ operation h30 h6)
  have h8 : f 8 = w8 (f 27) (f 31) := by
    change f (operation 30 15) = operation (w30 (f 27) (f 31)) (w15 (f 27) (f 31))
    exact (hf 30 15).trans (congrArg₂ operation h30 h15)
  have h2 : f 2 = w2 (f 27) (f 31) := by
    change f (operation 29 29) = operation (w29 (f 27) (f 31)) (w29 (f 27) (f 31))
    exact (hf 29 29).trans (congrArg₂ operation h29 h29)
  funext x
  fin_cases x
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24
  · exact h25
  · exact h26
  · exact h27
  · exact h28
  · exact h29
  · exact h30
  · exact h31

private theorem pair_cases : ∀ a b : Fin 32, a ≠ b →
    candidate a b 25 = operation (candidate a b 24) (candidate a b 26) →
    candidate a b 21 = operation (candidate a b 5) (candidate a b 24) →
    (a = 27 ∧ b = 31) ∨ (a = 24 ∧ b = 28) := by
  decide +kernel

private theorem candidate_id : candidate 27 31 = id := by decide +kernel
private theorem candidate_flip : candidate 24 28 = flip := by decide +kernel

theorem automorphisms (f : Fin 32 → Fin 32) (hi : Function.Injective f)
    (hf : ∀ x y, f (operation x y) = operation (f x) (f y)) :
    f = id ∨ f = flip := by
  have hd := determined f hf
  have hn : f 27 ≠ f 31 := fun h => (by decide : (27 : Fin 32) ≠ 31) (hi h)
  have h1 := hf 24 26
  have h2 := hf 5 24
  rw [hd] at h1 h2
  rcases pair_cases (f 27) (f 31) hn h1 h2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl (hd.trans (by rw [ha, hb]; exact candidate_id))
  · exact Or.inr (hd.trans (by rw [ha, hb]; exact candidate_flip))

theorem cube_automorphism_identity (f : Fin 32 → Fin 32)
    (hf : ∀ x y, f (operation x y) = operation (f x) (f y))
    (hc : ∀ x, f (f (f x)) = x) : f = id := by
  have hi : Function.Injective f := by
    intro x y hxy
    have h := congrArg (fun z => f (f z)) hxy
    simpa only [hc] using h
  rcases automorphisms f hi hf with h | h
  · exact h
  · subst f
    have bad := hc 0
    exact False.elim ((by decide +kernel : flip (flip (flip 0)) ≠ 0) bad)

/-- Even without asking the correction to be definable, no cubic automorphism works. -/
theorem no_cubic_untwist : ¬ ∃ f : Fin 32 → Fin 32,
    (∀ x y, f (operation x y) = operation (f x) (f y)) ∧
    (∀ x, f (f (f x)) = x) ∧
    @Equation1485 (Fin 32) ⟨fun x y => operation (f (f x)) (f y)⟩ := by
  rintro ⟨f, hf, hc, hnew⟩
  have he := cube_automorphism_identity f hf hc
  subst f
  exact not_law1485 hnew

/-- An unrelated E1485 operation: Boolean NAND on three bits times the
natural central operation on two binary coordinates. -/
def companionOperation (x y : Fin 32) : Fin 32 :=
  ⟨(4 * (7 ^^^ ((x.val / 4) &&& (y.val / 4))) +
    2 * (x.val % 2) + (y.val % 4) / 2) % 32, Nat.mod_lt _ (by decide)⟩

@[implicit_reducible] def companion : Magma (Fin 32) := ⟨companionOperation⟩

theorem companion_law : @Equation1485 (Fin 32) companion := by decide +kernel

theorem companion_flip : ∀ x y,
    flip (companionOperation x y) = companionOperation (flip x) (flip y) := by
  decide +kernel

/-- The failure of cubic untwisting is not a finite FO counterexample:
this particular source does admit an FO-definable E1485 operation. -/
theorem companion_definable : Law.MagmaLaw.DefinableOnMagma Law1485 source := by
  refine ⟨companion, (@Law1485.models_iff _ companion).mpr companion_law, ?_⟩
  apply Magma.definable_of_aut_invariant source companion.Graph
  intro σ hbij hhom v hv
  rcases automorphisms σ hbij.1 hhom with rfl | rfl
  · exact hv
  · change companionOperation (flip (v (some 0))) (flip (v (some 1))) = flip (v none)
    rw [← companion_flip]
    exact congrArg flip hv

/-- info: 'Spectrum.E1483.NoCubicUntwist.law1483' depends on axioms: [propext] -/
#guard_msgs in
#print axioms law1483
/-- info: 'Spectrum.E1483.NoCubicUntwist.automorphisms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms automorphisms
/-- info: 'Spectrum.E1483.NoCubicUntwist.no_cubic_untwist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_cubic_untwist
/-- info: 'Spectrum.E1483.NoCubicUntwist.companion_definable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms companion_definable
end Spectrum.E1483.NoCubicUntwist

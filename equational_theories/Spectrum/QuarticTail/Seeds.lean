import equational_theories.Spectrum.PBD.Truncation
import equational_theories.Spectrum.QuarticSeeds

/-! The same cardinality constructions apply to E1076 and E1313. Their
idempotent affine polynomials are related by b ↦ 1-b. -/
namespace Spectrum.QuarticTail
open Classical FreeMagma PBD

def law1076 : BinaryLaw :=
  let x := FreeMagma.Leaf false
  let y := FreeMagma.Leaf true
  ⟨x, y ⋆ ((x ⋆ (x ⋆ y)) ⋆ y)⟩

def law1313 : BinaryLaw :=
  let x := FreeMagma.Leaf false
  let y := FreeMagma.Leaf true
  ⟨x, y ⋆ (((y ⋆ x) ⋆ x) ⋆ y)⟩

structure Seeds (L : BinaryLaw) where
  scalar : ∀ (n b : ℕ), 0 < n →
    (b : ZMod n)^4 - (b : ZMod n)^3 - (b : ZMod n)^2 + (b : ZMod n) - 1 = 0 →
    Nonempty (Model L (Fin n))
  quartic : ∀ n : ℕ, Nonempty (Model L (Fin (n^4)))

def scalar1076 {R : Type*} [CommRing R] (b : R)
    (hb : b^4-b^3-b^2+b-1=0) : Model law1076 R where
  op x y := (1-b)*x+b*y
  idem x := by ring
  law x y := by
    change x = (1-b)*y+b*((1-b)*((1-b)*x+b*((1-b)*x+b*y))+b*y)
    linear_combination (y-x)*hb

def scalar1313 {R : Type*} [CommRing R] (b : R)
    (hb : b^4-b^3-b^2+b-1=0) : Model law1313 R where
  op x y := b*x+(1-b)*y
  idem x := by ring
  law x y := by
    change x = b*y+(1-b)*(b*(b*(b*y+(1-b)*x)+(1-b)*x)+(1-b)*y)
    linear_combination (y-x)*hb

noncomputable def seeds1076 : Seeds law1076 where
  scalar n b hn hb := by
    letI : NeZero n := ⟨by omega⟩
    exact ⟨(scalar1076 (b : ZMod n) hb).transport (ZMod.finEquiv n).toEquiv.symm⟩
  quartic n := by
    by_cases hn : n = 0
    · subst n; exact ⟨Model.empty⟩
    letI : NeZero n := ⟨hn⟩
    let M : Model law1076 (ZMod n × ZMod n × ZMod n × ZMod n) := {
      op := QuarticSeeds.op (-1) 1 (-1) (-1)
      idem := QuarticSeeds.idempotent _ _ _ _
      law := QuarticSeeds.law_1076 }
    exact ⟨M.transport (Fintype.equivFinOfCardEq (by simp [pow_succ, Nat.mul_assoc]))⟩

noncomputable def seeds1313 : Seeds law1313 where
  scalar n b hn hb := by
    letI : NeZero n := ⟨by omega⟩
    exact ⟨(scalar1313 (b : ZMod n) hb).transport (ZMod.finEquiv n).toEquiv.symm⟩
  quartic n := by
    by_cases hn : n = 0
    · subst n; exact ⟨Model.empty⟩
    letI : NeZero n := ⟨hn⟩
    let M : Model law1313 (ZMod n × ZMod n × ZMod n × ZMod n) := {
      op := QuarticSeeds.op (-1) 0 2 (-3)
      idem := QuarticSeeds.idempotent _ _ _ _
      law := QuarticSeeds.law_1313 }
    exact ⟨M.transport (Fintype.equivFinOfCardEq (by simp [pow_succ, Nat.mul_assoc]))⟩

end Spectrum.QuarticTail

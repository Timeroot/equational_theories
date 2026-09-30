import equational_theories.Spectrum.Equation677.EffectiveTail.Affine

/-! Small seeds and affine-certificate interpretation for the effective E677 tail.
The three table seeds are from PR #6. Products, fourth powers, and scalar models
reuse the existing spectrum constructions. -/
namespace Spectrum.E677.EffectiveTail
open Law Law.MagmaLaw
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The nine-element quadratic-field seed, without importing the full catalogue. -/
theorem model9 : Law677.HasModel 9 := by
  have hm : Model (ZMod 3 × ZMod 3) :=
    ⟨fun x y => (x.1+y.2, x.2+y.1+y.2), by decide +kernel, by simp⟩
  exact (hm.relabel (Fintype.equivFinOfCardEq (by simp))).hasModel

private def pack (w : Nat) (l : List Nat) : Nat := l.foldr (fun a acc => acc <<< w ||| a) 0

def plane21Table : List (List Nat) :=
  [[0, 3, 20, 1, 17, 10, 14, 18, 15, 12, 5, 16, 9, 19, 6, 8, 11, 4, 7, 13, 2],
   [20, 1, 3, 2, 8, 12, 10, 19, 4, 14, 6, 18, 5, 16, 9, 17, 13, 15, 11, 7, 0],
   [1, 0, 2, 20, 19, 8, 18, 10, 5, 13, 7, 15, 16, 9, 17, 11, 12, 14, 6, 4, 3],
   [2, 20, 0, 3, 10, 9, 19, 11, 12, 5, 4, 7, 8, 17, 18, 16, 15, 13, 14, 6, 1],
   [12, 16, 15, 14, 4, 20, 7, 6, 13, 17, 18, 19, 0, 8, 3, 2, 1, 9, 10, 11, 5],
   [13, 11, 17, 16, 7, 5, 20, 4, 14, 15, 19, 1, 18, 0, 8, 9, 3, 2, 12, 10, 6],
   [11, 15, 9, 8, 5, 4, 6, 20, 3, 2, 17, 0, 19, 18, 16, 1, 14, 10, 13, 12, 7],
   [8, 14, 16, 17, 20, 6, 5, 7, 0, 19, 12, 13, 10, 11, 1, 18, 2, 3, 15, 9, 4],
   [18, 13, 14, 19, 16, 17, 12, 15, 8, 20, 11, 10, 6, 1, 2, 7, 4, 5, 0, 3, 9],
   [4, 7, 18, 15, 0, 16, 13, 1, 11, 9, 20, 8, 17, 6, 19, 3, 5, 12, 2, 14, 10],
   [19, 17, 12, 18, 14, 13, 15, 16, 9, 8, 10, 20, 2, 5, 4, 6, 7, 1, 3, 0, 11],
   [14, 12, 4, 13, 2, 18, 16, 17, 20, 10, 9, 11, 1, 3, 0, 19, 6, 7, 5, 15, 8],
   [17, 18, 7, 6, 9, 11, 3, 2, 19, 4, 16, 5, 12, 20, 15, 14, 10, 0, 1, 8, 13],
   [10, 4, 6, 7, 1, 19, 2, 3, 16, 18, 0, 17, 15, 13, 20, 12, 8, 11, 9, 5, 14],
   [16, 19, 5, 10, 18, 2, 11, 9, 17, 7, 3, 6, 13, 12, 14, 20, 0, 8, 4, 1, 15],
   [7, 10, 19, 5, 11, 3, 17, 0, 18, 16, 1, 4, 20, 14, 13, 15, 9, 6, 8, 2, 12],
   [6, 8, 10, 9, 13, 15, 0, 12, 1, 3, 2, 14, 7, 4, 11, 5, 16, 20, 19, 18, 17],
   [9, 6, 8, 11, 12, 14, 1, 13, 2, 0, 15, 3, 4, 7, 5, 10, 19, 17, 20, 16, 18],
   [15, 5, 13, 4, 3, 1, 9, 8, 7, 6, 14, 12, 11, 2, 10, 0, 17, 16, 18, 20, 19],
   [5, 9, 11, 12, 15, 0, 8, 14, 6, 1, 13, 2, 3, 10, 7, 4, 20, 18, 17, 19, 16],
   [3, 2, 1, 0, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 20]]

/-- `plane21Table`, five bits an entry. -/
def plane21Packed : Nat := pack 5 plane21Table.flatten


def t79Table : List Nat :=
  [0, 6, 10, 15, 54, 28, 2, 55, 48, 3, 60, 30, 72, 65, 5, 11, 1, 23, 29, 59, 21, 47, 53, 34,
   41, 46, 35, 4, 61, 36, 71, 63, 37, 40, 12, 17, 22, 27, 70, 13, 66, 9, 52, 57, 62, 67, 39,
   42, 16, 8, 43, 18, 75, 44, 33, 38, 45, 26, 32, 58, 20, 50, 56, 78, 68, 74, 14, 7, 49, 19,
   76, 31, 24, 77, 51, 25, 64, 69, 73]

/-- `t79Table`, seven bits an entry. -/
def t79Packed : Nat := pack 7 t79Table


def t127Table : List Nat :=
  [0, 58, 116, 87, 105, 18, 47, 76, 83, 14, 36, 3, 94, 119, 25, 108, 39, 97, 28, 86, 72, 75,
   6, 32, 61, 53, 111, 21, 50, 79, 89, 20, 78, 68, 67, 125, 56, 114, 45, 115, 17, 92, 23, 104,
   12, 35, 64, 59, 122, 48, 106, 82, 95, 13, 42, 71, 100, 2, 31, 60, 51, 109, 40, 49, 29, 107,
   9, 38, 7, 65, 123, 54, 112, 43, 101, 16, 90, 74, 103, 10, 34, 126, 57, 121, 46, 52, 81, 93,
   24, 41, 70, 99, 1, 30, 118, 88, 117, 19, 96, 27, 85, 8, 37, 5, 63, 124, 26, 110, 84, 113,
   15, 44, 73, 77, 4, 66, 62, 55, 120, 22, 102, 33, 91, 11, 80, 69, 98]

/-- `t127Table`, seven bits an entry. -/
def t127Packed : Nat := pack 7 t127Table


def plane21 (x y : Fin 21) : Fin 21 :=
  ⟨((plane21Packed >>> (5 * (21*x.val+y.val))) % 32) % 21, Nat.mod_lt _ (by decide)⟩

/-- A translation-invariant operation needs only one displacement check per element. -/
def translation {A : Type*} [AddCommGroup A] (f : A → A) (x y : A) := x + f (y-x)

theorem translation_lawful {A : Type*} [AddCommGroup A] (f : A → A)
    (hf : ∀ d, f (d + f (-d + f d + f (-f d))) = d) : Lawful (translation f) := by
  intro x y
  dsimp only [translation]
  rw [show y - (y + f (x-y)) = -f (x-y) by abel]
  rw [show y + f (x-y) + f (-f (x-y)) - x = -(x-y) + f (x-y) + f (-f (x-y)) by abel]
  rw [show x + f (-(x-y) + f (x-y) + f (-f (x-y))) - y =
    (x-y) + f (-(x-y) + f (x-y) + f (-f (x-y))) by abel, hf]
  abel

def displacement79 (x : ZMod 79) : ZMod 79 :=
  ((t79Packed >>> (7*x.val)) % 128 : Nat)

def displacement127 (x : ZMod 127) : ZMod 127 :=
  ((t127Packed >>> (7*x.val)) % 128 : Nat)

theorem model21 : Law677.HasModel 21 :=
  ⟨⟨plane21⟩, (@Law677.models_iff _ ⟨plane21⟩).mpr (by decide +kernel)⟩

theorem idem79 : Model (Fin 79) true := by
  have hm : Model (ZMod 79) true := ⟨translation displacement79,
    translation_lawful displacement79 (by decide +kernel), by
      intro _ x
      simp only [translation, sub_self, show displacement79 0 = 0 by decide +kernel, add_zero]⟩
  exact hm.relabel (ZMod.finEquiv 79).toEquiv.symm

theorem model127 : Law677.HasModel 127 := by
  have hm : Model (ZMod 127) := ⟨translation displacement127,
    translation_lawful displacement127 (by decide +kernel), by simp⟩
  exact (hm.relabel (ZMod.finEquiv 127).toEquiv.symm).hasModel

spectrum_assert model21 complete
spectrum_assert idem79 complete
spectrum_assert model127 complete
end Spectrum.E677.EffectiveTail

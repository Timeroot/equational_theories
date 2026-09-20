import DefOrbit.Counting

/-! Compiled evaluator for a complete cyclic projection/kernel family. -/
namespace DefOrbit.NativeProjectionKernel4By11Scalars12345678910
abbrev Point := Fin 4 × Fin 11
def gPlaces : Array Nat := #[1, 4, 16, 64]
def hPlaces : Array Nat := #[1, 11, 121, 1331]
def g (code : Nat) (x : Fin 4) : Fin 4 :=
  ⟨(code / gPlaces.getD x.val 0) % 4, Nat.mod_lt _ (by decide)⟩
def h (code : Nat) (x : Fin 4) : Fin 11 :=
  ⟨(code / hPlaces.getD x.val 0) % 11, Nat.mod_lt _ (by decide)⟩
def valueData : Array (Array (Fin 11)) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], #[0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9], #[0, 3, 6, 9, 1, 4, 7, 10, 2, 5, 8], #[0, 4, 8, 1, 5, 9, 2, 6, 10, 3, 7], #[0, 5, 10, 4, 9, 3, 8, 2, 7, 1, 6], #[0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5], #[0, 7, 3, 10, 6, 2, 9, 5, 1, 8, 4], #[0, 8, 5, 2, 10, 7, 4, 1, 9, 6, 3], #[0, 9, 7, 5, 3, 1, 10, 8, 6, 4, 2], #[0, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]]
def value (i : Fin 11) (x : Fin 11) : Fin 11 :=
  (valueData.getD i.val #[]).getD x.val 0
def op (gc hc : Nat) (x y : Point) : Point :=
  (x.1 + g gc (y.1 - x.1), x.2 + value (h hc (y.1 - x.1)) (y.2 - x.2))
def points : List Point :=
  (List.finRange 4).flatMap fun x => (List.finRange 11).map fun y => (x, y)

abbrev test446 (gc hc : Nat) : Prop := ∀ v0 v1 : Point, (0, 0) = (op gc hc (0, 0) (op gc hc v0 (op gc hc v1 (op gc hc (0, 0) (0, 0)))))
def good446 (code : Nat) : Bool :=
  let gc := code % 256
  let hc := code / 256
  points.all (fun v0 => points.all (fun v1 => decide ((0, 0) = (op gc hc (0, 0) (op gc hc v0 (op gc hc v1 (op gc hc (0, 0) (0, 0))))))))

abbrev test3258 (gc hc : Nat) : Prop := ∀ v0 : Point, (op gc hc (0, 0) (0, 0)) = (op gc hc (0, 0) (op gc hc v0 (op gc hc (0, 0) (0, 0))))
def good3258 (code : Nat) : Bool :=
  let gc := code % 256
  let hc := code / 256
  points.all (fun v0 => decide ((op gc hc (0, 0) (0, 0)) = (op gc hc (0, 0) (op gc hc v0 (op gc hc (0, 0) (0, 0))))))

end DefOrbit.NativeProjectionKernel4By11Scalars12345678910

import equational_theories.Definability.Negative
import equational_theories.Definability.FiniteFlavour
import equational_theories.Spectrum.Equation1486.Encoding8

set_option maxHeartbeats 2000000
namespace Definability.Cyclic1483
open Spectrum.FiniteTableEncoding.N8

def rotate (x : Fin 8) : Fin 8 := ![0, 2, 4, 6, 1, 3, 5, 7] x
def rotateBack (x : Fin 8) : Fin 8 := ![0, 4, 1, 5, 2, 6, 3, 7] x
def rotateEquiv : Fin 8 ≃ Fin 8 where
  toFun := rotate
  invFun := rotateBack
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def reflect0 (x : Fin 8) : Fin 8 := ![0, 1, 4, 6, 2, 5, 3, 7] x
def reflectEquiv0 : Fin 8 ≃ Fin 8 where
  toFun := reflect0
  invFun := reflect0
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def reflect1 (x : Fin 8) : Fin 8 := ![0, 1, 4, 5, 2, 3, 6, 7] x
def reflectEquiv1 : Fin 8 ≃ Fin 8 where
  toFun := reflect1
  invFun := reflect1
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def reflect2 (x : Fin 8) : Fin 8 := ![0, 1, 4, 3, 2, 6, 5, 7] x
def reflectEquiv2 : Fin 8 ≃ Fin 8 where
  toFun := reflect2
  invFun := reflect2
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def operation (x y : Fin 8) : Fin 8 := (![![7, 7, 7, 7, 7, 7, 7, 7], ![7, 7, 7, 7, 5, 5, 5, 5], ![7, 3, 7, 3, 7, 3, 7, 3], ![7, 3, 7, 3, 5, 1, 5, 1], ![7, 7, 6, 6, 7, 7, 6, 6], ![7, 7, 6, 6, 5, 5, 4, 4], ![7, 3, 6, 2, 7, 3, 6, 2], ![7, 3, 6, 2, 5, 1, 4, 0]] x) y
@[implicit_reducible] def source : Magma (Fin 8) := ⟨operation⟩

theorem source_models : @Equation1483 (Fin 8) source := by decide +kernel
theorem source_rotation : source.IsEndo rotateEquiv := by decide +kernel
theorem source_not_reflection0 : ¬ source.IsEndo reflectEquiv0 := by decide +kernel
theorem source_not_reflection1 : ¬ source.IsEndo reflectEquiv1 := by decide +kernel
theorem source_not_reflection2 : ¬ source.IsEndo reflectEquiv2 := by decide +kernel

theorem bv_injective : Function.Injective bv := by
  intro a b h
  exact Fin.ext (congrArg BitVec.toNat h)

end Definability.Cyclic1483

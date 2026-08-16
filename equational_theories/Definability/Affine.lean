import Mathlib.Tactic.Ring
import equational_theories.Definability.Clone

/-!
# Affine clone families

Almost every certificate in `Definability/CloneCerts.lean` is an **affine** magma
`x ◇ y = a x + b y` over a finite ring. Such a magma has a small clone for a structural reason:
a term of it evaluates to `p x + q y`, so the clone is a set of *coefficient pairs* and closure
under composition is the coefficient recursion `(p, q), (p', q') ↦ (a p + b p', a q + b q')`.

That is worth exploiting, because `Magma.IsCloneFamily.comp` quantifies over
`Fin k × Fin k × Fin n × Fin n`; a `Fin 19` certificate with a `19`-element clone is `130321`
equations, and `decide` on that costs gigabytes. The two lemmas here discharge the `∀ x y` part
once and for all by algebra, leaving only the `k ^ 2` coefficient identities to be checked.

`affineFin_isCloneFamily` covers coefficients in `ZMod n`, written out as natural-number
arithmetic modulo `n` so that `decide` sees nothing but machine naturals.
`affineOf_isCloneFamily` covers any other ring, presented as a pair of bare functions together
with the identities the argument actually uses; `Magma.gf16` instantiates it at `GF(16)`, whose
multiplication table is packed four bits per entry into a single numeral for the same reason.
-/

namespace Magma

variable {G : Type}

/-! ### Coefficients in `ZMod n` -/

/-- The affine magma `x ◇ y = a x + b y` on `Fin n`, with the arithmetic done in `ℕ` and reduced
modulo `n`. -/
@[implicit_reducible]
def affineFin (n : ℕ) [NeZero n] (a b : ℕ) : Magma (Fin n) :=
  ⟨fun x y ↦ ⟨(a * x.val + b * y.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩⟩

/-- A family of affine operations on `Fin n` is a clone family for `x ◇ y = a x + b y` as soon as
its coefficients contain `(1, 0)` and `(0, 1)` and compose. Only the coefficients are quantified
over, so this replaces `k ^ 2 * n ^ 2` cases by `k ^ 2`. -/
theorem affineFin_isCloneFamily (n : ℕ) [NeZero n] (a b : ℕ) {k : ℕ} (P Q : Fin k → ℕ)
    (i₁ i₂ : Fin k) (c : Fin k → Fin k → Fin k)
    (hP₁ : P i₁ % n = 1 % n) (hQ₁ : Q i₁ % n = 0 % n)
    (hP₂ : P i₂ % n = 0 % n) (hQ₂ : Q i₂ % n = 1 % n)
    (hc : ∀ i j, P (c i j) % n = (a * P i + b * P j) % n ∧
                 Q (c i j) % n = (a * Q i + b * Q j) % n) :
    (affineFin n a b).IsCloneFamily (fun i ↦ affineFin n (P i) (Q i)) i₁ i₂ c where
  fst x y := by
    refine Fin.ext ?_
    show (P i₁ * x.val + Q i₁ * y.val) % n = x.val
    calc (P i₁ * x.val + Q i₁ * y.val) % n
        = (1 * x.val + 0 * y.val) % n :=
          Nat.ModEq.add (Nat.ModEq.mul_right _ hP₁) (Nat.ModEq.mul_right _ hQ₁)
      _ = x.val := by simpa using Nat.mod_eq_of_lt x.isLt
  snd x y := by
    refine Fin.ext ?_
    show (P i₂ * x.val + Q i₂ * y.val) % n = y.val
    calc (P i₂ * x.val + Q i₂ * y.val) % n
        = (0 * x.val + 1 * y.val) % n :=
          Nat.ModEq.add (Nat.ModEq.mul_right _ hP₂) (Nat.ModEq.mul_right _ hQ₂)
      _ = y.val := by simpa using Nat.mod_eq_of_lt y.isLt
  comp i j x y := by
    obtain ⟨h1, h2⟩ := hc i j
    refine Fin.ext ?_
    show (P (c i j) * x.val + Q (c i j) * y.val) % n
        = (a * ((P i * x.val + Q i * y.val) % n) + b * ((P j * x.val + Q j * y.val) % n)) % n
    have e : (a * ((P i * x.val + Q i * y.val) % n) + b * ((P j * x.val + Q j * y.val) % n)) % n
        = (a * (P i * x.val + Q i * y.val) + b * (P j * x.val + Q j * y.val)) % n :=
      Nat.ModEq.add (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _))
        (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _))
    have r : (a * P i + b * P j) * x.val + (a * Q i + b * Q j) * y.val
        = a * (P i * x.val + Q i * y.val) + b * (P j * x.val + Q j * y.val) := by ring
    rw [e, ← r]
    exact Nat.ModEq.add (Nat.ModEq.mul_right _ h1) (Nat.ModEq.mul_right _ h2)

/-! ### Coefficients in an arbitrary ring -/

/-- `x ◇ y = a ⊗ x ⊕ b ⊗ y`, for an addition and a multiplication given as bare functions. -/
@[implicit_reducible]
def affineOf (add mul : G → G → G) (a b : G) : Magma G := ⟨fun x y ↦ add (mul a x) (mul b y)⟩

/-- `affineFin_isCloneFamily` for coefficients in any structure satisfying the identities the
argument uses. The identities are hypotheses rather than a `Ring` instance because the rings that
come up are carried by `Fin n` with tabulated operations, where each identity is a `decide`. -/
theorem affineOf_isCloneFamily {k : ℕ} (add mul : G → G → G) (zero one : G)
    (hAA : ∀ x y z, add (add x y) z = add x (add y z))
    (hAC : ∀ x y, add x y = add y x)
    (hA0 : ∀ x, add x zero = x)
    (hM1 : ∀ x, mul one x = x)
    (hM0 : ∀ x, mul zero x = zero)
    (hMA : ∀ x y z, mul (mul x y) z = mul x (mul y z))
    (hD : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z))
    (hD' : ∀ x y z, add (mul x z) (mul y z) = mul (add x y) z)
    (a b : G) (P Q : Fin k → G) (i₁ i₂ : Fin k) (c : Fin k → Fin k → Fin k)
    (hP₁ : P i₁ = one) (hQ₁ : Q i₁ = zero) (hP₂ : P i₂ = zero) (hQ₂ : Q i₂ = one)
    (hc : ∀ i j, P (c i j) = add (mul a (P i)) (mul b (P j)) ∧
                 Q (c i j) = add (mul a (Q i)) (mul b (Q j))) :
    (affineOf add mul a b).IsCloneFamily (fun i ↦ affineOf add mul (P i) (Q i)) i₁ i₂ c where
  fst x y := by
    show add (mul (P i₁) x) (mul (Q i₁) y) = x
    rw [hP₁, hQ₁, hM1, hM0, hA0]
  snd x y := by
    show add (mul (P i₂) x) (mul (Q i₂) y) = y
    rw [hP₂, hQ₂, hM0, hM1, hAC, hA0]
  comp i j x y := by
    obtain ⟨h1, h2⟩ := hc i j
    have shuffle : ∀ u v w z, add (add u v) (add w z) = add (add u w) (add v z) := fun u v w z ↦ by
      rw [hAA, hAA, ← hAA v w z, hAC v w, hAA w v z]
    show add (mul (P (c i j)) x) (mul (Q (c i j)) y)
        = add (mul a (add (mul (P i) x) (mul (Q i) y)))
              (mul b (add (mul (P j) x) (mul (Q j) y)))
    rw [hD, hD, ← hMA, ← hMA, ← hMA, ← hMA, shuffle, hD', hD', h1, h2]

/-! ### `GF(16)` -/

/-- The multiplication table of `GF(16) = F₂[t]/(t⁴ + t + 1)`, four bits per entry, an element
being the bit pattern of its coefficient vector. Packing it into one numeral rather than a nested
`Matrix.vecCons` is what keeps a lookup at one machine-natural shift. -/
def gf16Tab : ℕ := 116196760129267793630862849262464326346044543732748708940920453221664288556434379745879494961270582141731748813355742142288220638766218855867759359510984593843506004200114943278699875244065120512813025380665946106619127097398772031257643617143689515450995722003729973585221105779229319991106539050771048038400

/-- Multiplication of `GF(16)`. -/
@[implicit_reducible]
def gf16 (x y : Fin 16) : Fin 16 :=
  ⟨gf16Tab >>> (4 * (16 * x.val + y.val)) % 16, Nat.mod_lt _ (by omega)⟩

/-- Addition of `GF(16)`, which is bitwise. -/
@[implicit_reducible]
def gf16add (x y : Fin 16) : Fin 16 := ⟨(x.val ^^^ y.val) % 16, Nat.mod_lt _ (by omega)⟩

theorem gf16add_assoc : ∀ x y z, gf16add (gf16add x y) z = gf16add x (gf16add y z) := by decide!
theorem gf16add_comm : ∀ x y, gf16add x y = gf16add y x := by decide!
theorem gf16add_zero : ∀ x, gf16add x 0 = x := by decide!
theorem gf16_one : ∀ x, gf16 1 x = x := by decide!
theorem gf16_zero : ∀ x, gf16 0 x = 0 := by decide!
theorem gf16_assoc : ∀ x y z, gf16 (gf16 x y) z = gf16 x (gf16 y z) := by decide!
theorem gf16_distrib : ∀ x y z, gf16 x (gf16add y z) = gf16add (gf16 x y) (gf16 x z) := by decide!
theorem gf16_distrib' : ∀ x y z, gf16add (gf16 x z) (gf16 y z) = gf16 (gf16add x y) z := by decide!

end Magma

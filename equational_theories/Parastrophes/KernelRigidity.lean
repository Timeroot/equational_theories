import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All

/-! Conditional restrictions on countermodels to the remaining arbitrary-carrier
bijectivity questions. None of these lemmas asserts unconditional bijectivity. -/
namespace Parastrophes.KernelRigidity
variable {G : Type*} [Magma G]

/-- Every row identifies exactly the same pairs of inputs. -/
def UniformRowKernels (G : Type*) [Magma G] : Prop :=
  ∀ a b x y : G, a ◇ x = a ◇ y → b ◇ x = b ◇ y

/-- A section which respects equal columns also makes those columns' indices
have equal rows, provided all row kernels agree. -/
theorem equal_rows_of_equal_columns (F : G → G → G)
    (section_law : ∀ x y, x = y ◇ F x y)
    (respects : ∀ x b c, (∀ t, t ◇ b = t ◇ c) → F x b = F x c)
    (hk : UniformRowKernels G) {b c : G} (col : ∀ t, t ◇ b = t ◇ c) :
    ∀ t, b ◇ t = c ◇ t := by
  intro t
  have hb := section_law (b ◇ t) b
  have hc := section_law (b ◇ t) c
  rw [← respects (b ◇ t) b c col] at hc
  exact hc.trans (hk b c _ t hb.symm)

/-- E464 forces injectivity when all row kernels agree. -/
theorem left_injective464 (h : Equation464 G) (hk : UniformRowKernels G) (a : G) :
    Function.Injective (fun x => a ◇ x) := by
  intro b c he
  have col : ∀ t, t ◇ b = t ◇ c := fun t => hk a t b c he
  have row : ∀ t, b ◇ t = c ◇ t :=
    equal_rows_of_equal_columns (fun x y => (x ◇ (x ◇ (x ◇ y)))) h
      (by intros; simp_all only) hk col
  have hb := h b b
  have hc := h c c
  simp only [row, col] at hb
  exact hb.trans hc.symm

/-- E669 forces injectivity when all row kernels agree. -/
theorem left_injective669 (h : Equation669 G) (hk : UniformRowKernels G) (a : G) :
    Function.Injective (fun x => a ◇ x) := by
  intro b c he
  have col : ∀ t, t ◇ b = t ◇ c := fun t => hk a t b c he
  have row : ∀ t, b ◇ t = c ◇ t :=
    equal_rows_of_equal_columns (fun x y => (x ◇ ((x ◇ y) ◇ x))) h
      (by intros; simp_all only) hk col
  have hb := h b b
  have hc := h c c
  simp only [row, col] at hb
  exact hb.trans hc.symm

/-- E879 forces injectivity when all row kernels agree. -/
theorem left_injective879 (h : Equation879 G) (hk : UniformRowKernels G) (a : G) :
    Function.Injective (fun x => a ◇ x) := by
  intro b c he
  have col : ∀ t, t ◇ b = t ◇ c := fun t => hk a t b c he
  have row : ∀ t, b ◇ t = c ◇ t :=
    equal_rows_of_equal_columns (fun x y => ((x ◇ y) ◇ (x ◇ x))) h
      (by intros; simp_all only) hk col
  have hb := h b b
  have hc := h c c
  simp only [row, col] at hb
  exact hb.trans hc.symm

/-- E1075 forces injectivity when all row kernels agree. -/
theorem left_injective1075 (h : Equation1075 G) (hk : UniformRowKernels G) (a : G) :
    Function.Injective (fun x => a ◇ x) := by
  intro b c he
  have col : ∀ t, t ◇ b = t ◇ c := fun t => hk a t b c he
  have row : ∀ t, b ◇ t = c ◇ t :=
    equal_rows_of_equal_columns (fun x y => ((x ◇ (x ◇ y)) ◇ x)) h
      (by intros; simp_all only) hk col
  have hb := h b b
  have hc := h c c
  simp only [row, col] at hb
  exact hb.trans hc.symm

/-- E1278 forces injectivity when all row kernels agree. -/
theorem left_injective1278 (h : Equation1278 G) (hk : UniformRowKernels G) (a : G) :
    Function.Injective (fun x => a ◇ x) := by
  intro b c he
  have col : ∀ t, t ◇ b = t ◇ c := fun t => hk a t b c he
  have row : ∀ t, b ◇ t = c ◇ t :=
    equal_rows_of_equal_columns (fun x y => (((x ◇ x) ◇ y) ◇ x)) h
      (by intros; simp_all only) hk col
  have hb := h b b
  have hc := h c c
  simp only [row, col] at hb
  exact hb.trans hc.symm

/-- E1285 forces injectivity when all row kernels agree. -/
theorem left_injective1285 (h : Equation1285 G) (hk : UniformRowKernels G) (a : G) :
    Function.Injective (fun x => a ◇ x) := by
  intro b c he
  have col : ∀ t, t ◇ b = t ◇ c := fun t => hk a t b c he
  have row : ∀ t, b ◇ t = c ◇ t :=
    equal_rows_of_equal_columns (fun x y => (((x ◇ y) ◇ x) ◇ x)) h
      (by intros; simp_all only) hk col
  have hb := h b b
  have hc := h c c
  simp only [row, col] at hb
  exact hb.trans hc.symm

end Parastrophes.KernelRigidity

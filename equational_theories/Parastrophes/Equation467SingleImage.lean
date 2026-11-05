import equational_theories.Parastrophes.Equation467ImageBasis
import equational_theories.Superposition

/-! A single fourteen-operation identity for E467's finite left-division image. -/
namespace Parastrophes.Eq467Image
open Law FreeMagma

/- The named maps keep this equational calculation small. All steps are checked
by the Lean kernel; the external prover is used only to discover the calculation. -/
set_option maxHeartbeats 2000000 in
private theorem compressed_algebra {G : Type}
    (m d r : G → G → G) (c u v g ci vi gi : G → G)
    (e20 : ∀ X0 : G, (c X0) = (m X0 (m X0 X0)))
    (e21 : ∀ X0 : G, (u X0) = (m X0 (m X0 (c X0))))
    (e22 : ∀ X0 : G, (v X0) = (m X0 (m X0 (u X0))))
    (e23 : ∀ X0 X1 : G, (m X1 (m X1 (m X0 X1))) = (g X0))
    (e24 : ∀ X0 X1 : G, (m X1 (m X1 (m (c X0) (g (v X1))))) = X0)
    (e25 : ∀ X0 X1 : G, (m X0 (d X0 X1)) = X1)
    (e26 : ∀ X0 X1 : G, (d X0 (m X0 X1)) = X1)
    (e27 : ∀ X0 X1 : G, (m (r X0 X1) X1) = X0)
    (e28 : ∀ X0 X1 : G, (r (m X0 X1) X1) = X0)
    (e29 : ∀ X0 : G, (c (ci X0)) = X0)
    (e30 : ∀ X0 : G, (ci (c X0)) = X0)
    (e31 : ∀ X0 : G, (v (vi X0)) = X0)
    (e32 : ∀ X0 : G, (vi (v X0)) = X0)
    (e33 : ∀ X0 : G, (g (gi X0)) = X0)
    (e34 : ∀ X0 : G, (gi (g X0)) = X0)
    : (∀ x, u x = x) ∧ (∀ x, g (c x) = x) := by
  have e36 (X0 X1 : G) : (d (r X0 X1) X0) = X1 := by
    exact superpose e27 e26
  have e37 (X0 X1 : G) : (r X0 (d X1 X0)) = X1 := by
    exact superpose e25 e28
  have e48 (X0 : G) : (m X0 (u X0)) = (d X0 (v X0)) := by
    exact superpose e22 e26
  have e57 (X0 X1 : G) : (g (r X0 X1)) = (m X1 (m X1 X0)) := by
    exact superpose e27 e23
  have e58 (X0 : G) : (m X0 (c X0)) = (g X0) := by
    exact superpose e20 e23
  have e60 (X0 X1 : G) : (m X1 (m X0 X1)) = (d X1 (g X0)) := by
    exact superpose e23 e26
  have e68 (X0 : G) : (m (ci X0) X0) = (g (ci X0)) := by
    exact superpose e29 e58
  have e69 (X0 : G) : (u X0) = (m X0 (g X0)) := by
    exact superpose e58 e21
  have e72 (X0 : G) : (c X0) = (d X0 (g X0)) := by
    exact superpose e58 e26
  have e75 (X0 X1 : G) : (m (vi X0) (m (vi X0) (m (c X1) (g X0)))) = X1 := by
    exact superpose e31 e24
  have e78 (X0 X1 : G) : (m X1 (m (c X0) (g (v X1)))) = (d X1 X0) := by
    exact superpose e24 e26
  have e81 (X0 X1 : G) : (g (r (m (c X1) (g X0)) (vi X0))) = X1 := by
    exact superpose e57 e75
  have e84 (X0 : G) : (u (gi X0)) = (m (gi X0) X0) := by
    exact superpose e33 e69
  have e101 (X0 : G) : (c (gi X0)) = (d (gi X0) X0) := by
    exact superpose e33 e72
  have e116 (X0 : G) : (m (vi X0) (u (vi X0))) = (d (vi X0) X0) := by
    exact superpose e31 e48
  have e135 (X0 : G) : (g (r X0 (ci X0))) = (m (ci X0) (g (ci X0))) := by
    exact superpose e68 e57
  have e141 (X0 : G) : (c X0) = (g (r X0 X0)) := by
    exact superpose e57 e20
  have e145 (X0 : G) : (v X0) = (g (r (u X0) X0)) := by
    exact superpose e57 e22
  have e154 (X0 : G) : (u (ci X0)) = (g (r X0 (ci X0))) := by
    exact superpose e69 e135
  have e165 (X0 : G) : (r X0 X0) = (gi (c X0)) := by
    exact superpose e141 e34
  have e166 (X0 : G) : (m (c X0) (g X0)) = (d (c X0) (g X0)) := by
    exact superpose e58 e60
  have e175 (X0 X1 : G) : (m (d X1 X0) X0) = (d (d X1 X0) (g X1)) := by
    exact superpose e25 e60
  have e195 (X0 : G) : (d (gi (c X0)) X0) = X0 := by
    exact superpose e165 e36
  have e196 (X0 : G) : (m (gi (c X0)) X0) = X0 := by
    exact superpose e165 e27
  have e214 (X0 : G) : (ci X0) = (d (gi X0) (ci X0)) := by
    exact superpose e29 e195
  have e218 (X0 X1 : G) : (ci X0) = (g (r (m X0 (g X1)) (vi X1))) := by
    exact superpose e29 e81
  have e228 (X0 X1 : G) : (gi X0) = (r (m (c X0) (g X1)) (vi X1)) := by
    exact superpose e81 e34
  have e235 (X0 : G) : (ci X0) = (m (gi X0) (ci X0)) := by
    exact superpose e29 e196
  have e238 (X0 : G) : (m (gi (c X0)) X0) = (g (r X0 (gi (c X0)))) := by
    exact superpose e196 e57
  have e243 (X0 : G) : (g (r X0 (gi (c X0)))) = X0 := by
    exact superpose e196 e238
  have e282 (X0 X1 : G) : (m (c X1) (g (v X0))) = (d X0 (d X0 X1)) := by
    exact superpose e78 e26
  have e293 (X0 : G) : (r (u X0) X0) = (gi (v X0)) := by
    exact superpose e145 e34
  have e318 (X0 : G) : (d X0 (g (gi X0))) = (m X0 (u (gi X0))) := by
    exact superpose e84 e60
  have e327 (X0 : G) : (m X0 (u (gi X0))) = (d X0 X0) := by
    exact superpose e33 e318
  have e502 (X0 : G) : (u X0) = (m (gi (v X0)) X0) := by
    exact superpose e293 e27
  have e633 (X0 : G) : (u (vi X0)) = (d (vi X0) (d (vi X0) X0)) := by
    exact superpose e116 e26
  have e641 (X0 : G) : (u (vi X0)) = (m (c X0) (g (v (vi X0)))) := by
    exact superpose e282 e633
  have e647 (X0 : G) : (m (c X0) (g X0)) = (u (vi X0)) := by
    exact superpose e31 e641
  have e696 (X0 : G) : (ci X0) = (g (r (u X0) (vi X0))) := by
    exact superpose e69 e218
  have e831 (X0 : G) : (gi X0) = (r X0 (gi (c X0))) := by
    exact superpose e243 e34
  have e834 (X0 : G) : (c (r X0 (gi (c X0)))) = (d (r X0 (gi (c X0))) X0) := by
    exact superpose e243 e72
  have e844 (X0 : G) : (gi (c X0)) = (c (r X0 (gi (c X0)))) := by
    exact superpose e36 e834
  have e848 (X0 : G) : (c (gi X0)) = (gi (c X0)) := by
    exact superpose e831 e844
  have e871 (X0 : G) : (m (c (gi X0)) X0) = X0 := by
    exact superpose e848 e196
  have e1118 (X0 : G) : (m (c (gi X0)) X0) = (d (c (gi X0)) (g (gi X0))) := by
    exact superpose e101 e175
  have e1171 (X0 : G) : (m (c (gi X0)) X0) = (m (c (gi X0)) (g (gi X0))) := by
    exact superpose e166 e1118
  have e1177 (X0 : G) : (m (c (gi X0)) X0) = (u (vi (gi X0))) := by
    exact superpose e647 e1171
  have e1179 (X0 : G) : (u (vi (gi X0))) = X0 := by
    exact superpose e871 e1177
  have e1181 (X0 : G) : (g X0) = (u (vi X0)) := by
    exact superpose e34 e1179
  have e1253 (X0 : G) : (u X0) = (g (v X0)) := by
    exact superpose e32 e1181
  have e1352 (X0 : G) : (v X0) = (gi (u X0)) := by
    exact superpose e1253 e34
  have e1394 (X0 : G) : (d (gi X0) (ci X0)) = (m (c (ci X0)) (g (v (gi X0)))) := by
    exact superpose e214 e282
  have e1440 (X0 : G) : (d (gi X0) (ci X0)) = (m (c (ci X0)) (u (gi X0))) := by
    exact superpose e1253 e1394
  have e1478 (X0 : G) : (d (gi X0) (ci X0)) = (m X0 (u (gi X0))) := by
    exact superpose e29 e1440
  have e1498 (X0 : G) : (d (gi X0) (ci X0)) = (d X0 X0) := by
    exact superpose e327 e1478
  have e1510 (X0 : G) : (ci X0) = (d X0 X0) := by
    exact superpose e214 e1498
  have e1520 (X0 : G) : (r X0 (ci X0)) = X0 := by
    exact superpose e1510 e37
  have e2762 (X0 : G) : (g X0) = (u (ci X0)) := by
    exact superpose e1520 e154
  have e2841 (X0 : G) : (gi (g X0)) = (v (ci X0)) := by
    exact superpose e2762 e1352
  have e2843 (X0 : G) : (v (ci X0)) = X0 := by
    exact superpose e34 e2841
  have e3013 (X0 : G) : (c X0) = (v X0) := by
    exact superpose e30 e2843
  have e3017 (X0 : G) : (ci X0) = (vi X0) := by
    exact superpose e2843 e32
  have e3028 (X0 : G) : (u (ci X0)) = (m (gi X0) (ci X0)) := by
    exact superpose e2843 e502
  have e3033 (X0 : G) : (ci X0) = (u (ci X0)) := by
    exact superpose e235 e3028
  have e3042 (X0 : G) : (g X0) = (ci X0) := by
    exact superpose e2762 e3033
  have e3072 (X0 X1 : G) : (gi X1) = (r (m (c X1) (ci X0)) (vi (r (u X0) (vi X0)))) := by
    exact superpose e696 e228
  have e3079 (X0 X1 : G) : (gi X1) = (r (m (c X1) (ci X0)) (ci (r (u X0) (vi X0)))) := by
    exact superpose e3017 e3072
  have e3105 (X0 X1 : G) : (gi X1) = (r (m (c X1) (ci X0)) (g (r (u X0) (vi X0)))) := by
    exact superpose e3042 e3079
  have e3130 (X0 X1 : G) : (gi X1) = (r (m (c X1) (ci X0)) (ci X0)) := by
    exact superpose e696 e3105
  have e3150 (X1 : G) : (c X1) = (gi X1) := by
    exact superpose e28 e3130
  have e3185 (X0 : G) : (m (c (c X0)) X0) = X0 := by
    exact superpose e3150 e196
  have e3192 (X0 : G) : (u X0) = (m (c (v X0)) X0) := by
    exact superpose e3150 e502
  have e3198 (X0 : G) : (u X0) = (m (c (c X0)) X0) := by
    exact superpose e3013 e3192
  have e3208 (X0 : G) : (u X0) = X0 := by
    exact superpose e3185 e3198
  exact ⟨e3208, fun x => (e3042 (c x)).trans (e30 x)⟩


/-- Six applications of the row indexed by x, starting at x. -/
def sixth {G : Type} (M : Magma G) (x : G) := M.op x (M.op x (fourth M x))

private def rowSquare {G : Type} (M : Magma G) (y x : G) := M.op y (M.op y x)
private def crossThree {G : Type} (M : Magma G) (x z : G) :=
  M.op z (M.op z (M.op x z))

/-- The inner bridge in the successful compression. -/
def compressionBridge {G : Type} (M : Magma G) (y z : G) :=
  crossThree M (sixth M y) z

/-- Unlike `Joined`, this fourteen-operation identity has a proved converse. -/
def Compressed {G : Type} (M : Magma G) : Prop :=
  ∀ x y z, M.op y (M.op y (M.op (cube M x) (compressionBridge M y z))) = x

private theorem compressed_initial {G : Type} [Finite G] (M : Magma G)
    (h : Compressed M) : Function.Bijective (cube M) ∧
      ∀ y, Function.Bijective (M.op y) := by
  have ci : Function.Injective (cube M) := by
    intro a b he
    have ha := h a a a
    have hb := h b a a
    rw [he] at ha
    exact ha.symm.trans hb
  refine ⟨⟨ci, Finite.surjective_of_injective ci⟩, ?_⟩
  intro y
  have hs : Function.Surjective (M.op y) :=
    fun x => ⟨M.op y (M.op (cube M x) (compressionBridge M y y)), h x y y⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

private theorem compressed_bridge_independent {G : Type} [Finite G] (M : Magma G)
    (h : Compressed M) (y z w : G) : compressionBridge M y z = compressionBridge M y w := by
  have hl := (compressed_initial M h).2
  apply (hl (cube M y)).1
  apply (hl y).1
  apply (hl y).1
  exact (h y y z).trans (h y y w).symm

/-- Equal sixth iterates give equal bridges, hence equal squared row maps.
Applying that common permutation three times recovers the original indices. -/
private theorem compressed_sixth_bijective {G : Type} [Finite G] (M : Magma G)
    (h : Compressed M) : Function.Bijective (sixth M) := by
  have hl := (compressed_initial M h).2
  have hi : Function.Injective (sixth M) := by
    intro a b he
    have hb : compressionBridge M a a = compressionBridge M b a := by
      unfold compressionBridge
      rw [he]
    let s (x : G) := M.op (cube M x) (compressionBridge M a a)
    have hsa (x : G) : rowSquare M a (s x) = x := h x a a
    have hsb (x : G) : rowSquare M b (s x) = x := by
      simpa only [s, hb] using h x b a
    have hs : Function.Surjective s :=
      Finite.surjective_of_injective (Function.LeftInverse.injective hsa)
    have ht (x : G) : rowSquare M a x = rowSquare M b x := by
      obtain ⟨t, rfl⟩ := hs x
      exact (hsa t).trans (hsb t).symm
    change rowSquare M a (rowSquare M a (rowSquare M a a)) =
      rowSquare M b (rowSquare M b (rowSquare M b b)) at he
    simp only [ht] at he
    have hj : Function.Injective (rowSquare M b) := (hl b).1.comp (hl b).1
    exact hj (hj (hj he))
  exact ⟨hi, Finite.surjective_of_injective hi⟩

private theorem basis_of_compressed_fin {G : Type} [Finite G] (M : Magma G)
    (h : Compressed M) : Basis M := by
  classical
  cases isEmpty_or_nonempty G with
  | inl hG =>
    letI := hG
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  | inr hG =>
    letI := hG
    let z₀ : G := Classical.choice hG
    obtain ⟨hc, hl⟩ := compressed_initial M h
    have hv := compressed_sixth_bijective M h
    let g (x : G) := crossThree M x z₀
    have hg (x z : G) : crossThree M x z = g x := by
      obtain ⟨y, rfl⟩ := hv.2 x
      exact compressed_bridge_independent M h y z z₀
    let k := compressionBridge M z₀ z₀
    have hk : Function.Bijective (fun x => M.op x k) := by
      have hi : Function.Injective (fun x => M.op x k) := by
        intro a b he
        obtain ⟨a, rfl⟩ := hc.2 a
        obtain ⟨b, rfl⟩ := hc.2 b
        apply congrArg (cube M)
        exact (h a z₀ z₀).symm.trans ((congrArg (rowSquare M z₀) he).trans (h b z₀ z₀))
      exact ⟨hi, Finite.surjective_of_injective hi⟩
    have hgb : Function.Bijective g := by
      have he : g = fun x => rowSquare M k (M.op x k) :=
        funext fun x => (hg x k).symm
      rw [he]
      exact (hl k).comp ((hl k).comp hk)
    have hr (y : G) : Function.Bijective (fun x => M.op x y) := by
      have hi : Function.Injective (fun x => M.op x y) := by
        intro a b he
        apply hgb.1
        rw [← hg a y, ← hg b y]
        exact congrArg (rowSquare M y) he
      exact ⟨hi, Finite.surjective_of_injective hi⟩
    let le (x : G) := Equiv.ofBijective (M.op x) (hl x)
    let re (y : G) := Equiv.ofBijective (fun x => M.op x y) (hr y)
    let ce := Equiv.ofBijective (cube M) hc
    let ve := Equiv.ofBijective (sixth M) hv
    let ge := Equiv.ofBijective g hgb
    have hs (x y : G) : M.op y (M.op y (M.op (cube M x) (g (sixth M y)))) = x := by
      simpa only [compressionBridge, hg] using h x y z₀
    have ha := compressed_algebra M.op (fun x y => (le x).symm y)
      (fun x y => (re y).symm x) (cube M) (fourth M) (sixth M) g ce.symm ve.symm ge.symm
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hg hs
      (fun x y => (le x).apply_symm_apply y) (fun x y => (le x).symm_apply_apply y)
      (fun x y => (re y).apply_symm_apply x) (fun x y => (re y).symm_apply_apply x)
      ce.apply_symm_apply ce.symm_apply_apply ve.apply_symm_apply ve.symm_apply_apply
      ge.apply_symm_apply ge.symm_apply_apply
    exact ⟨ha.1, fun x y => (hg (cube M x) y).trans (ha.2 x)⟩

private theorem compressed_of_basis {G : Type} (M : Magma G) (h : Basis M) :
    Compressed M := by
  have hv (y : G) : sixth M y = cube M y := by
    change M.op y (M.op y (fourth M y)) = cube M y
    rw [show fourth M y = y from h.1 y]
    rfl
  have hb (y z : G) : compressionBridge M y z = y := by
    unfold compressionBridge
    rw [hv]
    exact h.2 y z
  intro x y z
  rw [hb]
  exact h.2 x y

/-- The finite image of E467 is characterized by one equation, with fourteen
multiplications and three variables. -/
def compressedLaw : NatMagmaLaw :=
  let x := Lf 0
  let y := Lf 1
  let z := Lf 2
  let c := x ⋆ (x ⋆ x)
  let v := y ⋆ (y ⋆ (y ⋆ (y ⋆ (y ⋆ (y ⋆ y)))))
  ⟨x, y ⋆ (y ⋆ (c ⋆ (z ⋆ (z ⋆ (v ⋆ z)))))⟩

private theorem compressedLaw_iff {G : Type} (M : Magma G) :
    @satisfies _ G M compressedLaw ↔ Compressed M := by
  constructor
  · intro h x y z
    exact (h (fun n => if n = 0 then x else if n = 1 then y else z)).symm
  · intro h v
    exact (h (v 0) (v 1) (v 2)).symm

/-- A single identity replaces the previous E411 + E7681 basis for E467's
finite left-division image. The inverse multiplication remains
`M(x,y) = D(x,D(y*(y*y),x))`. -/
@[parastrophe_result] theorem left_characterizes467_fin_single :
    Characterizes .fin Law467 .left compressedLaw := by
  intro G M hG
  letI : Finite G := hG
  rw [compressedLaw_iff]
  exact ⟨fun h => (characterizes_fin M).mp (basis_of_compressed_fin M h),
    fun h => compressed_of_basis M ((characterizes_fin M).mpr h)⟩

end Parastrophes.Eq467Image

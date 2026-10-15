import equational_theories.Parastrophes.Attributes
import equational_theories.Definability.Tarski543
import equational_theories.Spectrum.SmallPairs.Basic

/-! Initial audited records. Additional results can be registered in any imported
module; the export reads attributes, not this file or a hard-coded equation list. -/
namespace Parastrophes.Catalogue
open Law FreeMagma

/-- E2 forces a subsingleton carrier, whose translations are bijections. -/
@[parastrophe_result] theorem quasigroup2 : QuasigroupLaw .all Law2 := by
  intro G M _ h
  have h2 := (@Law2.models_iff G M).mp h
  constructor <;> intro x <;> constructor
  all_goals first | exact fun _ _ _ => h2 _ _ | exact fun y => ⟨y, h2 _ _⟩

/-- The two-element constant magma satisfies E1 and is not a quasigroup. -/
@[parastrophe_result] theorem not_quasigroup1 : ¬ QuasigroupLaw .fin Law1 := by
  intro h
  let M : Magma Bool := ⟨fun _ _ => false⟩
  have hQ := h Bool M (inferInstance : Finite Bool) ((@Law1.models_iff Bool M).mpr (fun _ => rfl))
  have bad := (hQ.1 false).1 (a₁ := false) (a₂ := true) rfl
  contradiction

/-- The two-element left-zero magma is idempotent but is not a quasigroup. -/
@[parastrophe_result] theorem not_quasigroup3 : ¬ QuasigroupLaw .fin Law3 := by
  intro h
  let M : Magma Bool := ⟨fun x _ => x⟩
  have hQ := h Bool M (inferInstance : Finite Bool) ((@Law3.models_iff Bool M).mpr (fun _ => rfl))
  have bad := (hQ.1 false).1 (a₁ := false) (a₂ := true) rfl
  contradiction

/-- Left projection on two elements satisfies E4 but has constant rows. -/
@[parastrophe_result] theorem not_quasigroup4 : ¬ QuasigroupLaw .fin Law4 := by
  intro h
  let M : Magma Bool := ⟨fun x _ => x⟩
  have hQ := h Bool M (inferInstance : Finite Bool) ((@Law4.models_iff Bool M).mpr (fun _ _ => rfl))
  have bad := (hQ.1 false).1 (a₁ := false) (a₂ := true) rfl
  contradiction

/-- A two-element constant magma satisfies E46 and is not a quasigroup. -/
@[parastrophe_result] theorem not_quasigroup46 : ¬ QuasigroupLaw .fin Law46 := by
  intro h
  let M : Magma Bool := ⟨fun _ _ => false⟩
  have hQ := h Bool M (inferInstance : Finite Bool)
    ((@Law46.models_iff Bool M).mpr (fun _ _ _ _ => rfl))
  have bad := (hQ.1 false).1 (a₁ := false) (a₂ := true) rfl
  contradiction

/-- The standard four-element central groupoid satisfies E168 but is not Latin. -/
@[parastrophe_result] theorem not_quasigroup168 : ¬ QuasigroupLaw .fin Law168 := by
  intro h
  let M : Magma (Bool × Bool) := ⟨fun x y => (x.2, y.1)⟩
  have hm : @satisfies _ (Bool × Bool) M Law168 :=
    (@Law168.models_iff _ M).mpr (fun x _ _ => (Prod.eta x).symm)
  have hQ := h (Bool × Bool) M (inferInstance : Finite (Bool × Bool)) hm
  have bad := (hQ.1 (false,false)).1 (a₁ := (false,false)) (a₂ := (false,true)) rfl
  have := congrArg Prod.snd bad
  contradiction

private theorem characterizes2 (side : Side) : Characterizes .all Law2 side Law2 := by
  intro G D _
  constructor
  · intro h
    have h2 := (@Law2.models_iff G D).mp h
    refine ⟨D, h, quasigroup2 G D trivial h, ?_⟩
    cases side <;> exact ⟨fun _ _ => h2 _ _, fun _ _ => h2 _ _⟩
  · rintro ⟨M, hM, _, _⟩
    exact (@Law2.models_iff G D).mpr ((@Law2.models_iff G M).mp hM)

/-- The division image of the subsingleton law is the same subsingleton law. -/
@[parastrophe_result] theorem left_characterizes2 : Characterizes .all Law2 .left Law2 :=
  characterizes2 .left

/-- The division image of the subsingleton law is the same subsingleton law. -/
@[parastrophe_result] theorem right_characterizes2 : Characterizes .all Law2 .right Law2 :=
  characterizes2 .right

private theorem cyclic14 {G : Type} (M : Magma G) (h : @Equation14 G M) (x y : G) :
    M.op (M.op x y) x = y := by
  have hh := h y (M.op x y)
  rw [← h x y] at hh
  exact hh.symm

private theorem divisions14 {G : Type} (M : Magma G) (h : @Equation14 G M) :
    IsDivision .left M (opposite M) ∧ IsDivision .right M (opposite M) := by
  exact ⟨⟨fun x y => (h y x).symm, cyclic14 M h⟩,
    ⟨fun x y => cyclic14 M h y x, fun x y => (h x y).symm⟩⟩

/-- E14 is semisymmetric: both divisions are the opposite multiplication. -/
@[parastrophe_result] theorem quasigroup14 : QuasigroupLaw .all Law14 := by
  intro G M _ h
  have hd := divisions14 M ((@Law14.models_iff G M).mp h)
  exact quasigroup_of_divisions hd.1 hd.2

/-- In every E14 model, x left-divide y = y ◇ x. -/
@[parastrophe_result] theorem left_term14 :
    UniformTermWitness .all Law14 .left (Lf 1 ⋆ Lf 0) := by
  intro G M _ h
  exact (divisions14 M ((@Law14.models_iff G M).mp h)).1

/-- In every E14 model, x right-divide y = y ◇ x. -/
@[parastrophe_result] theorem right_term14 :
    UniformTermWitness .all Law14 .right (Lf 1 ⋆ Lf 0) := by
  intro G M _ h
  exact (divisions14 M ((@Law14.models_iff G M).mp h)).2

private theorem characterizes14 (side : Side) : Characterizes .all Law14 side Law29 := by
  intro G D _
  constructor
  · intro h
    have hm : @satisfies _ G (opposite D) Law14 := by
      apply (@Law14.models_iff G (opposite D)).mpr
      exact (@Law29.models_iff G D).mp h
    refine ⟨opposite D, hm, quasigroup14 G (opposite D) trivial hm, ?_⟩
    have hd := divisions14 (opposite D) ((@Law14.models_iff G (opposite D)).mp hm)
    cases side <;> first | exact hd.1 | exact hd.2
  · rintro ⟨M, hm, _, hd⟩
    have h14 := (@Law14.models_iff G M).mp hm
    have hp := divisions14 M h14
    have he : D = opposite M := division_unique hd (by cases side <;> first | exact hp.1 | exact hp.2)
    subst D
    exact (@Law29.models_iff G (opposite M)).mpr h14

/-- The left-division image of E14 is exactly E29, including the converse. -/
@[parastrophe_result] theorem left_characterizes14 : Characterizes .all Law14 .left Law29 :=
  characterizes14 .left

/-- The right-division image of E14 is exactly E29, including the converse. -/
@[parastrophe_result] theorem right_characterizes14 : Characterizes .all Law14 .right Law29 :=
  characterizes14 .right

/-- E543 is abelian-group subtraction. Left division is subtraction itself. -/
@[parastrophe_result] theorem left_term543 :
    UniformTermWitness .all Law543 .left (Lf 0 ⋆ Lf 1) := by
  intro G M _ h
  have h16 := @Equation543_implies_Equation16 G M ((@Law543.models_iff G M).mp h)
  exact ⟨fun x y => (h16 y x).symm, fun x y => (h16 y x).symm⟩

/-- The addition operation recovered from E543 is its right division. -/
@[parastrophe_result] theorem right_term543 :
    UniformTermWitness .all Law543 .right (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 1)) := by
  intro G M _ h
  have h543 := (@Law543.models_iff G M).mp h
  have h16 := @Equation543_implies_Equation16 G M h543
  have h40 := @Equation543_implies_Equation40 G M h543
  have h4369 := @Equation543_implies_Equation4369 G M h543
  have h3823 := @Equation543_implies_Equation3823 G M h543
  constructor
  · intro x y
    change M.op (M.op x (M.op (M.op x x) y)) y = x
    rw [h4369 x (M.op x x) y, h3823 (M.op y (M.op (M.op x x) x)) y x,
      ← h16 (M.op (M.op x x) x) y, ← h16 x (M.op x x)]
  · intro x y
    change M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) y) = x
    rw [h40 (M.op x y) x, h4369 (M.op x y) (M.op x x) y, ← h3823 y x x, ← h16 x y]

/-- Both translations of an E543 magma have the explicit inverses recorded above. -/
@[parastrophe_result] theorem quasigroup543 : QuasigroupLaw .all Law543 := by
  intro G M _ h
  exact quasigroup_of_divisions (left_term543 G M trivial h) (right_term543 G M trivial h)

/-- The left parastrophe of E543 is exactly E543 again. -/
@[parastrophe_result] theorem left_characterizes543 : Characterizes .all Law543 .left Law543 := by
  intro G D _
  constructor
  · intro h
    exact ⟨D, h, quasigroup543 G D trivial h, left_term543 G D trivial h⟩
  · rintro ⟨M, hm, _, hd⟩
    have he : D = M := division_unique hd (left_term543 G M trivial hm)
    exact he.symm ▸ hm

/-- The existing finite Latin-square reduction proves E704 is a quasigroup. -/
@[parastrophe_result] theorem quasigroup704_fin : QuasigroupLaw .fin Law704 := by
  intro G M hG h
  letI : Finite G := hG
  have hh := (Spectrum.SmallPairs.holds_iff .e704 M).mpr h
  exact ⟨Spectrum.SmallPairs.left_bijective hh,
    Spectrum.SmallPairs.right_bijective hh (Or.inl rfl)⟩

/-- The existing finite Latin-square reduction proves E1279 is a quasigroup. -/
@[parastrophe_result] theorem quasigroup1279_fin : QuasigroupLaw .fin Law1279 := by
  intro G M hG h
  letI : Finite G := hG
  have hh := (Spectrum.SmallPairs.holds_iff .e1279 M).mpr h
  exact ⟨Spectrum.SmallPairs.left_bijective hh,
    Spectrum.SmallPairs.right_bijective hh (Or.inr rfl)⟩

/-- The existing finite Latin-square reduction proves E1313 is a quasigroup. -/
@[parastrophe_result] theorem quasigroup1313_fin : QuasigroupLaw .fin Law1313 := by
  intro G M hG h
  letI : Finite G := hG
  have hh := (Spectrum.SmallPairs.holds_iff .e1313 M).mpr h
  exact ⟨Spectrum.SmallPairs.left_bijective hh, Spectrum.SmallPairs.right_bijective1313 hh⟩

/-- No identity characterizes the right-division image of E543 on arbitrary carriers.
The image contains integer addition. Every identity of integer addition also holds
in its natural-number submagma, whose left translation by 1 is not surjective.
This excludes every identity, not merely the equations in the catalogue. -/
@[parastrophe_result] theorem right_noSingleEquation543 :
    ¬ SingleEquation .all Law543 .right := by
  rintro ⟨target, ht⟩
  let Zsub : Magma Int := ⟨fun x y => x - y⟩
  let Zadd : Magma Int := ⟨fun x y => x + y⟩
  have hs : @satisfies _ Int Zsub Law543 := by
    apply (@Law543.models_iff Int Zsub).mpr
    intro x y z
    change x = y - (z - (x - (y - z)))
    omega
  have hz : @satisfies _ Int Zadd target := (ht Int Zadd trivial).mpr
    ⟨Zsub, hs, quasigroup543 Int Zsub trivial hs, by
      constructor
      · intro x y; change x + y - y = x; omega
      · intro x y; change x - y + y = x; omega⟩
  let Nadd : Magma Nat := ⟨fun x y => x + y⟩
  have cast_eval (t : FreeMagma Nat) (v : Nat → Nat) :
      ((@evalInMagma _ _ Nadd v t : Nat) : Int) =
      @evalInMagma _ _ Zadd (fun i => (v i : Int)) t := by
    induction t with
    | Leaf => rfl
    | Fork a b ha hb => simpa only [evalInMagma, Nadd, Zadd, Int.natCast_add] using congrArg₂ (· + ·) ha hb
  have hn : @satisfies _ Nat Nadd target := by
    intro v
    apply Int.ofNat_inj.mp
    change ((@evalInMagma _ _ Nadd v target.lhs : Nat) : Int) =
      ((@evalInMagma _ _ Nadd v target.rhs : Nat) : Int)
    rw [cast_eval, cast_eval]
    exact hz (fun i => (v i : Int))
  have hQ := characterizes_quasigroup ht Nat Nadd trivial hn
  obtain ⟨x, hx⟩ := (hQ.1 1).2 0
  change 1 + x = 0 at hx
  omega

end Parastrophes.Catalogue

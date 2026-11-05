import equational_theories.Parastrophes.Basic

/-!
# Finite division images are closed under submagmas and quotients

These closure properties hold for every source identity, whether or not its
finite division image has an equational characterization. In particular, a
finite submagma cannot replace the infinite submagmas used in the recent image
obstructions. A finite quotient cannot furnish such an obstruction either.

Only the smaller carrier needs to be finite. The containing or covering
division algebra can be infinite.
-/
namespace Parastrophes.FiniteImageClosure
open Law FreeMagma

private theorem eval_map {G H : Type} (M : Magma G) (N : Magma H) (f : G → H)
    (hf : ∀ x y, f (M.op x y) = N.op (f x) (f y))
    (t : FreeMagma Nat) (v : Nat → G) :
    f (@evalInMagma _ _ M v t) = @evalInMagma _ _ N (f ∘ v) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb => exact (hf _ _).trans (congrArg₂ N.op ha hb)

private theorem division_exists {G : Type} (side : Side) (D : Magma G)
    (hQ : IsSideQuasigroup side D) : ∃ M, IsDivision side M D := by
  classical
  cases side with
  | left =>
    let M : Magma G := ⟨fun x y => Classical.choose ((hQ x).2 y)⟩
    have he (x y : G) : D.op x (M.op x y) = y := Classical.choose_spec ((hQ x).2 y)
    exact ⟨M, fun x y => (hQ x).1 (he x (D.op x y)), he⟩
  | right =>
    let M : Magma G := ⟨fun x y => Classical.choose ((hQ y).2 x)⟩
    have he (x y : G) : D.op (M.op x y) y = x := Classical.choose_spec ((hQ y).2 x)
    exact ⟨M, fun x y => (hQ y).1 (he (D.op x y) y), he⟩

/-- A homomorphism between actual divisions also preserves the original
multiplications. This part needs no finiteness assumption. -/
theorem map_inverse {G H : Type} {side : Side}
    (M D : Magma G) (N E : Magma H) (f : G → H)
    (hd : IsDivision side M D) (he : IsDivision side N E)
    (hf : ∀ x y, f (D.op x y) = E.op (f x) (f y)) :
    ∀ x y, f (M.op x y) = N.op (f x) (f y) := by
  have hQ := sideQuasigroup_of_division (division_symm he)
  cases side with
  | left =>
    intro x y
    apply (hQ (f x)).1
    rw [← hf, hd.2, he.2]
  | right =>
    intro x y
    apply (hQ (f y)).1
    change E.op (f (M.op x y)) (f y) = E.op (N.op (f x) (f y)) (f y)
    rw [← hf, hd.2, he.2]

/-- A finite submagma inherits bijectivity on either bijective side. -/
theorem sideQuasigroup_of_embedding {G H : Type} [Finite G] {side : Side}
    (D : Magma G) (E : Magma H) (f : G → H) (hi : Function.Injective f)
    (hf : ∀ x y, f (D.op x y) = E.op (f x) (f y))
    (hQ : IsSideQuasigroup side E) : IsSideQuasigroup side D := by
  cases side with
  | left =>
    intro x
    have h : Function.Injective (D.op x) := by
      intro a b hab
      apply hi
      apply (hQ (f x)).1
      exact (hf x a).symm.trans ((congrArg f hab).trans (hf x b))
    exact ⟨h, Finite.surjective_of_injective h⟩
  | right =>
    intro y
    have h : Function.Injective (fun x => D.op x y) := by
      intro a b hab
      apply hi
      apply (hQ (f y)).1
      exact (hf a y).symm.trans ((congrArg f hab).trans (hf b y))
    exact ⟨h, Finite.surjective_of_injective h⟩

/-- A finite homomorphic image inherits bijectivity on either bijective side. -/
theorem sideQuasigroup_of_surjection {G H : Type} [Finite H] {side : Side}
    (D : Magma G) (E : Magma H) (f : G → H) (hs : Function.Surjective f)
    (hf : ∀ x y, f (D.op x y) = E.op (f x) (f y))
    (hQ : IsSideQuasigroup side D) : IsSideQuasigroup side E := by
  cases side with
  | left =>
    intro x
    obtain ⟨a, rfl⟩ := hs x
    have h : Function.Surjective (E.op (f a)) := by
      intro y
      obtain ⟨b, rfl⟩ := hs y
      obtain ⟨c, hc⟩ := (hQ a).2 b
      exact ⟨f c, (hf a c).symm.trans (congrArg f hc)⟩
    exact ⟨Finite.injective_iff_surjective.mpr h, h⟩
  | right =>
    intro y
    obtain ⟨b, rfl⟩ := hs y
    have h : Function.Surjective (fun x => E.op x (f b)) := by
      intro x
      obtain ⟨a, rfl⟩ := hs x
      obtain ⟨c, hc⟩ := (hQ b).2 a
      exact ⟨f c, (hf c b).symm.trans (congrArg f hc)⟩
    exact ⟨Finite.injective_iff_surjective.mpr h, h⟩

/-- Every finite submagma of an actual division image is another actual image
of the same source law. The ambient carrier need not be finite. -/
theorem inImage_of_embedding {G H : Type} [Finite G] {side : Side}
    {L : NatMagmaLaw} (D : Magma G) (E : Magma H)
    (f : G → H) (hi : Function.Injective f)
    (hf : ∀ x y, f (D.op x y) = E.op (f x) (f y)) (hE : InImage L side E) :
    InImage L side D := by
  obtain ⟨N, hN, he⟩ := hE
  obtain ⟨M, hd⟩ := division_exists side D
    (sideQuasigroup_of_embedding D E f hi hf
      (sideQuasigroup_of_division (division_symm he)))
  refine ⟨M, ?_, hd⟩
  have hm := map_inverse M D N E f hd he hf
  intro v
  apply hi
  exact (eval_map M N f hm L.lhs v).trans
    ((hN (f ∘ v)).trans (eval_map M N f hm L.rhs v).symm)

/-- Every finite homomorphic image of an actual division image is another
actual image of the same source law. The covering carrier may be infinite. -/
theorem inImage_of_surjection {G H : Type} [Finite H] {side : Side}
    {L : NatMagmaLaw} (D : Magma G) (E : Magma H)
    (f : G → H) (hs : Function.Surjective f)
    (hf : ∀ x y, f (D.op x y) = E.op (f x) (f y)) (hD : InImage L side D) :
    InImage L side E := by
  classical
  obtain ⟨M, hM, hd⟩ := hD
  obtain ⟨N, he⟩ := division_exists side E
    (sideQuasigroup_of_surjection D E f hs hf
      (sideQuasigroup_of_division (division_symm hd)))
  refine ⟨N, ?_, he⟩
  have hm := map_inverse M D N E f hd he hf
  intro v
  let w : Nat → G := fun i => Classical.choose (hs (v i))
  have hw : f ∘ w = v := funext (fun i => Classical.choose_spec (hs (v i)))
  have hh := (eval_map M N f hm L.lhs w).symm.trans
    ((congrArg f (hM w)).trans (eval_map M N f hm L.rhs w))
  simpa only [hw] using hh

end Parastrophes.FiniteImageClosure

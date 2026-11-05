import equational_theories.Parastrophes.TranslationChains
import equational_theories.Superposition

/-! Exact images found by equational search, replayed as short kernel-checked
superposition proofs. Only the source law and the two division identities are
used. No external solver result is trusted. -/
namespace Parastrophes.Catalogue

private theorem transfer692_692 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation692 G M) : @Equation692 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op X0 (M.op (M.op X2 X1) X2))) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op sK0 (D.op (D.op sK2 sK1) sK2))) := mod_symm hn
  have e12 (X0 X1 X2 : G) : (M.op (D.op X1 X0) (M.op X2 (M.op X0 X1))) = X2 := superpose e9 e8
  have e14 (X0 X1 X2 : G) : (M.op X2 (M.op (M.op (M.op X0 X1) X0) X2)) = X1 := superpose e8 e8
  have e15 (X0 X1 X2 : G) : (M.op X0 (M.op (M.op X2 X1) X2)) = (D.op X1 X0) := superpose e8 e10
  have e23 (X0 X1 X2 : G) : (D.op X1 X0) = (M.op X2 (M.op (M.op X0 X1) X2)) := superpose e12 e8
  have e25 (X0 X1 X2 : G) : (M.op X0 (M.op X2 X1)) = (D.op (D.op X1 X2) X0) := superpose e12 e10
  have e37 (X0 X1 X2 : G) : (M.op (D.op X1 (M.op (M.op X2 X0) X2)) X0) = X1 := superpose e14 e12
  have e40 (X0 X1 X2 : G) : (D.op X1 X0) = (M.op (M.op (M.op X2 X0) X2) X1) := superpose e14 e10
  have e71 (X0 X1 X2 : G) : (D.op X0 (D.op X1 X2)) = (M.op (M.op X2 X1) X0) := superpose e15 e12
  have e125 (X0 X1 X2 : G) : (D.op (D.op X1 X0) X1) = (M.op X2 (M.op X0 X2)) := superpose e9 e23
  have e161 (X0 X1 X2 : G) : (M.op X1 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := superpose e25 e125
  have e169 : sK0 ≠ (D.op sK1 (D.op sK0 (M.op sK2 (M.op sK1 sK2)))) := superpose e25 e11
  have e173 : sK0 ≠ (M.op (M.op (M.op sK2 (M.op sK1 sK2)) sK0) sK1) := superpose e71 e169
  have e303 (X0 X1 X2 : G) : (M.op (D.op X2 (D.op (M.op X0 X1) X1)) X0) = X2 := superpose e40 e37
  have e343 (X0 X1 X2 : G) : (M.op (M.op (M.op X1 (M.op X0 X1)) X2) X0) = X2 := superpose e71 e303
  have e1321 (X0 : G) : sK0 ≠ (M.op (M.op (M.op X0 (M.op sK1 X0)) sK0) sK1) := superpose e161 e173
  subsumption e1321 e343

private theorem transfer898_1368 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation898 G M) : @Equation1368 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X0 X2) (M.op X2 X1))) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op (D.op (D.op sK2 sK1) sK0) sK2)) := mod_symm hn
  have e12 (X0 X1 X2 : G) : (M.op X1 (M.op X0 (M.op (D.op X2 X0) X1))) = X2 := superpose e9 e8
  have e14 (X0 X1 X2 : G) : (M.op (D.op X1 X0) (M.op (M.op X2 X1) X0)) = X2 := superpose e9 e8
  have e17 (X0 X1 X2 : G) : (M.op (M.op X0 X2) (M.op X2 X1)) = (D.op X1 X0) := superpose e8 e10
  have e21 (X0 X1 X2 : G) : (M.op (D.op (D.op X1 X2) X0) (M.op X2 X0)) = X1 := superpose e9 e12
  have e44 (X0 X1 X2 : G) : (D.op (D.op X1 X2) X0) = (M.op (M.op X0 X1) X2) := superpose e14 e10
  have e115 (X0 X1 X2 X3 : G) : (D.op X3 (D.op (D.op X0 X1) X2)) = (M.op X0 (M.op (M.op X1 X2) X3)) := superpose e21 e17
  have e118 (X0 X1 X2 X3 : G) : (M.op X0 (M.op (M.op X1 X2) X3)) = (D.op X3 (M.op (M.op X2 X0) X1)) := superpose e44 e115
  have e288 : sK0 ≠ (D.op sK1 (M.op (M.op sK2 (D.op sK2 sK1)) sK0)) := superpose e44 e11
  have e302 : sK0 ≠ (M.op (D.op sK2 sK1) (M.op (M.op sK0 sK2) sK1)) := superpose e118 e288
  subsumption e302 e14

private theorem transfer1368_898 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1368 G M) : @Equation898 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op (M.op X2 X1) X0) X2)) = X0 := mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 := hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 := hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op (D.op sK0 sK2) (D.op sK2 sK1))) := mod_symm hn
  have e12 (X0 X1 X2 : G) : (M.op (D.op X1 X0) (M.op (M.op X0 X2) X1)) = X2 := superpose e9 e8
  have e16 (X0 X1 X2 : G) : (M.op (M.op (M.op X2 X1) X0) X2) = (D.op X1 X0) := superpose e8 e10
  have e20 (X0 X1 X2 : G) : (D.op X2 X0) = (M.op (D.op X1 X2) (M.op X0 X1)) := superpose e9 e12
  have e26 (X0 X1 X2 : G) : (M.op (M.op X2 X0) X1) = (D.op (D.op X1 X2) X0) := superpose e12 e10
  have e72 (X0 X1 X2 X3 : G) : (D.op X2 (M.op (M.op X3 X0) X1)) = (M.op (D.op X3 X2) (D.op X0 X1)) := superpose e16 e20
  have e98 : sK0 ≠ (D.op sK1 (M.op (M.op sK2 (D.op sK2 sK1)) sK0)) := superpose e26 e11
  have e103 : sK0 ≠ (M.op (D.op sK2 sK1) (D.op (D.op sK2 sK1) sK0)) := superpose e72 e98
  subsumption e103 e9

/-- E692 characterizes its own left-division image on arbitrary carriers. -/
@[parastrophe_result] theorem left_characterizes692_all :
    Characterizes .all Law692 .left Law692 := by
  apply characterizes_of_division
  · intro G M _ h
    have he := @Equation692_implies_Equation1358 G M ((@Law692.models_iff G M).mp h)
    have ht := (@Law1316.models_iff G M).mpr (fun x y => he x y y)
    exact sideQuasigroup_of_division (left_term1316 G M trivial ht)
  all_goals
    intro G M D _ hd h
    exact (@Law692.models_iff G D).mpr (transfer692_692 M D hd ((@Law692.models_iff G M).mp h))

/-- E898 and E1368 are exactly left-parastrophic, on finite and infinite carriers. -/
@[parastrophe_result] theorem left_characterizes898_all :
    Characterizes .all Law898 .left Law1368 := by
  apply characterizes_of_division
  · intro G M _ h
    have h1587 := @Equation1368_implies_Equation1587 G M ((@Law1368.models_iff G M).mp h)
    have h2805 := @Equation1587_implies_Equation2805 G M h1587
    have ho : @satisfies _ G (opposite M) Law898 :=
      (@Law898.models_iff G (opposite M)).mpr h2805
    have hr := sideQuasigroup_of_division (right_term898 G (opposite M) trivial ho)
    exact hr
  · intro G M D _ hd h
    exact (@Law1368.models_iff G D).mpr (transfer898_1368 M D hd ((@Law898.models_iff G M).mp h))
  · intro G M D _ hd h
    exact (@Law898.models_iff G D).mpr (transfer1368_898 M D hd ((@Law1368.models_iff G M).mp h))

end Parastrophes.Catalogue

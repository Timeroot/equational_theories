import equational_theories.Definability.PointedIdentityCountsC2
import equational_theories.Definability.PointedIdentityCountsC3
import equational_theories.Definability.PointedIdentityCountsC4

/-! FO-structural negatives on arbitrary carriers, by pointed-block
amplification and compactness. The local groups are counting devices;
these theorems do not assert finite FO-structural counterexamples. -/

open Law Law.MagmaLaw

local instance : Fact (1 < 4) := ⟨by decide⟩

theorem Equation108_not_StructuralFrom_Equation11_pointedIdentityC2 :
    ¬ Law108.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term11)
    (by rw [PointedIdentityCounting.C2.target108]; decide)
    (by rw [PointedIdentityCounting.C2.target108, PointedIdentityCounting.C2.source11]; decide)

/-- info: 'Equation108_not_StructuralFrom_Equation11_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation108_not_StructuralFrom_Equation11_pointedIdentityC2

theorem Equation630_not_StructuralFrom_Equation11_pointedIdentityC2 :
    ¬ Law630.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term11)
    (by rw [PointedIdentityCounting.C2.target630]; decide)
    (by rw [PointedIdentityCounting.C2.target630, PointedIdentityCounting.C2.source11]; decide)

/-- info: 'Equation630_not_StructuralFrom_Equation11_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation630_not_StructuralFrom_Equation11_pointedIdentityC2

theorem Equation643_not_StructuralFrom_Equation11_pointedIdentityC2 :
    ¬ Law643.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term11)
    (by rw [PointedIdentityCounting.C2.target643]; decide)
    (by rw [PointedIdentityCounting.C2.target643, PointedIdentityCounting.C2.source11]; decide)

/-- info: 'Equation643_not_StructuralFrom_Equation11_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation643_not_StructuralFrom_Equation11_pointedIdentityC2

theorem Equation818_not_StructuralFrom_Equation11_pointedIdentityC2 :
    ¬ Law818.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term11)
    (by rw [PointedIdentityCounting.C2.target818]; decide)
    (by rw [PointedIdentityCounting.C2.target818, PointedIdentityCounting.C2.source11]; decide)

/-- info: 'Equation818_not_StructuralFrom_Equation11_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation818_not_StructuralFrom_Equation11_pointedIdentityC2

theorem Equation843_not_StructuralFrom_Equation11_pointedIdentityC2 :
    ¬ Law843.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term11)
    (by rw [PointedIdentityCounting.C2.target843]; decide)
    (by rw [PointedIdentityCounting.C2.target843, PointedIdentityCounting.C2.source11]; decide)

/-- info: 'Equation843_not_StructuralFrom_Equation11_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation843_not_StructuralFrom_Equation11_pointedIdentityC2

theorem Equation1224_not_StructuralFrom_Equation11_pointedIdentityC2 :
    ¬ Law1224.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term11)
    (by rw [PointedIdentityCounting.C2.target1224]; decide)
    (by rw [PointedIdentityCounting.C2.target1224, PointedIdentityCounting.C2.source11]; decide)

/-- info: 'Equation1224_not_StructuralFrom_Equation11_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1224_not_StructuralFrom_Equation11_pointedIdentityC2

theorem Equation1249_not_StructuralFrom_Equation11_pointedIdentityC2 :
    ¬ Law1249.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term11)
    (by rw [PointedIdentityCounting.C2.target1249]; decide)
    (by rw [PointedIdentityCounting.C2.target1249, PointedIdentityCounting.C2.source11]; decide)

/-- info: 'Equation1249_not_StructuralFrom_Equation11_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1249_not_StructuralFrom_Equation11_pointedIdentityC2

theorem Equation1515_not_StructuralFrom_Equation11_pointedIdentityC2 :
    ¬ Law1515.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term11)
    (by rw [PointedIdentityCounting.C2.target1515]; decide)
    (by rw [PointedIdentityCounting.C2.target1515, PointedIdentityCounting.C2.source11]; decide)

/-- info: 'Equation1515_not_StructuralFrom_Equation11_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1515_not_StructuralFrom_Equation11_pointedIdentityC2

theorem Equation3465_not_StructuralFrom_Equation11_pointedIdentityC2 :
    ¬ Law3465.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term11)
    (by rw [PointedIdentityCounting.C2.target3465]; decide)
    (by rw [PointedIdentityCounting.C2.target3465, PointedIdentityCounting.C2.source11]; decide)

/-- info: 'Equation3465_not_StructuralFrom_Equation11_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3465_not_StructuralFrom_Equation11_pointedIdentityC2

theorem Equation3484_not_StructuralFrom_Equation11_pointedIdentityC2 :
    ¬ Law3484.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term11)
    (by rw [PointedIdentityCounting.C2.target3484]; decide)
    (by rw [PointedIdentityCounting.C2.target3484, PointedIdentityCounting.C2.source11]; decide)

/-- info: 'Equation3484_not_StructuralFrom_Equation11_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3484_not_StructuralFrom_Equation11_pointedIdentityC2

theorem Equation643_not_StructuralFrom_Equation108_pointedIdentityC2 :
    ¬ Law643.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term108)
    (by rw [PointedIdentityCounting.C2.target643]; decide)
    (by rw [PointedIdentityCounting.C2.target643, PointedIdentityCounting.C2.source108]; decide)

/-- info: 'Equation643_not_StructuralFrom_Equation108_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation643_not_StructuralFrom_Equation108_pointedIdentityC2

theorem Equation843_not_StructuralFrom_Equation108_pointedIdentityC2 :
    ¬ Law843.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term108)
    (by rw [PointedIdentityCounting.C2.target843]; decide)
    (by rw [PointedIdentityCounting.C2.target843, PointedIdentityCounting.C2.source108]; decide)

/-- info: 'Equation843_not_StructuralFrom_Equation108_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation843_not_StructuralFrom_Equation108_pointedIdentityC2

theorem Equation4381_not_StructuralFrom_Equation108_pointedIdentityC2 :
    ¬ Law4381.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term108)
    (by rw [PointedIdentityCounting.C2.target4381]; decide)
    (by rw [PointedIdentityCounting.C2.target4381, PointedIdentityCounting.C2.source108]; decide)

/-- info: 'Equation4381_not_StructuralFrom_Equation108_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4381_not_StructuralFrom_Equation108_pointedIdentityC2

theorem Equation108_not_StructuralFrom_Equation1252_pointedIdentityC2 :
    ¬ Law108.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term1252)
    (by rw [PointedIdentityCounting.C2.target108]; decide)
    (by rw [PointedIdentityCounting.C2.target108, PointedIdentityCounting.C2.source1252]; decide)

/-- info: 'Equation108_not_StructuralFrom_Equation1252_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation108_not_StructuralFrom_Equation1252_pointedIdentityC2

theorem Equation630_not_StructuralFrom_Equation1252_pointedIdentityC2 :
    ¬ Law630.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term1252)
    (by rw [PointedIdentityCounting.C2.target630]; decide)
    (by rw [PointedIdentityCounting.C2.target630, PointedIdentityCounting.C2.source1252]; decide)

/-- info: 'Equation630_not_StructuralFrom_Equation1252_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation630_not_StructuralFrom_Equation1252_pointedIdentityC2

theorem Equation643_not_StructuralFrom_Equation1252_pointedIdentityC2 :
    ¬ Law643.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term1252)
    (by rw [PointedIdentityCounting.C2.target643]; decide)
    (by rw [PointedIdentityCounting.C2.target643, PointedIdentityCounting.C2.source1252]; decide)

/-- info: 'Equation643_not_StructuralFrom_Equation1252_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation643_not_StructuralFrom_Equation1252_pointedIdentityC2

theorem Equation818_not_StructuralFrom_Equation1252_pointedIdentityC2 :
    ¬ Law818.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term1252)
    (by rw [PointedIdentityCounting.C2.target818]; decide)
    (by rw [PointedIdentityCounting.C2.target818, PointedIdentityCounting.C2.source1252]; decide)

/-- info: 'Equation818_not_StructuralFrom_Equation1252_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation818_not_StructuralFrom_Equation1252_pointedIdentityC2

theorem Equation843_not_StructuralFrom_Equation1252_pointedIdentityC2 :
    ¬ Law843.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term1252)
    (by rw [PointedIdentityCounting.C2.target843]; decide)
    (by rw [PointedIdentityCounting.C2.target843, PointedIdentityCounting.C2.source1252]; decide)

/-- info: 'Equation843_not_StructuralFrom_Equation1252_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation843_not_StructuralFrom_Equation1252_pointedIdentityC2

theorem Equation1224_not_StructuralFrom_Equation1252_pointedIdentityC2 :
    ¬ Law1224.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term1252)
    (by rw [PointedIdentityCounting.C2.target1224]; decide)
    (by rw [PointedIdentityCounting.C2.target1224, PointedIdentityCounting.C2.source1252]; decide)

/-- info: 'Equation1224_not_StructuralFrom_Equation1252_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1224_not_StructuralFrom_Equation1252_pointedIdentityC2

theorem Equation1249_not_StructuralFrom_Equation1252_pointedIdentityC2 :
    ¬ Law1249.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term1252)
    (by rw [PointedIdentityCounting.C2.target1249]; decide)
    (by rw [PointedIdentityCounting.C2.target1249, PointedIdentityCounting.C2.source1252]; decide)

/-- info: 'Equation1249_not_StructuralFrom_Equation1252_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1249_not_StructuralFrom_Equation1252_pointedIdentityC2

theorem Equation1515_not_StructuralFrom_Equation1252_pointedIdentityC2 :
    ¬ Law1515.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term1252)
    (by rw [PointedIdentityCounting.C2.target1515]; decide)
    (by rw [PointedIdentityCounting.C2.target1515, PointedIdentityCounting.C2.source1252]; decide)

/-- info: 'Equation1515_not_StructuralFrom_Equation1252_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1515_not_StructuralFrom_Equation1252_pointedIdentityC2

theorem Equation3484_not_StructuralFrom_Equation1252_pointedIdentityC2 :
    ¬ Law3484.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C2.H) (t := PointedIdentityCounting.C2.term1252)
    (by rw [PointedIdentityCounting.C2.target3484]; decide)
    (by rw [PointedIdentityCounting.C2.target3484, PointedIdentityCounting.C2.source1252]; decide)

/-- info: 'Equation3484_not_StructuralFrom_Equation1252_pointedIdentityC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3484_not_StructuralFrom_Equation1252_pointedIdentityC2

theorem Equation107_not_StructuralFrom_Equation11_pointedIdentityC3 :
    ¬ Law107.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term11)
    (by rw [PointedIdentityCounting.C3.target107]; decide)
    (by rw [PointedIdentityCounting.C3.target107, PointedIdentityCounting.C3.source11]; decide)

theorem Equation819_not_StructuralFrom_Equation11_pointedIdentityC3 :
    ¬ Law819.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term11)
    (by rw [PointedIdentityCounting.C3.target819]; decide)
    (by rw [PointedIdentityCounting.C3.target819, PointedIdentityCounting.C3.source11]; decide)

theorem Equation825_not_StructuralFrom_Equation11_pointedIdentityC3 :
    ¬ Law825.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term11)
    (by rw [PointedIdentityCounting.C3.target825]; decide)
    (by rw [PointedIdentityCounting.C3.target825, PointedIdentityCounting.C3.source11]; decide)

theorem Equation845_not_StructuralFrom_Equation11_pointedIdentityC3 :
    ¬ Law845.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term11)
    (by rw [PointedIdentityCounting.C3.target845]; decide)
    (by rw [PointedIdentityCounting.C3.target845, PointedIdentityCounting.C3.source11]; decide)

theorem Equation1225_not_StructuralFrom_Equation11_pointedIdentityC3 :
    ¬ Law1225.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term11)
    (by rw [PointedIdentityCounting.C3.target1225]; decide)
    (by rw [PointedIdentityCounting.C3.target1225, PointedIdentityCounting.C3.source11]; decide)

theorem Equation1251_not_StructuralFrom_Equation11_pointedIdentityC3 :
    ¬ Law1251.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term11)
    (by rw [PointedIdentityCounting.C3.target1251]; decide)
    (by rw [PointedIdentityCounting.C3.target1251, PointedIdentityCounting.C3.source11]; decide)

theorem Equation1252_not_StructuralFrom_Equation11_pointedIdentityC3 :
    ¬ Law1252.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term11)
    (by rw [PointedIdentityCounting.C3.target1252]; decide)
    (by rw [PointedIdentityCounting.C3.target1252, PointedIdentityCounting.C3.source11]; decide)

theorem Equation1429_not_StructuralFrom_Equation11_pointedIdentityC3 :
    ¬ Law1429.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term11)
    (by rw [PointedIdentityCounting.C3.target1429]; decide)
    (by rw [PointedIdentityCounting.C3.target1429, PointedIdentityCounting.C3.source11]; decide)

theorem Equation3457_not_StructuralFrom_Equation11_pointedIdentityC3 :
    ¬ Law3457.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term11)
    (by rw [PointedIdentityCounting.C3.target3457]; decide)
    (by rw [PointedIdentityCounting.C3.target3457, PointedIdentityCounting.C3.source11]; decide)

theorem Equation105_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law105.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target105]; decide)
    (by rw [PointedIdentityCounting.C3.target105, PointedIdentityCounting.C3.source56]; decide)

theorem Equation427_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law427.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target427]; decide)
    (by rw [PointedIdentityCounting.C3.target427, PointedIdentityCounting.C3.source56]; decide)

theorem Equation615_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law615.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target615]; decide)
    (by rw [PointedIdentityCounting.C3.target615, PointedIdentityCounting.C3.source56]; decide)

theorem Equation623_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law623.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target623]; decide)
    (by rw [PointedIdentityCounting.C3.target623, PointedIdentityCounting.C3.source56]; decide)

theorem Equation632_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law632.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target632]; decide)
    (by rw [PointedIdentityCounting.C3.target632, PointedIdentityCounting.C3.source56]; decide)

theorem Equation639_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law639.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target639]; decide)
    (by rw [PointedIdentityCounting.C3.target639, PointedIdentityCounting.C3.source56]; decide)

theorem Equation826_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law826.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target826]; decide)
    (by rw [PointedIdentityCounting.C3.target826, PointedIdentityCounting.C3.source56]; decide)

theorem Equation836_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law836.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target836]; decide)
    (by rw [PointedIdentityCounting.C3.target836, PointedIdentityCounting.C3.source56]; decide)

theorem Equation843_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law843.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target843]; decide)
    (by rw [PointedIdentityCounting.C3.target843, PointedIdentityCounting.C3.source56]; decide)

theorem Equation1021_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law1021.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target1021]; decide)
    (by rw [PointedIdentityCounting.C3.target1021, PointedIdentityCounting.C3.source56]; decide)

theorem Equation1026_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law1026.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target1026]; decide)
    (by rw [PointedIdentityCounting.C3.target1026, PointedIdentityCounting.C3.source56]; decide)

theorem Equation1029_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law1029.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target1029]; decide)
    (by rw [PointedIdentityCounting.C3.target1029, PointedIdentityCounting.C3.source56]; decide)

theorem Equation1053_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law1053.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target1053]; decide)
    (by rw [PointedIdentityCounting.C3.target1053, PointedIdentityCounting.C3.source56]; decide)

theorem Equation1254_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law1254.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target1254]; decide)
    (by rw [PointedIdentityCounting.C3.target1254, PointedIdentityCounting.C3.source56]; decide)

theorem Equation1632_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law1632.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target1632]; decide)
    (by rw [PointedIdentityCounting.C3.target1632, PointedIdentityCounting.C3.source56]; decide)

theorem Equation1635_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law1635.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target1635]; decide)
    (by rw [PointedIdentityCounting.C3.target1635, PointedIdentityCounting.C3.source56]; decide)

theorem Equation3484_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law3484.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target3484]; decide)
    (by rw [PointedIdentityCounting.C3.target3484, PointedIdentityCounting.C3.source56]; decide)

theorem Equation4381_not_StructuralFrom_Equation56_pointedIdentityC3 :
    ¬ Law4381.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term56)
    (by rw [PointedIdentityCounting.C3.target4381]; decide)
    (by rw [PointedIdentityCounting.C3.target4381, PointedIdentityCounting.C3.source56]; decide)

theorem Equation630_not_StructuralFrom_Equation108_pointedIdentityC3 :
    ¬ Law630.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term108)
    (by rw [PointedIdentityCounting.C3.target630]; decide)
    (by rw [PointedIdentityCounting.C3.target630, PointedIdentityCounting.C3.source108]; decide)

theorem Equation818_not_StructuralFrom_Equation108_pointedIdentityC3 :
    ¬ Law818.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term108)
    (by rw [PointedIdentityCounting.C3.target818]; decide)
    (by rw [PointedIdentityCounting.C3.target818, PointedIdentityCounting.C3.source108]; decide)

theorem Equation825_not_StructuralFrom_Equation108_pointedIdentityC3 :
    ¬ Law825.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term108)
    (by rw [PointedIdentityCounting.C3.target825]; decide)
    (by rw [PointedIdentityCounting.C3.target825, PointedIdentityCounting.C3.source108]; decide)

theorem Equation845_not_StructuralFrom_Equation108_pointedIdentityC3 :
    ¬ Law845.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term108)
    (by rw [PointedIdentityCounting.C3.target845]; decide)
    (by rw [PointedIdentityCounting.C3.target845, PointedIdentityCounting.C3.source108]; decide)

theorem Equation1224_not_StructuralFrom_Equation108_pointedIdentityC3 :
    ¬ Law1224.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term108)
    (by rw [PointedIdentityCounting.C3.target1224]; decide)
    (by rw [PointedIdentityCounting.C3.target1224, PointedIdentityCounting.C3.source108]; decide)

theorem Equation1249_not_StructuralFrom_Equation108_pointedIdentityC3 :
    ¬ Law1249.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term108)
    (by rw [PointedIdentityCounting.C3.target1249]; decide)
    (by rw [PointedIdentityCounting.C3.target1249, PointedIdentityCounting.C3.source108]; decide)

theorem Equation1251_not_StructuralFrom_Equation108_pointedIdentityC3 :
    ¬ Law1251.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term108)
    (by rw [PointedIdentityCounting.C3.target1251]; decide)
    (by rw [PointedIdentityCounting.C3.target1251, PointedIdentityCounting.C3.source108]; decide)

theorem Equation3457_not_StructuralFrom_Equation108_pointedIdentityC3 :
    ¬ Law3457.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term108)
    (by rw [PointedIdentityCounting.C3.target3457]; decide)
    (by rw [PointedIdentityCounting.C3.target3457, PointedIdentityCounting.C3.source108]; decide)

theorem Equation3484_not_StructuralFrom_Equation108_pointedIdentityC3 :
    ¬ Law3484.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term108)
    (by rw [PointedIdentityCounting.C3.target3484]; decide)
    (by rw [PointedIdentityCounting.C3.target3484, PointedIdentityCounting.C3.source108]; decide)

theorem Equation310_not_StructuralFrom_Equation440_pointedIdentityC3 :
    ¬ Law310.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term440)
    (by rw [PointedIdentityCounting.C3.target310]; decide)
    (by rw [PointedIdentityCounting.C3.target310, PointedIdentityCounting.C3.source440]; decide)

theorem Equation846_not_StructuralFrom_Equation440_pointedIdentityC3 :
    ¬ Law846.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term440)
    (by rw [PointedIdentityCounting.C3.target846]; decide)
    (by rw [PointedIdentityCounting.C3.target846, PointedIdentityCounting.C3.source440]; decide)

theorem Equation1718_not_StructuralFrom_Equation440_pointedIdentityC3 :
    ¬ Law1718.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term440)
    (by rw [PointedIdentityCounting.C3.target1718]; decide)
    (by rw [PointedIdentityCounting.C3.target1718, PointedIdentityCounting.C3.source440]; decide)

theorem Equation3268_not_StructuralFrom_Equation440_pointedIdentityC3 :
    ¬ Law3268.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term440)
    (by rw [PointedIdentityCounting.C3.target3268]; decide)
    (by rw [PointedIdentityCounting.C3.target3268, PointedIdentityCounting.C3.source440]; decide)

theorem Equation3537_not_StructuralFrom_Equation440_pointedIdentityC3 :
    ¬ Law3537.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term440)
    (by rw [PointedIdentityCounting.C3.target3537]; decide)
    (by rw [PointedIdentityCounting.C3.target3537, PointedIdentityCounting.C3.source440]; decide)

theorem Equation4388_not_StructuralFrom_Equation440_pointedIdentityC3 :
    ¬ Law4388.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term440)
    (by rw [PointedIdentityCounting.C3.target4388]; decide)
    (by rw [PointedIdentityCounting.C3.target4388, PointedIdentityCounting.C3.source440]; decide)

theorem Equation843_not_StructuralFrom_Equation643_pointedIdentityC3 :
    ¬ Law843.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term643)
    (by rw [PointedIdentityCounting.C3.target843]; decide)
    (by rw [PointedIdentityCounting.C3.target843, PointedIdentityCounting.C3.source643]; decide)

theorem Equation1254_not_StructuralFrom_Equation643_pointedIdentityC3 :
    ¬ Law1254.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term643)
    (by rw [PointedIdentityCounting.C3.target1254]; decide)
    (by rw [PointedIdentityCounting.C3.target1254, PointedIdentityCounting.C3.source643]; decide)

theorem Equation3471_not_StructuralFrom_Equation643_pointedIdentityC3 :
    ¬ Law3471.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term643)
    (by rw [PointedIdentityCounting.C3.target3471]; decide)
    (by rw [PointedIdentityCounting.C3.target3471, PointedIdentityCounting.C3.source643]; decide)

theorem Equation3484_not_StructuralFrom_Equation643_pointedIdentityC3 :
    ¬ Law3484.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term643)
    (by rw [PointedIdentityCounting.C3.target3484]; decide)
    (by rw [PointedIdentityCounting.C3.target3484, PointedIdentityCounting.C3.source643]; decide)

theorem Equation4381_not_StructuralFrom_Equation643_pointedIdentityC3 :
    ¬ Law4381.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term643)
    (by rw [PointedIdentityCounting.C3.target4381]; decide)
    (by rw [PointedIdentityCounting.C3.target4381, PointedIdentityCounting.C3.source643]; decide)

theorem Equation440_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law440.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target440]; decide)
    (by rw [PointedIdentityCounting.C3.target440, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation820_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law820.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target820]; decide)
    (by rw [PointedIdentityCounting.C3.target820, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation823_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law823.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target823]; decide)
    (by rw [PointedIdentityCounting.C3.target823, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation835_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law835.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target835]; decide)
    (by rw [PointedIdentityCounting.C3.target835, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation842_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law842.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target842]; decide)
    (by rw [PointedIdentityCounting.C3.target842, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation846_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law846.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target846]; decide)
    (by rw [PointedIdentityCounting.C3.target846, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation1637_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law1637.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target1637]; decide)
    (by rw [PointedIdentityCounting.C3.target1637, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation1731_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law1731.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target1731]; decide)
    (by rw [PointedIdentityCounting.C3.target1731, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation3268_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law3268.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target3268]; decide)
    (by rw [PointedIdentityCounting.C3.target3268, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation3537_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law3537.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target3537]; decide)
    (by rw [PointedIdentityCounting.C3.target3537, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation3660_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law3660.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target3660]; decide)
    (by rw [PointedIdentityCounting.C3.target3660, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation3661_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law3661.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target3661]; decide)
    (by rw [PointedIdentityCounting.C3.target3661, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation4388_not_StructuralFrom_Equation1049_pointedIdentityC3 :
    ¬ Law4388.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1049)
    (by rw [PointedIdentityCounting.C3.target4388]; decide)
    (by rw [PointedIdentityCounting.C3.target4388, PointedIdentityCounting.C3.source1049]; decide)

theorem Equation819_not_StructuralFrom_Equation1252_pointedIdentityC3 :
    ¬ Law819.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1252)
    (by rw [PointedIdentityCounting.C3.target819]; decide)
    (by rw [PointedIdentityCounting.C3.target819, PointedIdentityCounting.C3.source1252]; decide)

theorem Equation825_not_StructuralFrom_Equation1252_pointedIdentityC3 :
    ¬ Law825.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1252)
    (by rw [PointedIdentityCounting.C3.target825]; decide)
    (by rw [PointedIdentityCounting.C3.target825, PointedIdentityCounting.C3.source1252]; decide)

theorem Equation845_not_StructuralFrom_Equation1252_pointedIdentityC3 :
    ¬ Law845.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1252)
    (by rw [PointedIdentityCounting.C3.target845]; decide)
    (by rw [PointedIdentityCounting.C3.target845, PointedIdentityCounting.C3.source1252]; decide)

theorem Equation1225_not_StructuralFrom_Equation1252_pointedIdentityC3 :
    ¬ Law1225.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1252)
    (by rw [PointedIdentityCounting.C3.target1225]; decide)
    (by rw [PointedIdentityCounting.C3.target1225, PointedIdentityCounting.C3.source1252]; decide)

theorem Equation1251_not_StructuralFrom_Equation1252_pointedIdentityC3 :
    ¬ Law1251.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1252)
    (by rw [PointedIdentityCounting.C3.target1251]; decide)
    (by rw [PointedIdentityCounting.C3.target1251, PointedIdentityCounting.C3.source1252]; decide)

theorem Equation3457_not_StructuralFrom_Equation1252_pointedIdentityC3 :
    ¬ Law3457.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1252)
    (by rw [PointedIdentityCounting.C3.target3457]; decide)
    (by rw [PointedIdentityCounting.C3.target3457, PointedIdentityCounting.C3.source1252]; decide)

theorem Equation3465_not_StructuralFrom_Equation1252_pointedIdentityC3 :
    ¬ Law3465.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C3.H) (t := PointedIdentityCounting.C3.term1252)
    (by rw [PointedIdentityCounting.C3.target3465]; decide)
    (by rw [PointedIdentityCounting.C3.target3465, PointedIdentityCounting.C3.source1252]; decide)

theorem Equation622_not_StructuralFrom_Equation11_pointedIdentityC4 :
    ¬ Law622.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term11)
    (by rw [PointedIdentityCounting.C4.target622]; decide)
    (by rw [PointedIdentityCounting.C4.target622, PointedIdentityCounting.C4.source11]; decide)

theorem Equation1226_not_StructuralFrom_Equation11_pointedIdentityC4 :
    ¬ Law1226.StructuralFrom Law11 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term11)
    (by rw [PointedIdentityCounting.C4.target1226]; decide)
    (by rw [PointedIdentityCounting.C4.target1226, PointedIdentityCounting.C4.source11]; decide)

theorem Equation417_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law417.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target417]; decide)
    (by rw [PointedIdentityCounting.C4.target417, PointedIdentityCounting.C4.source56]; decide)

theorem Equation419_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law419.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target419]; decide)
    (by rw [PointedIdentityCounting.C4.target419, PointedIdentityCounting.C4.source56]; decide)

theorem Equation617_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law617.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target617]; decide)
    (by rw [PointedIdentityCounting.C4.target617, PointedIdentityCounting.C4.source56]; decide)

theorem Equation620_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law620.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target620]; decide)
    (by rw [PointedIdentityCounting.C4.target620, PointedIdentityCounting.C4.source56]; decide)

theorem Equation630_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law630.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target630]; decide)
    (by rw [PointedIdentityCounting.C4.target630, PointedIdentityCounting.C4.source56]; decide)

theorem Equation643_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law643.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target643]; decide)
    (by rw [PointedIdentityCounting.C4.target643, PointedIdentityCounting.C4.source56]; decide)

theorem Equation818_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law818.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target818]; decide)
    (by rw [PointedIdentityCounting.C4.target818, PointedIdentityCounting.C4.source56]; decide)

theorem Equation819_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law819.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target819]; decide)
    (by rw [PointedIdentityCounting.C4.target819, PointedIdentityCounting.C4.source56]; decide)

theorem Equation825_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law825.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target825]; decide)
    (by rw [PointedIdentityCounting.C4.target825, PointedIdentityCounting.C4.source56]; decide)

theorem Equation845_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law845.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target845]; decide)
    (by rw [PointedIdentityCounting.C4.target845, PointedIdentityCounting.C4.source56]; decide)

theorem Equation1035_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law1035.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target1035]; decide)
    (by rw [PointedIdentityCounting.C4.target1035, PointedIdentityCounting.C4.source56]; decide)

theorem Equation1224_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law1224.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target1224]; decide)
    (by rw [PointedIdentityCounting.C4.target1224, PointedIdentityCounting.C4.source56]; decide)

theorem Equation1229_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law1229.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target1229]; decide)
    (by rw [PointedIdentityCounting.C4.target1229, PointedIdentityCounting.C4.source56]; decide)

theorem Equation1239_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law1239.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target1239]; decide)
    (by rw [PointedIdentityCounting.C4.target1239, PointedIdentityCounting.C4.source56]; decide)

theorem Equation1241_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law1241.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target1241]; decide)
    (by rw [PointedIdentityCounting.C4.target1241, PointedIdentityCounting.C4.source56]; decide)

theorem Equation1249_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law1249.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target1249]; decide)
    (by rw [PointedIdentityCounting.C4.target1249, PointedIdentityCounting.C4.source56]; decide)

theorem Equation1256_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law1256.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target1256]; decide)
    (by rw [PointedIdentityCounting.C4.target1256, PointedIdentityCounting.C4.source56]; decide)

theorem Equation3259_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law3259.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target3259]; decide)
    (by rw [PointedIdentityCounting.C4.target3259, PointedIdentityCounting.C4.source56]; decide)

theorem Equation3457_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law3457.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target3457]; decide)
    (by rw [PointedIdentityCounting.C4.target3457, PointedIdentityCounting.C4.source56]; decide)

theorem Equation3462_not_StructuralFrom_Equation56_pointedIdentityC4 :
    ¬ Law3462.StructuralFrom Law56 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term56)
    (by rw [PointedIdentityCounting.C4.target3462]; decide)
    (by rw [PointedIdentityCounting.C4.target3462, PointedIdentityCounting.C4.source56]; decide)

theorem Equation819_not_StructuralFrom_Equation108_pointedIdentityC4 :
    ¬ Law819.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term108)
    (by rw [PointedIdentityCounting.C4.target819]; decide)
    (by rw [PointedIdentityCounting.C4.target819, PointedIdentityCounting.C4.source108]; decide)

theorem Equation1225_not_StructuralFrom_Equation108_pointedIdentityC4 :
    ¬ Law1225.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term108)
    (by rw [PointedIdentityCounting.C4.target1225]; decide)
    (by rw [PointedIdentityCounting.C4.target1225, PointedIdentityCounting.C4.source108]; decide)

theorem Equation1226_not_StructuralFrom_Equation108_pointedIdentityC4 :
    ¬ Law1226.StructuralFrom Law108 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term108)
    (by rw [PointedIdentityCounting.C4.target1226]; decide)
    (by rw [PointedIdentityCounting.C4.target1226, PointedIdentityCounting.C4.source108]; decide)

theorem Equation820_not_StructuralFrom_Equation440_pointedIdentityC4 :
    ¬ Law820.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term440)
    (by rw [PointedIdentityCounting.C4.target820]; decide)
    (by rw [PointedIdentityCounting.C4.target820, PointedIdentityCounting.C4.source440]; decide)

theorem Equation823_not_StructuralFrom_Equation440_pointedIdentityC4 :
    ¬ Law823.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term440)
    (by rw [PointedIdentityCounting.C4.target823]; decide)
    (by rw [PointedIdentityCounting.C4.target823, PointedIdentityCounting.C4.source440]; decide)

theorem Equation835_not_StructuralFrom_Equation440_pointedIdentityC4 :
    ¬ Law835.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term440)
    (by rw [PointedIdentityCounting.C4.target835]; decide)
    (by rw [PointedIdentityCounting.C4.target835, PointedIdentityCounting.C4.source440]; decide)

theorem Equation842_not_StructuralFrom_Equation440_pointedIdentityC4 :
    ¬ Law842.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term440)
    (by rw [PointedIdentityCounting.C4.target842]; decide)
    (by rw [PointedIdentityCounting.C4.target842, PointedIdentityCounting.C4.source440]; decide)

theorem Equation1036_not_StructuralFrom_Equation440_pointedIdentityC4 :
    ¬ Law1036.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term440)
    (by rw [PointedIdentityCounting.C4.target1036]; decide)
    (by rw [PointedIdentityCounting.C4.target1036, PointedIdentityCounting.C4.source440]; decide)

theorem Equation3315_not_StructuralFrom_Equation440_pointedIdentityC4 :
    ¬ Law3315.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term440)
    (by rw [PointedIdentityCounting.C4.target3315]; decide)
    (by rw [PointedIdentityCounting.C4.target3315, PointedIdentityCounting.C4.source440]; decide)

theorem Equation3660_not_StructuralFrom_Equation440_pointedIdentityC4 :
    ¬ Law3660.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term440)
    (by rw [PointedIdentityCounting.C4.target3660]; decide)
    (by rw [PointedIdentityCounting.C4.target3660, PointedIdentityCounting.C4.source440]; decide)

theorem Equation3661_not_StructuralFrom_Equation440_pointedIdentityC4 :
    ¬ Law3661.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term440)
    (by rw [PointedIdentityCounting.C4.target3661]; decide)
    (by rw [PointedIdentityCounting.C4.target3661, PointedIdentityCounting.C4.source440]; decide)

theorem Equation3721_not_StructuralFrom_Equation440_pointedIdentityC4 :
    ¬ Law3721.StructuralFrom Law440 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term440)
    (by rw [PointedIdentityCounting.C4.target3721]; decide)
    (by rw [PointedIdentityCounting.C4.target3721, PointedIdentityCounting.C4.source440]; decide)

theorem Equation630_not_StructuralFrom_Equation643_pointedIdentityC4 :
    ¬ Law630.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term643)
    (by rw [PointedIdentityCounting.C4.target630]; decide)
    (by rw [PointedIdentityCounting.C4.target630, PointedIdentityCounting.C4.source643]; decide)

theorem Equation818_not_StructuralFrom_Equation643_pointedIdentityC4 :
    ¬ Law818.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term643)
    (by rw [PointedIdentityCounting.C4.target818]; decide)
    (by rw [PointedIdentityCounting.C4.target818, PointedIdentityCounting.C4.source643]; decide)

theorem Equation819_not_StructuralFrom_Equation643_pointedIdentityC4 :
    ¬ Law819.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term643)
    (by rw [PointedIdentityCounting.C4.target819]; decide)
    (by rw [PointedIdentityCounting.C4.target819, PointedIdentityCounting.C4.source643]; decide)

theorem Equation825_not_StructuralFrom_Equation643_pointedIdentityC4 :
    ¬ Law825.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term643)
    (by rw [PointedIdentityCounting.C4.target825]; decide)
    (by rw [PointedIdentityCounting.C4.target825, PointedIdentityCounting.C4.source643]; decide)

theorem Equation845_not_StructuralFrom_Equation643_pointedIdentityC4 :
    ¬ Law845.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term643)
    (by rw [PointedIdentityCounting.C4.target845]; decide)
    (by rw [PointedIdentityCounting.C4.target845, PointedIdentityCounting.C4.source643]; decide)

theorem Equation1224_not_StructuralFrom_Equation643_pointedIdentityC4 :
    ¬ Law1224.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term643)
    (by rw [PointedIdentityCounting.C4.target1224]; decide)
    (by rw [PointedIdentityCounting.C4.target1224, PointedIdentityCounting.C4.source643]; decide)

theorem Equation1249_not_StructuralFrom_Equation643_pointedIdentityC4 :
    ¬ Law1249.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term643)
    (by rw [PointedIdentityCounting.C4.target1249]; decide)
    (by rw [PointedIdentityCounting.C4.target1249, PointedIdentityCounting.C4.source643]; decide)

theorem Equation1256_not_StructuralFrom_Equation643_pointedIdentityC4 :
    ¬ Law1256.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term643)
    (by rw [PointedIdentityCounting.C4.target1256]; decide)
    (by rw [PointedIdentityCounting.C4.target1256, PointedIdentityCounting.C4.source643]; decide)

theorem Equation3457_not_StructuralFrom_Equation643_pointedIdentityC4 :
    ¬ Law3457.StructuralFrom Law643 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term643)
    (by rw [PointedIdentityCounting.C4.target3457]; decide)
    (by rw [PointedIdentityCounting.C4.target3457, PointedIdentityCounting.C4.source643]; decide)

theorem Equation436_not_StructuralFrom_Equation1049_pointedIdentityC4 :
    ¬ Law436.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term1049)
    (by rw [PointedIdentityCounting.C4.target436]; decide)
    (by rw [PointedIdentityCounting.C4.target436, PointedIdentityCounting.C4.source1049]; decide)

theorem Equation1036_not_StructuralFrom_Equation1049_pointedIdentityC4 :
    ¬ Law1036.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term1049)
    (by rw [PointedIdentityCounting.C4.target1036]; decide)
    (by rw [PointedIdentityCounting.C4.target1036, PointedIdentityCounting.C4.source1049]; decide)

theorem Equation3258_not_StructuralFrom_Equation1049_pointedIdentityC4 :
    ¬ Law3258.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term1049)
    (by rw [PointedIdentityCounting.C4.target3258]; decide)
    (by rw [PointedIdentityCounting.C4.target3258, PointedIdentityCounting.C4.source1049]; decide)

theorem Equation3315_not_StructuralFrom_Equation1049_pointedIdentityC4 :
    ¬ Law3315.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term1049)
    (by rw [PointedIdentityCounting.C4.target3315]; decide)
    (by rw [PointedIdentityCounting.C4.target3315, PointedIdentityCounting.C4.source1049]; decide)

theorem Equation3712_not_StructuralFrom_Equation1049_pointedIdentityC4 :
    ¬ Law3712.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term1049)
    (by rw [PointedIdentityCounting.C4.target3712]; decide)
    (by rw [PointedIdentityCounting.C4.target3712, PointedIdentityCounting.C4.source1049]; decide)

theorem Equation3721_not_StructuralFrom_Equation1049_pointedIdentityC4 :
    ¬ Law3721.StructuralFrom Law1049 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term1049)
    (by rw [PointedIdentityCounting.C4.target3721]; decide)
    (by rw [PointedIdentityCounting.C4.target3721, PointedIdentityCounting.C4.source1049]; decide)

theorem Equation1226_not_StructuralFrom_Equation1252_pointedIdentityC4 :
    ¬ Law1226.StructuralFrom Law1252 :=
  PointedIdentityCounting.not_structural (H := PointedIdentityCounting.C4.H) (t := PointedIdentityCounting.C4.term1252)
    (by rw [PointedIdentityCounting.C4.target1226]; decide)
    (by rw [PointedIdentityCounting.C4.target1226, PointedIdentityCounting.C4.source1252]; decide)

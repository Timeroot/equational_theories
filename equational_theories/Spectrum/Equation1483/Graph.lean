import equational_theories.Definability.Central1483Translations

/-!
# The directed graph of an E1483 operation

An edge `a → b` means that `b` occurs in row `a`. Column membership is the
transpose of this relation. Every product chooses a two-step path, and the
edges rotate in directed triangles. These facts hold without finiteness.
-/
namespace Spectrum.E1483.Graph
variable {G : Type*} [Magma G] (h : Equation1483 G)

def Edge (a b : G) : Prop := ∃ z, a ◇ z = b

include h

/-- An edge gives the two reverse products completing its directed triangle. -/
theorem triangle {a b : G} (hab : Edge a b) :
    (b ◇ a) ◇ b = a ∧ a ◇ (b ◇ a) = b := by
  obtain ⟨z, rfl⟩ := hab
  exact ⟨CentralDual.dual h a z a, CentralDual.left_regular h a z⟩

theorem edge_iff_column (a b : G) : Edge a b ↔ ∃ z, z ◇ b = a := by
  constructor
  · intro hab
    exact ⟨b ◇ a, (triangle h hab).1⟩
  · rintro ⟨z, rfl⟩
    exact ⟨b ◇ (z ◇ b), (h b z b).symm⟩

/-- Multiplication selects an intermediate vertex between its two inputs. -/
theorem product_path (a b : G) : Edge a (a ◇ b) ∧ Edge (a ◇ b) b := by
  exact ⟨⟨b, rfl⟩, (edge_iff_column h (a ◇ b) b).mpr ⟨a, rfl⟩⟩

/-- Along any edge, the two translations jointly recover their argument. -/
theorem edge_law {a b : G} (hab : Edge a b) (x : G) :
    (a ◇ x) ◇ (x ◇ b) = x := by
  obtain ⟨z, rfl⟩ := hab
  exact (h x a z).symm

/-- Left translation at an idempotent has constant third iterate. -/
theorem idempotent_third (a : G) (ha : a ◇ a = a) (x : G) :
    a ◇ (a ◇ (a ◇ x)) = a := by
  simpa only [ha] using (h a a x).symm

/-- A nonconstant idempotent row has a distinct image point mapping back to it.
This permits a stronger choice of label one in finite normalizations. -/
theorem idempotent_image_predecessor (a : G) (ha : a ◇ a = a)
    (hn : ∃ x, a ◇ x ≠ a) :
    ∃ b, Edge a b ∧ b ≠ a ∧ a ◇ b = a := by
  obtain ⟨x, hx⟩ := hn
  by_cases hh : a ◇ (a ◇ x) = a
  · exact ⟨a ◇ x, ⟨x, rfl⟩, hx, hh⟩
  · exact ⟨a ◇ (a ◇ x), ⟨a ◇ x, rfl⟩, hh, idempotent_third h a ha x⟩

/-- If a point fixes its square on the left, the point and its square form
 the usual two-point NAND table (possibly collapsed to a singleton). -/
theorem nand_pair (a : G) (ha : a ◇ (a ◇ a) = a ◇ a) :
    (a ◇ a) ◇ a = a ◇ a ∧ (a ◇ a) ◇ (a ◇ a) = a := by
  constructor
  · simpa only [ha] using CentralDual.right_regular h a a
  · simpa only [ha] using (h a a a).symm

end Spectrum.E1483.Graph

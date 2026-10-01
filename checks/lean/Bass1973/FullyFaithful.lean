import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Full faithful functors reflect isomorphism classes

This verifies the assertion in Bass, *Algebraic K-Theory*, Chapter I,
§1 (Russian edition, Mir, 1973, p. 16). The book's functor `T` is `F`,
its objects `A`, `B` are `X`, `Y`, and its full and faithful hypotheses
are `F.Full` and `F.Faithful`. This does not prove the subsequent
equivalence criterion or its construction of a quasi-inverse functor.

For a full faithful functor, an isomorphism between the images of two
objects lifts to an isomorphism of the objects. Fullness lifts the
forward and inverse morphisms separately; faithfulness reflects both
inverse equations after applying the functor laws.

The composition `f ≫ g` means first `f`, then `g`.
-/

namespace Bass1973

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]

/-- An explicit lift using fullness and the two faithful inverse checks. -/
noncomputable def liftImageIso (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : C} (e : F.obj X ≅ F.obj Y) : X ≅ Y where
  hom := F.preimage e.hom
  inv := F.preimage e.inv
  hom_inv_id := by
    apply F.map_injective
    calc
      F.map (F.preimage e.hom ≫ F.preimage e.inv) =
          F.map (F.preimage e.hom) ≫ F.map (F.preimage e.inv) :=
        F.map_comp _ _
      _ = e.hom ≫ e.inv := by rw [F.map_preimage, F.map_preimage]
      _ = 𝟙 (F.obj X) := e.hom_inv_id
      _ = F.map (𝟙 X) := (F.map_id X).symm
  inv_hom_id := by
    apply F.map_injective
    calc
      F.map (F.preimage e.inv ≫ F.preimage e.hom) =
          F.map (F.preimage e.inv) ≫ F.map (F.preimage e.hom) :=
        F.map_comp _ _
      _ = e.inv ≫ e.hom := by rw [F.map_preimage, F.map_preimage]
      _ = 𝟙 (F.obj Y) := e.inv_hom_id
      _ = F.map (𝟙 Y) := (F.map_id Y).symm

/-- Images are isomorphic exactly when the original objects are isomorphic. -/
theorem imageIso_iff (F : C ⥤ D) [F.Full] [F.Faithful] {X Y : C} :
    Nonempty (F.obj X ≅ F.obj Y) ↔ Nonempty (X ≅ Y) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨liftImageIso F e⟩
  · rintro ⟨e⟩
    exact ⟨F.mapIso e⟩

#print axioms liftImageIso
#print axioms imageIso_iff

end Bass1973

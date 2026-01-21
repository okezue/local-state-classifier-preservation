import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# The local state classifier `Ξ` and a robust preservation criterion

This file formalizes the *local state classifier* of a category `C` as the colimit of the
inclusion of the wide subcategory of monomorphisms into `C`.

Concretely, we define

* `MonoWide C` : the wide subcategory of `C` consisting of monomorphisms,
* `monoInclusion C : MonoWide C ⥤ C` : the forgetful inclusion,
* `Ξ C := colimit (monoInclusion C)` when this colimit exists.

We then prove a clean criterion for when a functor `F : C ⥤ D` preserves `Ξ`:

* `F` sends monomorphisms to monomorphisms (so it induces a functor on mono-wide subcategories),
* `F` preserves the defining colimit (e.g. if `F` is a left adjoint), and
* the induced functor on mono-wide subcategories is *final*.

Under these hypotheses we build a canonical isomorphism `F.obj (Ξ C) ≅ Ξ D`.

Finally, we package the *property* of preserving `Ξ` as a Prop `PreservesΞ F` and show it is
closed under identities and composition.

## Relation to geometric morphisms (informal)
Inverse-image functors of geometric morphisms are left exact (hence preserve monomorphisms) and
are left adjoints (hence preserve all colimits). Thus, once you establish the finality hypothesis
(on the induced functor between mono-wide subcategories), you can apply `mapΞIso_of_isLeftAdjoint`.

## Important note
We do **not** formalize Grothendieck topoi or geometric morphisms here; we work at the level of
arbitrary categories with the required colimits.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace LocalStateClassifier

/-- The wide subcategory of monomorphisms in `C`. -/
abbrev MonoWide (C : Type u₁) [Category.{v₁} C] : Type u₁ :=
  WideSubcategory (MorphismProperty.monomorphisms C)

/-- The inclusion `MonoWide C ⥤ C`. -/
abbrev monoInclusion (C : Type u₁) [Category.{v₁} C] : MonoWide C ⥤ C :=
  wideSubcategoryInclusion (MorphismProperty.monomorphisms C)

/-- The local state classifier `Ξ(C)` (when it exists): the colimit of `MonoWide C ⥤ C`. -/
noncomputable abbrev Ξ (C : Type u₁) [Category.{v₁} C]
    [HasColimit (monoInclusion C)] : C :=
  colimit (monoInclusion C)

/-- A lightweight predicate: `F` sends monomorphisms to monomorphisms.

(We also provide a lemma showing this follows from the bundled typeclass
`CategoryTheory.Functor.PreservesMonomorphisms`.)
-/
def PreservesMonos {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Mono f → Mono (F.map f)

namespace PreservesMonos

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- If `F` has the standard typeclass `[F.PreservesMonomorphisms]`, then it satisfies
our unbundled `PreservesMonos` predicate. -/
lemma of_typeclass (F : C ⥤ D) [F.PreservesMonomorphisms] : PreservesMonos F := by
  intro X Y f hf
  -- Turn the explicit proof into an instance so `infer_instance` can use `Functor.map_mono`.
  haveI : Mono f := hf
  infer_instance

/-- If `F : C ⥤ D` preserves monos, it induces a functor on mono-wide subcategories. -/
noncomputable def monoMap (F : C ⥤ D) (hF : PreservesMonos F) : MonoWide C ⥤ MonoWide D where
  obj X := ⟨F.obj X.obj⟩
  map {X Y} f := ⟨F.map f.1, by
    have hm : Mono f.1 := f.2
    exact hF f.1 hm⟩
  map_id X := Subtype.ext (by simp)
  map_comp {X Y Z} f g := Subtype.ext (by simp)

lemma monoMap_obj (F : C ⥤ D) (hF : PreservesMonos F) (X : MonoWide C) :
    ((monoMap F hF).obj X).obj = F.obj X.obj := rfl

lemma monoMap_map_val (F : C ⥤ D) (hF : PreservesMonos F)
    {X Y : MonoWide C} (f : X ⟶ Y) : ((monoMap F hF).map f).1 = F.map f.1 := rfl

/-- The diagram `monoInclusion C ⋙ F` is naturally isomorphic to
`monoMap F ⋙ monoInclusion D`. -/
noncomputable def monoInclusionCompIso (F : C ⥤ D) (hF : PreservesMonos F) :
    (monoInclusion C) ⋙ F ≅ (monoMap F hF) ⋙ (monoInclusion D) :=
  NatIso.ofComponents (fun X => Iso.refl _) (by intros; simp [monoMap_map_val])

/-- **Main theorem.**

If `F` preserves the colimit defining `Ξ(C)` and the induced `monoMap` is final,
then `F` sends `Ξ(C)` to `Ξ(D)` up to canonical isomorphism.
-/
noncomputable def mapΞIso
    (F : C ⥤ D) (hF : PreservesMonos F)
    [HasColimit (monoInclusion C)] [HasColimit (monoInclusion D)]
    [PreservesColimit (monoInclusion C) F]
    [Functor.Final (monoMap F hF)] :
    F.obj (Ξ C) ≅ Ξ D := by
  classical
  -- (1) Use preservation of the defining colimit of `Ξ(C)`.
  let t₁ : IsColimit (F.mapCocone (colimit.cocone (monoInclusion C))) :=
    isColimitOfPreserves F (colimit.isColimit (monoInclusion C))
  have i₁ : F.obj (Ξ C) ≅ colimit ((monoInclusion C) ⋙ F) :=
    t₁.coconePointUniqueUpToIso (colimit.isColimit ((monoInclusion C) ⋙ F))
  -- (2) Replace the diagram `monoInclusion C ⋙ F` by the factorization through `MonoWide D`.
  have i₂ : colimit ((monoInclusion C) ⋙ F) ≅ colimit ((monoMap F hF) ⋙ (monoInclusion D)) :=
    HasColimit.isoOfNatIso (monoInclusionCompIso F hF)
  -- (3) Use finality to replace the colimit over the image by the full mono-diagram in `D`.
  have i₃ : colimit ((monoMap F hF) ⋙ (monoInclusion D)) ≅ colimit (monoInclusion D) :=
    (Functor.Final.colimitIso (monoMap F hF) (monoInclusion D))
  -- Finish.
  exact i₁ ≪≫ i₂ ≪≫ i₃

/-- A convenient corollary: if `F` is a left adjoint (so `F` preserves all colimits),
then finality of `monoMap` already implies preservation of `Ξ`.

This matches the topos situation for inverse-image functors of geometric morphisms.
-/
noncomputable def mapΞIso_of_isLeftAdjoint
    (F : C ⥤ D) (hF : PreservesMonos F)
    [HasColimit (monoInclusion C)] [HasColimit (monoInclusion D)]
    [Functor.Final (monoMap F hF)]
    [Functor.IsLeftAdjoint F] :
    F.obj (Ξ C) ≅ Ξ D := by
  classical
  -- Any left adjoint preserves colimits of any shape.
  haveI : PreservesColimit (monoInclusion C) F := by
    infer_instance
  exact mapΞIso (F := F) (hF := hF)

/-- A version of `mapΞIso_of_isLeftAdjoint` that uses the standard typeclass
`[F.PreservesMonomorphisms]` instead of an explicit `hF`. -/
noncomputable def mapΞIso_of_isLeftAdjoint'
    (F : C ⥤ D) [F.PreservesMonomorphisms]
    [HasColimit (monoInclusion C)] [HasColimit (monoInclusion D)]
    [Functor.Final (monoMap F (of_typeclass F))]
    [Functor.IsLeftAdjoint F] :
    F.obj (Ξ C) ≅ Ξ D := by
  exact mapΞIso_of_isLeftAdjoint (F := F) (hF := of_typeclass F)

end PreservesMonos

/-- The *property* that a functor `F` preserves the local state classifier.

We phrase this purely as the existence of an isomorphism `F.obj (Ξ C) ≅ Ξ D`.
This is the closure-friendly notion.
-/
def PreservesΞ {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    [HasColimit (monoInclusion C)] [HasColimit (monoInclusion D)]
    (F : C ⥤ D) : Prop :=
  Nonempty (F.obj (Ξ C) ≅ Ξ D)

namespace PreservesΞ

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

variable [HasColimit (monoInclusion C)]
variable [HasColimit (monoInclusion D)]
variable [HasColimit (monoInclusion E)]

/-- Identity preserves `Ξ`. -/
lemma id : PreservesΞ (F := (𝟭 C)) := by
  refine ⟨Iso.refl _⟩

/-- Preservation of `Ξ` is closed under composition. -/
lemma comp {F : C ⥤ D} {G : D ⥤ E}
    (hF : PreservesΞ (F := F)) (hG : PreservesΞ (F := G)) :
    PreservesΞ (F := F ⋙ G) := by
  rcases hF with ⟨iF⟩
  rcases hG with ⟨iG⟩
  refine ⟨(G.mapIso iF) ≪≫ iG⟩

end PreservesΞ

end LocalStateClassifier

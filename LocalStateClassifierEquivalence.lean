import LocalStateClassifierSpecialize2
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EssentialImage

open CategoryTheory
open CategoryTheory.Limits
open LocalStateClassifier

namespace LocalStateClassifier.PreservesMonos

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-!
## Mono-wide functoriality: full/faithful/ess-surj descend to `monoMap`

These instances are convenient when the underlying functor is an equivalence.
-/

instance monoMap_faithful (F : C ⥤ D) (hF : PreservesMonos F) [F.Faithful] :
    (monoMap F hF).Faithful where
  map_injective {X Y} f g h := by
    -- `WideSubcategory` morphisms are subtypes, reduce to equality of underlying morphisms.
    apply Subtype.ext
    -- Extract equality of underlying morphisms in `D` and use faithfulness of `F`.
    have h' : F.map f.1 = F.map g.1 := by
      simpa using congrArg Subtype.val h
    exact F.map_injective h'

instance monoMap_full (F : C ⥤ D) (hF : PreservesMonos F) [F.Full] [F.Faithful] :
    (monoMap F hF).Full where
  map_surjective {X Y} g := by
    classical
    -- A faithful functor reflects monomorphisms.
    haveI : F.ReflectsMonomorphisms := inferInstance
    -- `g` lives in the mono-wide category, hence its underlying morphism is mono.
    haveI : Mono g.1 := g.2
    -- Define the preimage of a mono-arrow, and show it's mono by reflection.
    have hEq : F.map (F.preimage g.1) = g.1 := F.map_preimage g.1
    have hmono : Mono (F.map (F.preimage g.1)) := by rw [hEq]; infer_instance
    haveI hmono' : Mono (F.preimage g.1) := F.mono_of_mono_map hmono
    refine ⟨⟨F.preimage g.1, hmono'⟩, ?_⟩
    apply Subtype.ext
    exact F.map_preimage g.1

instance monoMap_essSurj (F : C ⥤ D) (hF : PreservesMonos F) [F.EssSurj] :
    (monoMap F hF).EssSurj where
  mem_essImage Y := by
    classical
    -- Use the chosen preimage of `Y.obj` under `F`, then lift the resulting iso to `MonoWide`.
    let preimg : C := F.objPreimage Y.obj
    let i0 : F.obj preimg ≅ Y.obj := F.objObjPreimageIso Y.obj
    haveI : Mono i0.hom := inferInstance
    haveI : Mono i0.inv := inferInstance
    refine ⟨(⟨preimg⟩ : MonoWide C), ⟨?_⟩⟩
    refine
      { hom := ⟨i0.hom, ‹Mono i0.hom›⟩
        inv := ⟨i0.inv, ‹Mono i0.inv›⟩
        hom_inv_id := by apply Subtype.ext; simp
        inv_hom_id := by apply Subtype.ext; simp }

/-!
## If `F` is an equivalence, then `monoMap F hF` is an equivalence (hence final)
-/

instance monoMap_isEquivalence (F : C ⥤ D) (hF : PreservesMonos F) [F.IsEquivalence] :
    (monoMap F hF).IsEquivalence where

instance monoMap_final_of_isEquivalence (F : C ⥤ D) (hF : PreservesMonos F) [F.IsEquivalence] :
    Functor.Final (monoMap F hF) :=
  -- An equivalence is a right adjoint, and right adjoints are final.
  inferInstance

/-!
## As a consequence, equivalences preserve the local state classifier `Ξ`

This is the "topos-equivalence example": if `f*` is an equivalence of categories, then the
finality hypothesis in `mapΞIso` is automatic.
-/

noncomputable def mapΞIso_of_functor_isEquivalence (F : C ⥤ D)
    [F.IsEquivalence]
    [HasColimit (monoInclusion C)]
    [HasColimit (monoInclusion D)] :
    F.obj (Ξ C) ≅ Ξ D := by
  -- Use the ready-made lemma in `LocalStateClassifierFull`.
  -- All required instances follow from `F.IsEquivalence`.
  haveI : F.IsLeftAdjoint := inferInstance
  haveI : F.PreservesMonomorphisms := inferInstance
  haveI : Functor.Final (monoMap F (of_typeclass F)) := inferInstance
  exact PreservesMonos.mapΞIso_of_isLeftAdjoint' (F := F)

/-- Both directions of an equivalence preserve `Ξ` (forward direction). -/
noncomputable def mapΞIso_of_equivalence (e : C ≌ D)
    [HasColimit (monoInclusion C)]
    [HasColimit (monoInclusion D)] :
    e.functor.obj (Ξ C) ≅ Ξ D :=
  mapΞIso_of_functor_isEquivalence (F := e.functor)

/-- Both directions of an equivalence preserve `Ξ` (inverse direction). -/
noncomputable def mapΞIso_of_equivalence_inverse (e : C ≌ D)
    [HasColimit (monoInclusion C)]
    [HasColimit (monoInclusion D)] :
    e.inverse.obj (Ξ D) ≅ Ξ C :=
  mapΞIso_of_functor_isEquivalence (F := e.inverse)

end LocalStateClassifier.PreservesMonos

/-!
## Back to the "geometric inverse image" specialization

In `LocalStateClassifierSpecialize2`, the only nontrivial hypothesis left to check for a concrete
`f* : F ⥤ E` was the finality condition on the induced mono-map.

If `f*` is an equivalence of categories (as happens for an equivalence of topoi), then this
finality condition is automatic.
-/

namespace LocalStateClassifier.IsGeometricInverseImage

universe u₃ v₃ u₄ v₄

variable {F : Type u₃} [Category.{v₃} F]
variable {E : Type u₄} [Category.{v₄} E]

instance isGeometricInverseImage_of_isEquivalence (fstar : F ⥤ E) [fstar.IsEquivalence] :
    IsGeometricInverseImage fstar :=
  { isLeftAdjoint := inferInstance
    preservesMonomorphisms := inferInstance }

noncomputable def mapΞIso_of_isEquivalence (fstar : F ⥤ E)
    [fstar.IsEquivalence]
    [HasColimit (monoInclusion F)]
    [HasColimit (monoInclusion E)] :
    fstar.obj (Ξ F) ≅ Ξ E := by
  -- `f*` is geometric (left adjoint + preserves monos) and its induced mono-map is final.
  haveI : IsGeometricInverseImage fstar := inferInstance
  haveI : Functor.Final (PreservesMonos.monoMap fstar (PreservesMonos.of_typeclass fstar)) :=
    inferInstance
  exact mapΞIso (fstar := fstar)

noncomputable def mapΞIso_of_equivalence (e : F ≌ E)
    [HasColimit (monoInclusion F)]
    [HasColimit (monoInclusion E)] :
    e.functor.obj (Ξ F) ≅ Ξ E :=
  mapΞIso_of_isEquivalence (fstar := e.functor)

noncomputable def mapΞIso_of_equivalence_inverse (e : F ≌ E)
    [HasColimit (monoInclusion F)]
    [HasColimit (monoInclusion E)] :
    e.inverse.obj (Ξ E) ≅ Ξ F :=
  mapΞIso_of_isEquivalence (fstar := e.inverse)

end LocalStateClassifier.IsGeometricInverseImage

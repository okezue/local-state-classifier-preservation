import LocalStateClassifierFull

/-!
# Specialization: “geometric inverse-image functors” preserve `Ξ` under finality

This file is meant as a lightweight bridge from the *purely categorical* theorem
`LocalStateClassifier.PreservesMonos.mapΞIso_of_isLeftAdjoint'` to the topos-theoretic slogan

> If `f*` is the inverse-image functor of a geometric morphism and it is final on monos,
> then `f*` preserves the local state classifier.

Mathlib does not currently provide a single bundled definition of Grothendieck topos / geometric
morphism that exposes exactly the interface we need, so we introduce a *minimal* class
`IsGeometricInverseImage`:

* `f*` is a left adjoint (hence preserves all colimits), and
* `f*` preserves monomorphisms.

Then the specialization is one line: it is exactly `mapΞIso_of_isLeftAdjoint'`.

The *only remaining hypothesis* is the interesting one: finality of the induced functor on
mono-wide subcategories.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace LocalStateClassifier

/-- Minimal interface for an “inverse image” functor of a geometric morphism. -/
class IsGeometricInverseImage
    {F : Type u₁} [Category.{v₁} F]
    {E : Type u₂} [Category.{v₂} E]
    (fstar : F ⥤ E) : Prop where
  /-- `f*` is a left adjoint. -/
  isLeftAdjoint : Functor.IsLeftAdjoint fstar
  /-- `f*` preserves monomorphisms. -/
  preservesMonomorphisms : fstar.PreservesMonomorphisms

attribute [instance] IsGeometricInverseImage.isLeftAdjoint
attribute [instance] IsGeometricInverseImage.preservesMonomorphisms

namespace IsGeometricInverseImage

variable {F : Type u₁} [Category.{v₁} F]
variable {E : Type u₂} [Category.{v₂} E]

/--
**Specialization of the main theorem.**

If `f*` is geometric (in the minimal sense above) and its induced map on the
mono-wide subcategories is final, then `f*` preserves the local state classifier.
-/
noncomputable def mapΞIso
    (fstar : F ⥤ E) [IsGeometricInverseImage (fstar := fstar)]
    [HasColimit (monoInclusion F)] [HasColimit (monoInclusion E)]
    [Functor.Final (PreservesMonos.monoMap fstar (PreservesMonos.of_typeclass fstar))] :
    fstar.obj (Ξ F) ≅ Ξ E := by
  simpa using PreservesMonos.mapΞIso_of_isLeftAdjoint' (F := fstar)

end IsGeometricInverseImage

end LocalStateClassifier

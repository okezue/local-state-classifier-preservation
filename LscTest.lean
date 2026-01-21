import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Preserves.Limits

open CategoryTheory
open CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

namespace LocalStateClassifier

/--
A cofinal presentation of a diagram `D : J ⥤ C` consists of:
* a "small" index category `I`,
* a functor `ι : I ⥤ J` which is `Final` (a.k.a. cofinal),
so that colimits of `D` can be computed by the restricted diagram `ι ⋙ D`.
-/
structure CofinalPresentation (C : Type u₁) [Category.{v₁} C] where
  (J : Type u₂)
  [instJ : Category.{v₂} J]
  (I : Type u₃)
  [instI : Category.{v₃} I]
  (ι : I ⥤ J)
  [final_ι : ι.Final]
  (D : J ⥤ C)

attribute [instance] CofinalPresentation.instJ
attribute [instance] CofinalPresentation.instI
attribute [instance] CofinalPresentation.final_ι

namespace CofinalPresentation

variable {C : Type u₁} [Category.{v₁} C]
variable (P : CofinalPresentation C)

/-- The restricted ("small") diagram `I ⥤ C`. -/
abbrev small : P.I ⥤ C := P.ι ⋙ P.D

/--
If `ι : I ⥤ J` is final, the canonical isomorphism
`colimit (ι ⋙ D) ≅ colimit D`.
-/
noncomputable def colimitIso [HasColimit P.D] :
    colimit (P.small) ≅ colimit P.D := by
  classical
  exact Functor.Final.colimitIso P.ι P.D

/--
For `ι : I ⥤ J` final, a functor `T : C ⥤ D'` preserves `colimit D`
iff it preserves `colimit (ι ⋙ D)`.

This is the formal "you only need to check preservation on the cofinal subdiagram" lemma.
-/
theorem preservesColimit_iff
    {D' : Type u₄} [Category.{v₄} D'] (T : C ⥤ D') :
    PreservesColimit P.D T ↔ PreservesColimit (P.small) T := by
  constructor
  · intro h
    -- If `T` preserves the big colimit, it preserves the cofinal restriction.
    letI : PreservesColimit P.D T := h
    infer_instance
  · intro h
    -- If `T` preserves the cofinal restriction, it preserves the big colimit.
    letI : PreservesColimit (P.small) T := h
    exact (Functor.Final.preservesColimit_of_comp (F := P.ι) (G := P.D) (H := T))

/--
If `T` preserves the colimit of the *restricted* diagram `ι ⋙ D`,
then `T` preserves the colimit of `D`, hence we get the standard comparison isomorphism
`T.obj (colimit D) ≅ colimit (D ⋙ T)`.

This is the exact "preserves the (local state classifier) colimit" conclusion once you
encode your LSC as a colimit of `D`.
-/
noncomputable def mapColimitIso
    {D' : Type u₄} [Category.{v₄} D'] (T : C ⥤ D')
    [HasColimit P.D] [HasColimit (P.D ⋙ T)] [PreservesColimit (P.small) T] :
    T.obj (colimit P.D) ≅ colimit (P.D ⋙ T) := by
  classical
  -- Upgrade preservation from the cofinal restriction to the original diagram:
  haveI : PreservesColimit P.D T :=
    (Functor.Final.preservesColimit_of_comp (F := P.ι) (G := P.D) (H := T))
  -- Use the canonical comparison isomorphism for a colimit-preserving functor:
  exact preservesColimitIso T P.D

end CofinalPresentation
end LocalStateClassifier

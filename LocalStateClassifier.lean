-- LocalStateClassifier.lean
--
-- Lean formalization of the "local state classifier" (LSC) as the colimit of all monomorphisms,
-- together with the standard reduction of that (potentially large) colimit along a final functor.
--
-- This is a faithful formal skeleton of the key categorical steps used in Hora's work on LSCs.

import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

open CategoryTheory
open CategoryTheory.Limits

universe v u v₁ u₁ v₂ u₂

namespace LocalStateClassifier

/-!
# 1. The indexing category `C_mono` and the LSC diagram

For a category `C`, let `C_mono` denote the wide subcategory of `C` whose morphisms are
*monomorphisms*.

The *local state classifier* `Ξ` (when it exists) is defined as the colimit of the inclusion
diagram `C_mono ⥤ C`.

This matches Hora's definition: the LSC `Ξ` is the colimit of *all* monomorphisms.
-/

section

variable (C : Type u) [Category.{v} C]

/-- The wide subcategory of `C` consisting of monomorphisms. -/
abbrev C_mono : Type u :=
  WideSubcategory (MorphismProperty.monomorphisms C)

/-- The inclusion functor `C_mono ⥤ C`. -/
abbrev monoInclusion : C_mono C ⥤ C :=
  wideSubcategoryInclusion (MorphismProperty.monomorphisms C)

/-- The diagram whose colimit is the local state classifier. -/
abbrev lscDiagram : C_mono C ⥤ C :=
  monoInclusion C

/-- The local state classifier object `Ξ`, defined as `colimit (lscDiagram C)`.

This is only defined under `[HasColimit (lscDiagram C)]`. -/
noncomputable abbrev LSC [HasColimit (lscDiagram C)] : C :=
  colimit (lscDiagram C)

/-- The structure maps `ξ_X : X ⟶ Ξ` for the LSC cocone. -/
noncomputable abbrev ξ [HasColimit (lscDiagram C)] (X : C_mono C) : X.obj ⟶ LSC C :=
  colimit.ι (lscDiagram C) X

/-- Naturality of the LSC cocone: for any mono `f : X ⟶ Y` (i.e. a morphism in `C_mono`),
we have `f ≫ ξ_Y = ξ_X`.

This is exactly the "local determination" property used in Hora's papers. -/
@[simp, reassoc]
theorem ξ_naturality [HasColimit (lscDiagram C)] {X Y : C_mono C} (f : X ⟶ Y) :
    (monoInclusion C).map f ≫ ξ C Y = ξ C X :=
  colimit.w (lscDiagram C) f

/-- A "local state family into `A`": maps `p_X : X ⟶ A` compatible with all monomorphisms.

This is an explicit spelling of a cocone over `lscDiagram C` with cone-point `A`. -/
def LocalStateFamily (A : C) : Type (max u v) :=
  { p : (X : C_mono C) → X.obj ⟶ A //
      ∀ {X Y : C_mono C} (f : X ⟶ Y), (monoInclusion C).map f ≫ p Y = p X }

end

/-!
# 2. Reducing the (potentially large) LSC colimit along a final functor

Hora's key "size reduction" move is:

*If there is a small subcategory / diagram of monomorphisms which is final (cofinal) in `C_mono`,
then the LSC colimit over `C_mono` is isomorphic to a colimit over that smaller indexing category.*

In mathlib this is exactly the `Functor.Final` colimit theorem.
-/

section

variable {C : Type u} [Category.{v} C]

variable {S : Type u₁} [Category.{v₁} S]
variable (ι : S ⥤ C_mono C)

/-- The restricted diagram `S ⥤ C` obtained from `ι : S ⥤ C_mono`.
Think of `S` as a "small mono-dense generating" indexing category. -/
abbrev smallDiagram : S ⥤ C :=
  ι ⋙ lscDiagram C

/-- If `ι` is final and the small diagram has a colimit, then the big LSC diagram has a colimit.

This is the existence direction needed when `C` only has "small" colimits. -/
theorem hasColimit_lsc_of_hasColimit_small [ι.Final] [HasColimit (smallDiagram (C := C) ι)] :
    HasColimit (lscDiagram C) :=
  Functor.Final.hasColimit_of_comp (F := ι) (G := lscDiagram C)

/-- The canonical isomorphism `colim (ι ⋙ lscDiagram) ≅ colim (lscDiagram)` for a final `ι`.

Specialized, this is the statement that a "small mono-dense" presentation computes the LSC. -/
noncomputable def lscIso_of_final
    [ι.Final] [hSmall : HasColimit (smallDiagram (C := C) ι)]
    [hBig : HasColimit (lscDiagram C)] :
    colimit (smallDiagram (C := C) ι) ≅ LSC C :=
  Functor.Final.colimitIso ι (lscDiagram C)

/-- Preservation reduction (the "engine"):
A functor preserves the big LSC colimit iff it preserves the small, final restriction. -/
theorem preservesLSC_iff
    {D : Type u₂} [Category.{v₂} D]
    (T : C ⥤ D)
    [ι.Final] :
    PreservesColimit (lscDiagram C) T ↔ PreservesColimit (smallDiagram (C := C) ι) T := by
  constructor
  · intro h
    letI : PreservesColimit (lscDiagram C) T := h
    infer_instance
  · intro h
    letI : PreservesColimit (smallDiagram (C := C) ι) T := h
    exact Functor.Final.preservesColimit_of_comp (F := ι) (G := lscDiagram C) (H := T)

/-- If `T` preserves the (small) LSC colimit, we get the standard comparison isomorphism
`T(Ξ) ≅ colim (lscDiagram ⋙ T)`.

This is the form you typically use to *transport* the LSC across a functor. -/
noncomputable def mapLSC_iso
    {D : Type u₂} [Category.{v₂} D]
    (T : C ⥤ D)
    [ι.Final]
    [HasColimit (smallDiagram (C := C) ι)]
    [HasColimit (lscDiagram C)]
    [HasColimit ((lscDiagram C) ⋙ T)]
    [PreservesColimit (smallDiagram (C := C) ι) T] :
    T.obj (LSC C) ≅ colimit ((lscDiagram C) ⋙ T) := by
  haveI : PreservesColimit (lscDiagram C) T :=
    (preservesLSC_iff (C := C) (ι := ι) T).2 (by infer_instance)
  exact preservesColimitIso T (lscDiagram C)

end

/-!
# 3. A convenient corollary: left adjoints preserve the LSC when it has a small final presentation

In topos theory, inverse image functors of geometric morphisms are left adjoints, so they
preserve *small* colimits.

Hora's reduction says: if `Ξ` can be computed as a small colimit, then such functors preserve `Ξ`.

The lemma below packages that in Lean.
-/

section

variable {C : Type u} [Category.{v} C]
variable {D : Type u₂} [Category.{v₂} D]

variable {S : Type u₁} [Category.{v₁} S]
variable (ι : S ⥤ C_mono C)

/-- If `ι` is final and the small diagram exists, then any left adjoint `T` preserves the LSC
colimit.

(We phrase "left adjoint" via an explicit adjunction `T ⊣ R`.) -/
theorem leftAdjoint_preserves_LSC
    (T : C ⥤ D) (R : D ⥤ C) (adj : T ⊣ R)
    [ι.Final]
    [HasColimit (smallDiagram (C := C) ι)] :
    PreservesColimit (lscDiagram C) T := by
  haveI : PreservesColimitsOfSize.{v₁, u₁} T :=
    Adjunction.leftAdjoint_preservesColimits (adj := adj)
  have hsmall : PreservesColimit (smallDiagram (C := C) ι) T := inferInstance
  exact (preservesLSC_iff (C := C) (ι := ι) T).2 hsmall

end

end LocalStateClassifier

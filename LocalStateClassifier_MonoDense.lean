import LocalStateClassifier
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# Mono-density and Local State Classifiers

This file continues the development in `LocalStateClassifier.lean` by formalizing
Hora's *mono-density* condition (Appendix B, Def. B.1) and the corresponding
existence theorem for local state classifiers (Appendix B, Prop. B.2).

## References

* Ryuya Hora, "Internal parameterization of hyperconnected quotients",
  arXiv:2302.06851, Appendix B.

## Main definitions

The key idea is to phrase mono-density as the statement that the canonical square

```
  S_mono  ⟶  C
    |          |
    v          v
  C_mono  ⟶  C
```

is a *pointwise* left Kan extension. In mathlib, this is expressed using
`CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension`.

From this we derive a Lean version of Hora's existence theorem:
if the restricted diagram `S_mono ⥤ C` has a colimit, then so does the full
mono-diagram `C_mono ⥤ C`, and the resulting colimit object is (a choice of)
local state classifier.
-/

namespace LocalStateClassifier

open CategoryTheory
open CategoryTheory.Limits

universe u v u₁ v₁

section MonoDense

variable {C : Type u} [Category.{v} C]
variable {S : Type u₁} [Category.{v₁} S]

/-- The restricted LSC diagram `S ⥤ C` obtained from a functor `ι : S ⥤ C_mono C`. -/
abbrev sigmaDiagram (ι : S ⥤ C_mono C) : S ⥤ C :=
  ι ⋙ lscDiagram C

/-- The canonical `LeftExtension` witnessing that `lscDiagram C` extends
`sigmaDiagram ι` along `ι`.

Concretely, the right functor is `lscDiagram C`, and the comparison natural
transformation is the identity (since `sigmaDiagram ι = ι ⋙ lscDiagram C`). -/
abbrev monoDenseExt (ι : S ⥤ C_mono C) :
    ι.LeftExtension (sigmaDiagram (C := C) ι) :=
  Functor.LeftExtension.mk (lscDiagram C)
    (NatTrans.id (sigmaDiagram (C := C) ι))

/-- **Hora's mono-density** condition (Appendix B, Def. B.1).

A functor `ι : S ⥤ C_mono C` is *mono-dense* if the canonical square
`S ⥤ C` / `C_mono ⥤ C` is a *pointwise left Kan extension*.

In mathlib terms, this means the canonical `LeftExtension` `monoDenseExt ι`
(i.e. right functor `lscDiagram C` with identity comparison cell) is pointwise. -/
abbrev MonoDense (ι : S ⥤ C_mono C) :=
  (monoDenseExt (C := C) ι).IsPointwiseLeftKanExtension

/-- A proposition-only version of mono-density: we assert existence of the pointwise
colimit data rather than fixing a specific choice.

This matches the usual mathematical reading of Hora's definition. -/
def IsMonoDense (ι : S ⥤ C_mono C) : Prop :=
  ∀ X : C_mono C, Nonempty (IsColimit ((monoDenseExt (C := C) ι).coconeAt X))

/-- Unfolding mono-density: it says that for every `X : C_mono C`,
`(monoDenseExt ι).coconeAt X` is a colimit cocone.

This matches the “comma category colimit” formulation in Hora (Appendix B, Def. B.1). -/
lemma isMonoDense_iff (ι : S ⥤ C_mono C) :
    IsMonoDense (C := C) ι ↔
      ∀ X : C_mono C, Nonempty (IsColimit ((monoDenseExt (C := C) ι).coconeAt X)) := by
  rfl

/-- Choose pointwise Kan extension data from the proposition-only hypothesis `IsMonoDense`.

This is the small amount of choice needed to pass from Hora's *existential* definition
to the *data-carrying* notion used by `Functor.LeftExtension.IsPointwiseLeftKanExtension`.
-/
noncomputable
def monoDense_of_isMonoDense (ι : S ⥤ C_mono C)
    (hι : IsMonoDense (C := C) ι) :
    MonoDense (C := C) ι := by
  classical
  -- Unfold `MonoDense`: it is a dependent function returning `IsColimit` data.
  intro X
  exact Classical.choice (hι X)

/-- Construct a `ColimitCocone` for the full diagram `lscDiagram C` from:

* a colimit of the restricted (small) diagram `sigmaDiagram ι`, and
* a proof that `ι` is mono-dense.

This is a direct formalization of Hora's existence theorem (Appendix B, Prop. B.2). -/
noncomputable
def lscColimitCoconeOfMonoDense
    (ι : S ⥤ C_mono C) [HasColimit (sigmaDiagram (C := C) ι)]
    (hι : MonoDense (C := C) ι) :
    ColimitCocone (lscDiagram C) := by
  classical
  -- Abbreviate the small diagram and the canonical left extension.
  let F : S ⥤ C := sigmaDiagram (C := C) ι
  let E : ι.LeftExtension F := monoDenseExt (C := C) ι
  -- Pointwise left Kan extension ⇒ (ordinary) left Kan extension, installed as instance.
  haveI : (lscDiagram C).IsLeftKanExtension E.hom := hι.isLeftKanExtension
  -- Start from the chosen colimit cocone over the small diagram.
  let cF : Cocone F := colimit.cocone F
  have hcF : IsColimit cF := colimit.isColimit F
  -- Transport the cocone along the Kan extension.
  let cG : Cocone (lscDiagram C) := (lscDiagram C).coconeOfIsLeftKanExtension E.hom cF
  have hcG : IsColimit cG := (lscDiagram C).isColimitCoconeOfIsLeftKanExtension E.hom hcF
  exact ⟨cG, hcG⟩

/-- If `ι : S ⥤ C_mono C` is mono-dense and the restricted diagram has a colimit,
then the full mono-diagram `lscDiagram C` has a colimit.

This gives a *chosen* LSC colimit in the sense of the original file `LocalStateClassifier.lean`. -/
theorem hasColimit_lsc_of_monoDense
    (ι : S ⥤ C_mono C) [HasColimit (sigmaDiagram (C := C) ι)]
    (hι : MonoDense (C := C) ι) :
    HasColimit (lscDiagram C) := by
  classical
  refine ⟨⟨(lscColimitCoconeOfMonoDense (C := C) ι hι).cocone,
          (lscColimitCoconeOfMonoDense (C := C) ι hι).isColimit⟩⟩

/-- Convenience wrapper: the same existence theorem, but assuming only the proposition
`IsMonoDense` (and using choice internally to pick the `IsColimit` data). -/
theorem hasColimit_lsc_of_isMonoDense
    (ι : S ⥤ C_mono C) [HasColimit (sigmaDiagram (C := C) ι)]
    (hι : IsMonoDense (C := C) ι) :
    HasColimit (lscDiagram C) := by
  classical
  exact hasColimit_lsc_of_monoDense (C := C) ι (monoDense_of_isMonoDense (C := C) ι hι)

/-- The canonical isomorphism between the colimit of the restricted diagram
and the (chosen) colimit of the full mono-diagram, under mono-density.

In other words: **the local state classifier can be computed as a small colimit
once a mono-dense small presentation is chosen** (Hora, Appendix B). -/
noncomputable
def lscIso_of_monoDense
    (ι : S ⥤ C_mono C) [hSmall : HasColimit (sigmaDiagram (C := C) ι)]
    (hι : MonoDense (C := C) ι)
    [hBig : HasColimit (lscDiagram C)] :
    colimit (sigmaDiagram (C := C) ι) ≅ colimit (lscDiagram C) := by
  classical
  let E := monoDenseExt (C := C) ι
  haveI hLan : (lscDiagram C).IsLeftKanExtension E.hom := hι.isLeftKanExtension
  -- Transport the small cocone to a colimit cocone over lscDiagram C.
  -- By coconeOfIsLeftKanExtension, cBig.pt = colimit (sigmaDiagram ι).
  let cSmall := colimit.cocone (sigmaDiagram (C := C) ι)
  let hcSmall := colimit.isColimit (sigmaDiagram (C := C) ι)
  let cBig := (lscDiagram C).coconeOfIsLeftKanExtension E.hom cSmall
  let hcBig := (lscDiagram C).isColimitCoconeOfIsLeftKanExtension E.hom hcSmall
  -- cBig.pt = cSmall.pt = colimit (sigmaDiagram ι), so the isomorphism from
  -- uniqueness of colimits is exactly what we need.
  exact IsColimit.coconePointUniqueUpToIso hcBig (colimit.isColimit (lscDiagram C))

/-- Variant of `lscIso_of_monoDense` that only assumes the proposition `IsMonoDense`.

This mirrors the informal mathematics: one typically proves mono-density existentially,
and then picks a choice to obtain the comparison isomorphism. -/
noncomputable
def lscIso_of_isMonoDense
    (ι : S ⥤ C_mono C) [HasColimit (sigmaDiagram (C := C) ι)]
    (hι : IsMonoDense (C := C) ι)
    [HasColimit (lscDiagram C)] :
    colimit (sigmaDiagram (C := C) ι) ≅ colimit (lscDiagram C) := by
  classical
  exact lscIso_of_monoDense (C := C) ι (monoDense_of_isMonoDense (C := C) ι hι)

end MonoDense

end LocalStateClassifier

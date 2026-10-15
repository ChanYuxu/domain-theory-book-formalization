import Practice.DomainTheory.Chapter08.Section82_83

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Sections 8.4--8.5

Source-faithful interfaces for the axiomatic and synthetic domain-theory
programmes.  These sections are research surveys, not theorem/proof sections;
the declarations therefore expose the mathematical obligations without
asserting that the chapter proves a complete axiom system.
-/

universe u v

namespace AbramskyJung
namespace Chapter8

open CategoryTheory

/-- A preorder and dcpo structure on every hom-set of a category.  This is the
minimum local data behind the source's phrase "enriched over a suitable
subcategory of DCPO"; compatibility of composition is kept explicit. -/
structure DcpoEnrichment (C : Type u) [Category.{v} C] where
  homPreorder : ∀ X Y : C, Preorder (X ⟶ Y)
  homDcpo :
    ∀ X Y : C, @Chapter2.IsDcpoOrder (X ⟶ Y) (homPreorder X Y)
  compositionMonotone :
    ∀ {X Y Z : C} (f f' : X ⟶ Y) (g g' : Y ⟶ Z),
      @LE.le (X ⟶ Y) (homPreorder X Y).toLE f f' →
      @LE.le (Y ⟶ Z) (homPreorder Y Z).toLE g g' →
      @LE.le (X ⟶ Z) (homPreorder X Z).toLE (f ≫ g) (f' ≫ g')

/-- Canonical solutions of recursive domain equations at the level explicitly
needed by the survey: every endofunctor receives a chosen fixed-point object
and an isomorphism.  Freyd's full notion of algebraic compactness additionally
uses initial-algebra/final-coalgebra universal properties and is not silently
collapsed to this record. -/
structure CanonicalRecursiveSolutions (C : Type u) [Category.{v} C] where
  solution : (C ⥤ C) → C
  fixedPointIso : ∀ F : C ⥤ C, F.obj (solution F) ≅ solution F

/-- Section 8.4, the obligations singled out for axiomatic domain theory.
This is a programme interface, not a declaration that these fields constitute
Freyd's complete axiomatization. -/
structure AxiomaticDomainTheory (C : Type u) [Category.{v} C] where
  enrichment : DcpoEnrichment C
  recursiveSolutions : CanonicalRecursiveSolutions C
  fixpointPrinciple : Prop
  semanticMetalanguage : Prop
  representationProblem : Prop
  citations : List SurveyCitation

/-- The non-functional morphism models named in Section 8.4. -/
def axiomaticDomainTheoryModels : List SurveyCitation :=
  [ { key := "Cur93", role := "sequential algorithms" },
    { key := "AJ94b", role := "information flows" },
    { key := "AJ94a", role := "game-theoretic strategies" },
    { key := "Abr94", role := "concurrent processes" },
    { key := "Fre91", role := "algebraically compact categories" },
    { key := "Fre92", role := "algebraic compactness and recursive equations" },
    { key := "CP92", role := "FIX-categories" } ]

/-- Section 8.5, the synthetic-domain-theory research programme.  The Boolean
fields record the three kinds of structure that the source proposes absorbing
into a constructive universe; they do not assert a theorem about an arbitrary
topos. -/
structure SyntheticDomainTheory where
  ambientUniverse : String
  absorbsConvergence : Bool
  absorbsApproximation : Bool
  absorbsComputability : Bool
  slogan : String
  citations : List SurveyCitation
deriving DecidableEq, Repr

/-- The programme and references exactly listed in Section 8.5. -/
def syntheticDomainTheoryProgramme : SyntheticDomainTheory :=
  { ambientUniverse := "a suitable constructive set theory or topos"
    absorbsConvergence := true
    absorbsApproximation := true
    absorbsComputability := true
    slogan := "Domains are Sets"
    citations :=
      [ { key := "Koc81", role := "synthetic differential geometry analogy" },
        { key := "Ros86", role := "first substantial construction" },
        { key := "Pho91", role := "synthetic domain theory" },
        { key := "FMRS90", role := "synthetic domain-theoretic axioms" },
        { key := "Hyl91", role := "axioms for synthetic domain theory" },
        { key := "Tay91", role := "axioms for synthetic domain theory" } ] }

end Chapter8
end AbramskyJung

import Practice.DomainTheory.Chapter07.NumberedItems

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 8.1

Effectively given domains, universal domains, polymorphism, and information
systems.  The chapter is expository, so declarations below distinguish exact
source definitions from raw interfaces whose complete axiom systems are only
referenced in the literature.
-/

universe u v w

namespace AbramskyJung
namespace Chapter8

open Chapter4

/-- A citation attached to a survey interface or reported result. -/
structure SurveyCitation where
  key : String
  role : String
deriving DecidableEq, Repr

/-- Section 8.1.1, effectively given domains.  The source uses a numbered
concrete basis and requires the way-below relation on basis indices to be
recursive.  A Boolean decision procedure is the executable Lean spelling of
that requirement. -/
structure EffectiveDomain where
  domain : OrderedDomain.{u}
  dcpo : Chapter2.IsDcpoOrder domain.carrier
  basis : Set domain.carrier
  basis_is_basis : Chapter2.IsBasisRaw basis
  numbering : Nat -> domain.carrier
  numbering_mem : forall n : Nat, numbering n ∈ basis
  numbering_surjective : forall b : domain.carrier, b ∈ basis -> exists n : Nat, numbering n = b
  recursiveApprox : Nat -> Nat -> Bool
  recursiveApprox_spec :
    forall m n : Nat,
      recursiveApprox m n = true <->
        Chapter2.WayBelow (numbering m) (numbering n)

namespace EffectiveDomain

/-- A numbered basis is countable. -/
theorem basis_countable (D : EffectiveDomain.{u}) : D.basis.Countable := by
  refine (Set.countable_range D.numbering).mono ?_
  intro b hb
  rcases D.numbering_surjective b hb with ⟨n, rfl⟩
  exact ⟨n, rfl⟩

/-- The source definition indeed gives an omega-continuous dcpo. -/
theorem isOmegaContinuousDcpo (D : EffectiveDomain.{u}) :
    Chapter2.IsOmegaContinuousDcpo D.domain.carrier := by
  refine ⟨D.dcpo, D.basis, D.basis_countable, D.basis_is_basis⟩

end EffectiveDomain

/-- Section 8.1.1, effective continuous maps.  The enumerable relation records
exactly the basis pairs `(m,n)` for which the target approximant is way below
the image of the source approximant. -/
structure EffectiveContinuousMap (D : EffectiveDomain.{u}) (E : EffectiveDomain.{v}) where
  toFun : D.domain.carrier -> E.domain.carrier
  continuous : Chapter3.ScottContinuous toFun
  enumeration : Nat -> Nat × Nat
  enumerates :
    forall m n : Nat,
      (exists k : Nat, enumeration k = (m, n)) <->
        Chapter2.WayBelow (E.numbering n) (toFun (D.numbering m))

namespace EffectiveContinuousMap

instance (D : EffectiveDomain.{u}) (E : EffectiveDomain.{v}) :
    CoeFun (EffectiveContinuousMap D E) (fun _ => D.domain.carrier -> E.domain.carrier) :=
  ⟨toFun⟩

end EffectiveContinuousMap

/-- Section 8.1.2, universal domains.  Membership of the universal object and
cartesian-closed object-class data are explicit; each represented object comes
with the embedding-projection pair used by the textbook. -/
structure UniversalDomain (C : DomainClass.{u}) where
  cartesianClosed : DomainClass.CartesianClosed C
  universal : OrderedDomain.{u}
  universal_mem : C.Obj universal
  embeds :
    forall D : OrderedDomain.{u},
      C.Obj D -> Chapter3.EPPair D.carrier universal.carrier

namespace UniversalDomain

/-- The idempotent `e_D = e o p` representing an object inside a universal
domain. -/
def representedIdempotent {C : DomainClass.{u}} (U : UniversalDomain C)
    (D : OrderedDomain.{u}) (hD : C.Obj D) : U.universal.carrier -> U.universal.carrier :=
  fun x => (U.embeds D hD).e ((U.embeds D hD).p x)

theorem representedIdempotent_idempotent {C : DomainClass.{u}}
    (U : UniversalDomain C) (D : OrderedDomain.{u}) (hD : C.Obj D)
    (x : U.universal.carrier) :
    U.representedIdempotent D hD (U.representedIdempotent D hD x) =
      U.representedIdempotent D hD x := by
  simp only [representedIdempotent, (U.embeds D hD).retract]

theorem representedIdempotent_below {C : DomainClass.{u}}
    (U : UniversalDomain C) (D : OrderedDomain.{u}) (hD : C.Obj D)
    (x : U.universal.carrier) : U.representedIdempotent D hD x <= x :=
  (U.embeds D hD).below x

end UniversalDomain

/-- Section 8.1.2, the additional coding data behind the displayed continuous
operations `fun, prod : U^2 -> U`.  The laws state that these operations send
codes to the codes of function-space and product objects.  Existence of this
extra coding is not asserted merely from `UniversalDomain`. -/
structure UniversalDomainCoding {C : DomainClass.{u}} (U : UniversalDomain C) where
  code : forall D : OrderedDomain.{u}, C.Obj D -> U.universal.carrier
  functionCode :
    OrderedDomain.ContFunCarrier
      (OrderedDomain.prod U.universal U.universal) U.universal
  productCode :
    OrderedDomain.ContFunCarrier
      (OrderedDomain.prod U.universal U.universal) U.universal
  functionCode_apply :
    forall (D E : OrderedDomain.{u}) (hD : C.Obj D) (hE : C.Obj E),
      functionCode (code D hD, code E hE) =
        code (OrderedDomain.functionSpace D E)
          (U.cartesianClosed.exponentials hD hE)
  productCode_apply :
    forall (D E : OrderedDomain.{u}) (hD : C.Obj D) (hE : C.Obj E),
      productCode (code D hD, code E hE) =
        code (OrderedDomain.prod D E) (U.cartesianClosed.products hD hE)

namespace UniversalDomainCoding

/-- The subset of `U` consisting of object codes. -/
def IsTypeCode {C : DomainClass.{u}} {U : UniversalDomain C}
    (coding : UniversalDomainCoding U) (x : U.universal.carrier) : Prop :=
  exists D : OrderedDomain.{u}, exists hD : C.Obj D, x = coding.code D hD

/-- The source's subdomain `V` of codes, with its inherited order. -/
def typeCodesDomain {C : DomainClass.{u}} {U : UniversalDomain C}
    (coding : UniversalDomainCoding U) : OrderedDomain.{u} where
  carrier := {x : U.universal.carrier // coding.IsTypeCode x}
  preorder := inferInstance

/-- A universal domain admits a universal type when its object-code subdomain
is itself an object of the represented class. -/
def AdmitsUniversalType {C : DomainClass.{u}} {U : UniversalDomain C}
    (coding : UniversalDomainCoding U) : Prop :=
  C.Obj coding.typeCodesDomain

/-- The resulting code `u_V` for the type of all represented types. -/
def universalTypeCode {C : DomainClass.{u}} {U : UniversalDomain C}
    (coding : UniversalDomainCoding U) (h : coding.AdmitsUniversalType) :
    U.universal.carrier :=
  coding.code coding.typeCodesDomain h

end UniversalDomainCoding

/-- Outcomes reported in the universal-type literature survey.  These are
bibliographic data, not proof constants. -/
inductive UniversalTypeOutcome where
  | exists
  | doesNotExist
deriving DecidableEq, Repr

/-- A source-reported universal-type case study. -/
structure UniversalTypeCaseStudy where
  universalDomain : String
  representedClass : String
  outcome : UniversalTypeOutcome
  citations : List SurveyCitation
deriving DecidableEq, Repr

/-- The two `P(omega)` outcomes reported in Section 8.1.2. -/
def universalTypeCaseStudies : List UniversalTypeCaseStudy :=
  [ { universalDomain := "P(omega)"
      representedClass := "omega-continuous lattices represented by idempotents"
      outcome := .doesNotExist
      citations :=
        [ { key := "Ers75", role := "non-existence theorem" },
          { key := "HS77", role := "independent non-existence theorem" } ] },
    { universalDomain := "P(omega)"
      representedClass := "omega-algebraic lattices represented by closures"
      outcome := .exists
      citations :=
        [ { key := "Sco76", role := "reported Hancock-Martin-Lof result" } ] } ]

/-- Semantic approaches to polymorphism listed in Section 8.1.3. -/
inductive PolymorphismModelKind where
  | impredicativeFunctorial
  | idealBasedImplicit
  | partialEquivalenceRelation
deriving DecidableEq, Repr

/-- Section 8.1.3 is a literature map rather than a formal construction.  This
record keeps the interpreted type language together with the precise approach
and citations, without claiming a semantics not specified by the chapter. -/
structure PolymorphicSemantics where
  TypeExpr : Type u
  Context : Type v
  interpret : Context -> TypeExpr -> OrderedDomain.{w}
  approach : PolymorphismModelKind
  citations : List SurveyCitation

/-- Section 8.1.4 gives only the token/consistency/entailment signature of an
information system and refers elsewhere for the axioms.  No unprinted axioms
are invented here. -/
structure InformationSystem where
  Token : Type u
  consistent : Set Token -> Prop
  entails : Set Token -> Token -> Prop

/-- The uses of information systems explicitly listed in Section 8.1.4. -/
structure InformationSystemRole where
  representsAbstractBases : Bool
  supportsEffectivePresentation : Bool
  bilimitsByUnions : Bool
  domainEquationsByEquality : Bool
  citations : List SurveyCitation
deriving DecidableEq, Repr

def informationSystemSurveyRole : InformationSystemRole :=
  { representsAbstractBases := true
    supportsEffectivePresentation := true
    bilimitsByUnions := true
    domainEquationsByEquality := true
    citations :=
      [ { key := "Win88", role := "domain information systems" },
        { key := "Zha91", role := "logic of domains" },
        { key := "Cur93", role := "domain representations" },
        { key := "ES93", role := "general information-system theory" } ] }

/-- The section headings of Chapter 8 as Lean data. -/
inductive FurtherTopic where
  | effectivelyGivenDomains
  | universalDomains
  | polymorphism
  | informationSystems
  | stabilityAndSequentiality
  | predomainsAndPartialFunctions
  | computationalMonads
  | linearTypes
  | axiomaticDomainTheory
  | syntheticDomainTheory
deriving DecidableEq, Repr

end Chapter8
end AbramskyJung

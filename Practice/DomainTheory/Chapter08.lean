import Practice.DomainTheory.Chapter07

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 8

This chapter is a map of further directions.  The Lean file keeps these as
interfaces so later developments can attach concrete constructions and theorems.
-/

universe u v

namespace AbramskyJung
namespace Chapter8

open Chapter4

/-- Effectively given domains add codes for basic approximants. -/
structure EffectiveDomain where
  domain : OrderedDomain.{u}
  Code : Type v
  decode : Code → domain.carrier
  enumerable : Code → Nat

/-- A universal domain contains embeddings of all objects in a chosen class. -/
structure UniversalDomain (C : DomainClass.{u}) where
  universal : OrderedDomain.{u}
  embeds :
    ∀ D : OrderedDomain.{u},
      C.Obj D → Chapter3.EPPair D.carrier universal.carrier

/-- Information systems present domains by tokens and consistency/entailment. -/
structure InformationSystem where
  Token : Type u
  consistent : Set Token → Prop
  entails : Set Token → Token → Prop
  monotone_entails :
    ∀ A B : Set Token, A ⊆ B → consistent B →
      ∀ t : Token, entails A t → entails B t

/-- A domain-theoretic semantics interface for polymorphism. -/
structure PolymorphicSemantics where
  TypeExpr : Type u
  Context : Type v
  interpret : Context → TypeExpr → OrderedDomain.{v}

/-- Computational monads as one reformulation of partiality and effects. -/
structure ComputationalMonad where
  T : Type u → Type u
  pure : ∀ {α : Type u}, α → T α
  bind : ∀ {α β : Type u}, T α → (α → T β) → T β

/-- Linear type models distinguish reusable and single-use information. -/
structure LinearDomainModel where
  domain : OrderedDomain.{u}
  tensor : domain.carrier → domain.carrier → domain.carrier
  unit : domain.carrier

/-- Axiomatic domain theory abstracts the domain constructions required by
semantics into axioms over a semantic universe. -/
structure AxiomaticDomainTheory where
  semanticUniverse : Chapter1.SemanticUniverse.{u, v}
  hasFixpoints : Prop
  hasFunctionSpaces : Prop
  hasPowerdomains : Prop

/-- Synthetic domain theory internalizes domain-theoretic reasoning in an
ambient logic or topos. -/
structure SyntheticDomainTheory where
  Ambient : Type u
  dominance : Ambient → Prop
  fixedPointPrinciple : Prop

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

import Mathlib

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 1

This opening chapter records the motivating data described in the introduction:
least fixed points for recursive definitions, recursive domain equations, domains
as semantic universes, and continuity as the order-theoretic proxy for computable
approximation.

The chapter is intentionally light on theorem proving.  It provides named Lean
interfaces used by later chapters of this formalized book.
-/

universe u v

namespace AbramskyJung
namespace Chapter1

/-- A semantic reading of a recursive definition `x = f x`. -/
structure RecursiveDefinitionProblem (D : Type u) where
  step : D → D

/-- A solution of a recursive definition is a fixed point of its semantic step. -/
def RecursiveDefinitionProblem.Solution {D : Type u}
    (P : RecursiveDefinitionProblem D) (x : D) : Prop :=
  P.step x = x

/-- A least fixed point, when the carrier is ordered. -/
def RecursiveDefinitionProblem.LeastSolution {D : Type u} [Preorder D]
    (P : RecursiveDefinitionProblem D) (x : D) : Prop :=
  P.Solution x ∧ ∀ y : D, P.Solution y → x ≤ y

/-- A recursive domain equation asks for an object equivalent to a functorial
expression in that same object. -/
structure RecursiveDomainEquationProblem (Obj : Type u) where
  body : Obj → Obj

/-- A concrete solution of a recursive domain equation. -/
structure RecursiveDomainEquationProblem.Solution
    {Obj : Type u} (E : RecursiveDomainEquationProblem Obj) where
  object : Obj
  unfold : object = E.body object

/-- The three recurring motivations listed in Section 1.1. -/
inductive Motivation where
  | leastFixpoints
  | recursiveDomainEquations
  | continuityVersusComputability
deriving DecidableEq, Repr

/-- The major technical themes announced in the chapter overview. -/
inductive Theme where
  | domainsIndividually
  | domainsCollectively
  | cartesianClosedCategories
  | recursiveDomainEquations
  | equationalTheories
  | domainsAndLogic
  | furtherDirections
deriving DecidableEq, Repr

/-- A small interface for semantic categories of domains.  Later chapters refine
this with order, continuity, products, exponentials, and bilimits. -/
structure SemanticUniverse where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : ∀ X : Obj, Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z

namespace SemanticUniverse

/-- An endomorphism in a semantic universe. -/
abbrev End (C : SemanticUniverse.{u, v}) (X : C.Obj) : Type v :=
  C.Hom X X

/-- A categorical fixed point of an object transformer. -/
structure ObjectFixpoint (C : SemanticUniverse.{u, v}) (F : C.Obj → C.Obj) where
  object : C.Obj
  fold : C.Hom (F object) object
  unfold : C.Hom object (F object)

end SemanticUniverse

end Chapter1
end AbramskyJung

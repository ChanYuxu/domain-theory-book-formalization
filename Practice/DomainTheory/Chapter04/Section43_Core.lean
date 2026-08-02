import Practice.DomainTheory.Chapter04.Section42

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 4.3 core interfaces

Object predicates and class-level interfaces shared by the pointed and
unpointed classification modules.
-/

universe u

namespace AbramskyJung
namespace Chapter4

/-- Inclusion of one Chapter 4 domain class in another. -/
def DomainClass.Subclass (C D : DomainClass.{u}) : Prop :=
  ∀ X : OrderedDomain.{u}, C.Obj X → D.Obj X

/-- A cartesian closed full subcategory of a base class, represented by its object predicate. -/
def DomainClass.CartesianClosedSubcategoryOf (Base C : DomainClass.{u}) : Prop :=
  DomainClass.Subclass C Base ∧ DomainClass.CartesianClosed C

/-- Continuous-domain objects in Section 4.3: a dcpo carrying a basis. -/
def IsContinuousDomainObject (D : OrderedDomain.{u}) : Prop :=
  Chapter3.IsDcpo D.carrier ∧ Chapter3.IsContinuousDomain D.carrier

/-- Algebraic-domain objects in Section 4.3. -/
def IsAlgebraicDomainObject (D : OrderedDomain.{u}) : Prop :=
  Chapter3.IsDcpo D.carrier ∧ Chapter3.IsAlgebraicDomain D.carrier

/-- L-domain objects in Section 4.3. -/
def IsLDomainObject (D : OrderedDomain.{u}) : Prop :=
  IsContinuousDomainObject D ∧ IsLDomain D

/-- Algebraic L-domain objects in Section 4.3. -/
def IsAlgebraicLDomainObject (D : OrderedDomain.{u}) : Prop :=
  IsAlgebraicDomainObject D ∧ IsLDomain D

/-- Bifinite domain objects in Section 4.3. -/
def IsBifiniteDomainObject (D : OrderedDomain.{u}) : Prop :=
  IsAlgebraicDomainObject D ∧ HasBifiniteCompactBasis D

/-- Continuous domains as a Chapter 4 domain class. -/
def ContinuousDomainClass : DomainClass.{u} where
  Obj := IsContinuousDomainObject

/-- Pointed continuous domains. -/
def PointedContinuousDomainClass : DomainClass.{u} where
  Obj := IsPointedContinuousDomain

/-- Algebraic domains as a Chapter 4 domain class. -/
def AlgebraicDomainClass : DomainClass.{u} where
  Obj := IsAlgebraicDomainObject

/-- Pointed algebraic domains. -/
def PointedAlgebraicDomainClass : DomainClass.{u} where
  Obj := IsPointedAlgebraicDomain

/-- Section 4.3 object-level class of L-domains. -/
def LDomainObjectClass : DomainClass.{u} where
  Obj := IsLDomainObject

/-- Section 4.3 object-level class of algebraic L-domains. -/
def AlgebraicLDomainObjectClass : DomainClass.{u} where
  Obj := IsAlgebraicLDomainObject

/-- Section 4.3 object-level class of bifinite domains. -/
def BifiniteDomainObjectClass : DomainClass.{u} where
  Obj := IsBifiniteDomainObject

/-- Continuity of a function-space object, including its dcpo structure. -/
def HasContinuousFunctionSpace (D E : OrderedDomain.{u}) : Prop :=
  IsContinuousDomainObject (OrderedDomain.functionSpace D E)

/-- Continuity of a self-function-space object, including its dcpo structure. -/
def HasContinuousSelfFunctionSpace (D : OrderedDomain.{u}) : Prop :=
  HasContinuousFunctionSpace D D

/-- Forget the bottom from a pointed continuous domain object. -/
theorem IsPointedContinuousDomain.toContinuousDomainObject
    {D : OrderedDomain.{u}} (hD : IsPointedContinuousDomain D) :
    IsContinuousDomainObject D :=
  ⟨hD.1, hD.2.2⟩

/-- Forget the bottom from a pointed algebraic domain object. -/
theorem IsPointedAlgebraicDomain.toAlgebraicDomainObject
    {D : OrderedDomain.{u}} (hD : IsPointedAlgebraicDomain D) :
    IsAlgebraicDomainObject D :=
  ⟨hD.1, hD.2.2⟩

/-- Algebraic domains are continuous domains in the local strong-basis presentation. -/
theorem IsAlgebraicDomainObject.toContinuousDomainObject
    {D : OrderedDomain.{u}} (hD : IsAlgebraicDomainObject D) :
    IsContinuousDomainObject D :=
  ⟨hD.1, ⟨{x : D.carrier | Chapter3.Compact x}, hD.2⟩⟩

/-- Pointed algebraic domains are pointed continuous domains. -/
theorem IsPointedAlgebraicDomain.toPointedContinuousDomain
    {D : OrderedDomain.{u}} (hD : IsPointedAlgebraicDomain D) :
    IsPointedContinuousDomain D :=
  ⟨hD.1, hD.2.1, hD.toAlgebraicDomainObject.toContinuousDomainObject.2⟩

end Chapter4
end AbramskyJung

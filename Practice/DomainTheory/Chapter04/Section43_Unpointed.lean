import Practice.DomainTheory.Chapter04.Section43_Pointed

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 4.3.2

Domains without a least element, finite amalgams, and the final maximality
classification.
-/

universe u

namespace AbramskyJung
namespace Chapter4

/-- Compactness of the underlying Scott space. -/
def IsCompactDomain (D : OrderedDomain.{u}) : Prop :=
  IsScottCompactSet D Set.univ

/-- A pointed sub-dcpo of an ambient ordered domain, represented by a subset
closed under directed suprema and carrying a least element. -/
def IsPointedSubdcpo (D : OrderedDomain.{u}) (A : Set D.carrier) : Prop :=
  A.Nonempty ∧
    (∃ bot ∈ A, ∀ x ∈ A, bot ≤ x) ∧
      ∀ B : Set D.carrier, B ⊆ A → Chapter3.DirectedSet B →
        ∀ s : D.carrier, Chapter3.IsSup B s → s ∈ A

/-- A pointed domain component of an ambient domain: a pointed sub-dcpo whose
subtype is itself a continuous dcpo. -/
def IsPointedDomainComponent (D : OrderedDomain.{u}) (A : Set D.carrier) : Prop :=
  IsPointedSubdcpo D A ∧ Chapter3.IsDcpo A ∧ Chapter3.IsContinuousDomain A

/-- A domain decomposes as a disjoint union of pointed domain components. -/
def IsDisjointUnionOfPointedDomains (D : OrderedDomain.{u}) : Prop :=
  ∃ parts : Set (Set D.carrier),
    (∀ A ∈ parts, IsPointedDomainComponent D A) ∧
      Set.univ = ⋃₀ parts ∧
        ∀ A ∈ parts, ∀ B ∈ parts, A ≠ B → Disjoint A B

/-- Lemma 4.3.6, PDF text: if `[D -> E]` is continuous then `D` is compact or
`E` is a disjoint union of pointed domains.  The proof is registered as local
proof debt. -/
theorem lemma_4_3_6_compactness_from_continuous_function_space
    (D E : OrderedDomain.{u})
    (hD : IsContinuousDomainObject D)
    (hE : IsContinuousDomainObject E)
    (hFun : HasContinuousFunctionSpace D E) :
    IsCompactDomain D ∨ IsDisjointUnionOfPointedDomains E := by
  admit

/-- The PDF's intersection-closure condition for finite amalgams: every
intersection of selected components is a union of components. -/
def HasFiniteAmalgamIntersections
    (D : OrderedDomain.{u}) (parts : Set (Set D.carrier)) : Prop :=
  ∀ selected : Set (Set D.carrier), selected ⊆ parts →
    ∃ unionParts : Set (Set D.carrier), unionParts ⊆ parts ∧ ⋂₀ selected = ⋃₀ unionParts

/-- A finite amalgam is covered by finitely many pointed sub-dcpos whose
intersections are unions of components. -/
def IsFiniteAmalgam (D : OrderedDomain.{u}) : Prop :=
  Chapter3.IsDcpo D.carrier ∧
    ∃ parts : Set (Set D.carrier),
      parts.Finite ∧
        (∀ A ∈ parts, IsPointedSubdcpo D A) ∧
          Set.univ = ⋃₀ parts ∧
            HasFiniteAmalgamIntersections D parts

/-- Definition 4.3.7: finite amalgams. -/
def def_4_3_7_finite_amalgam (D : OrderedDomain.{u}) : Prop :=
  IsFiniteAmalgam D

/-- A component is represented by an object of a class through an order
isomorphism, not merely a carrier equivalence. -/
def ComponentOrderIsoToClass
    (C : DomainClass.{u}) (D : OrderedDomain.{u}) (A : Set D.carrier) : Prop :=
  ∃ E : OrderedDomain.{u}, C.Obj E ∧ Nonempty (Chapter3.OrderIsoData A E.carrier)

/-- Finite-amalgam closure of a domain class, with components compared by order
isomorphism to objects of the class. -/
def IsFiniteAmalgamOfClass (C : DomainClass.{u}) (D : OrderedDomain.{u}) : Prop :=
  Chapter3.IsDcpo D.carrier ∧
    ∃ parts : Set (Set D.carrier),
      parts.Finite ∧
        (∀ A ∈ parts, IsPointedSubdcpo D A) ∧
          Set.univ = ⋃₀ parts ∧
            HasFiniteAmalgamIntersections D parts ∧
              ∀ A ∈ parts, ComponentOrderIsoToClass C D A

/-- Finite-amalgam closure of a domain class. -/
def FiniteAmalgamClass (C : DomainClass.{u}) : DomainClass.{u} where
  Obj := IsFiniteAmalgamOfClass C

/-- Disjoint-union closure of a domain class, with components compared by order
isomorphism to objects of the class. -/
def IsDisjointUnionOfClass (C : DomainClass.{u}) (D : OrderedDomain.{u}) : Prop :=
  Chapter3.IsDcpo D.carrier ∧
    ∃ parts : Set (Set D.carrier),
      (∀ A ∈ parts, IsPointedSubdcpo D A) ∧
        Set.univ = ⋃₀ parts ∧
          (∀ A ∈ parts, ∀ B ∈ parts, A ≠ B → Disjoint A B) ∧
            ∀ A ∈ parts, ComponentOrderIsoToClass C D A

/-- Disjoint-union closure of a domain class. -/
def DisjointUnionClass (C : DomainClass.{u}) : DomainClass.{u} where
  Obj := IsDisjointUnionOfClass C

/-- The mub-closure of the empty set, using the finite-mub closure from
Definition 4.2.1. -/
def EmptyMubClosure (D : OrderedDomain.{u}) : Set D.carrier :=
  MubClosure D (∅ : Set D.carrier)

/-- Proposition 4.3.8, PDF text: a mub-complete dcpo is a finite amalgam iff
the mub-closure of the empty set is finite.  The proof is registered as local
proof debt. -/
theorem prop_4_3_8_finite_amalgam_mub_property
    (D : OrderedDomain.{u}) (hDdcpo : Chapter3.IsDcpo D.carrier) (hD : IsMubComplete D) :
    IsFiniteAmalgam D ↔ (EmptyMubClosure D).Finite := by
  admit

/-- Lemma 4.3.9, PDF text: if both `D` and `[D -> D]` are compact and
continuous then `D` is a finite amalgam.  The proof is registered as local proof
debt. -/
theorem lemma_4_3_9_compact_self_function_space_finite_amalgam
    (D : OrderedDomain.{u})
    (hD : IsContinuousDomainObject D)
    (hCompactD : IsCompactDomain D)
    (hFun : HasContinuousSelfFunctionSpace D)
    (hCompactFun : IsCompactDomain (OrderedDomain.functionSpace D D)) :
    IsFiniteAmalgam D := by
  admit

/-- Maximal cartesian closed full subcategories of a base class. -/
def IsMaximalCartesianClosedSubcategory (Base C : DomainClass.{u}) : Prop :=
  DomainClass.CartesianClosedSubcategoryOf Base C ∧
    ∀ E : DomainClass.{u},
      DomainClass.CartesianClosedSubcategoryOf Base E →
        DomainClass.Subclass C E → DomainClass.Subclass E C

/-- Theorem 4.3.10, PDF text: the maximal cartesian closed full subcategories
of `CONT` and `ALG` are the finite-amalgam and disjoint-union closures listed
in the book.  The classification proof is registered as local proof debt. -/
theorem theorem_4_3_10_maximal_cartesian_closed_subcategories :
    IsMaximalCartesianClosedSubcategory
        (ContinuousDomainClass : DomainClass.{u})
        (FiniteAmalgamClass (FSDomainClass : DomainClass.{u}) : DomainClass.{u}) ∧
      IsMaximalCartesianClosedSubcategory
        (ContinuousDomainClass : DomainClass.{u})
        (DisjointUnionClass (FSDomainClass : DomainClass.{u}) : DomainClass.{u}) ∧
      IsMaximalCartesianClosedSubcategory
        (ContinuousDomainClass : DomainClass.{u})
        (FiniteAmalgamClass (LDomainObjectClass : DomainClass.{u}) : DomainClass.{u}) ∧
      IsMaximalCartesianClosedSubcategory
        (ContinuousDomainClass : DomainClass.{u})
        (DisjointUnionClass (LDomainObjectClass : DomainClass.{u}) : DomainClass.{u}) ∧
      IsMaximalCartesianClosedSubcategory AlgebraicDomainClass
        (FiniteAmalgamClass (BifiniteDomainObjectClass : DomainClass.{u}) : DomainClass.{u}) ∧
      IsMaximalCartesianClosedSubcategory AlgebraicDomainClass
        (DisjointUnionClass (BifiniteDomainObjectClass : DomainClass.{u}) : DomainClass.{u}) ∧
      IsMaximalCartesianClosedSubcategory
        (AlgebraicDomainClass : DomainClass.{u})
        (FiniteAmalgamClass (AlgebraicLDomainObjectClass : DomainClass.{u}) : DomainClass.{u}) ∧
      IsMaximalCartesianClosedSubcategory
        (AlgebraicDomainClass : DomainClass.{u})
        (DisjointUnionClass (AlgebraicLDomainObjectClass : DomainClass.{u}) : DomainClass.{u}) := by
  admit

end Chapter4
end AbramskyJung

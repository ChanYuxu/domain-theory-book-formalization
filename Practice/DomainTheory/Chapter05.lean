import Practice.DomainTheory.Chapter04

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 5

This chapter gives reusable Lean interfaces for recursive domain equations:
continuous endofunctors, solutions, bilimit approximations, canonicity, and
admissible predicates/relations used for induction and coinduction.

Numbered declarations live in the split `Chapter05/Section*.lean` files.  The
canonical-solution interface records the iterated expanding sequence and its
bilimit identification; initiality, finality, and minimality remain theorems to
be derived from that construction.
-/

universe u v

namespace AbramskyJung
namespace Chapter5

open Chapter4

/-- The pointwise bottom continuous map.  This instance belongs with the common
Chapter 5 function-space infrastructure because the fixed-point arguments of
Section 5.3 use it before the relation machinery of Section 5.4. -/
instance continuousFunctionSpaceOrderBot
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E] :
    OrderBot (Chapter3.ContFun D E) where
  bot := Chapter3.ContFun.const (D := D) (E := E) (⊥ : E)
  bot_le _ _ := bot_le

/-- A domain endofunctor on the bundled ordered domains from Chapter 4.

The laws are stated pointwise because the local continuous-map bundle does not
yet provide an extensionality theorem. -/
structure DomainEndofunctor where
  mapObj : OrderedDomain.{u} → OrderedDomain.{u}
  mapHom :
    ∀ ⦃D E : OrderedDomain.{u}⦄,
      OrderedDomain.ContFunCarrier D E →
        OrderedDomain.ContFunCarrier (mapObj D) (mapObj E)
  mapHom_id :
    ∀ ⦃D : OrderedDomain.{u}⦄ (x : (mapObj D).carrier),
      mapHom (OrderedDomain.idContFun D) x = x
  mapHom_comp :
    ∀ ⦃D E G : OrderedDomain.{u}⦄
      (f : OrderedDomain.ContFunCarrier D E)
      (g : OrderedDomain.ContFunCarrier E G)
      (x : (mapObj D).carrier),
        mapHom g (mapHom f x) =
          mapHom (OrderedDomain.compContFun g f) x
  mapHom_congr :
    ∀ ⦃D E : OrderedDomain.{u}⦄
      {f g : OrderedDomain.ContFunCarrier D E},
      (∀ x : D.carrier, f x = g x) →
        ∀ y : (mapObj D).carrier, mapHom f y = mapHom g y

/-- Local continuity of an endofunctor, expressed as preservation of directed
suprema in hom-posets. -/
def LocallyContinuous (F : DomainEndofunctor.{u}) : Prop :=
  ∀ ⦃D E : OrderedDomain.{u}⦄,
    Chapter3.ScottContinuous
      (fun f : OrderedDomain.ContFunCarrier D E => F.mapHom f)

/-- A solution of the recursive equation `D = F D`. -/
structure DomainEquationSolution (F : DomainEndofunctor.{u}) where
  object : OrderedDomain.{u}
  fold : OrderedDomain.ContFunCarrier (F.mapObj object) object
  unfold : OrderedDomain.ContFunCarrier object (F.mapObj object)
  fold_unfold : ∀ x : object.carrier, fold (unfold x) = x
  unfold_fold : ∀ x : (F.mapObj object).carrier, unfold (fold x) = x

/-- An algebra for an endofunctor on the bundled domain interface. -/
structure FunctorAlgebra (F : DomainEndofunctor.{u}) where
  object : OrderedDomain.{u}
  structureMap : OrderedDomain.ContFunCarrier (F.mapObj object) object

namespace FunctorAlgebra

/-- Homomorphisms of `F`-algebras, expressed by the usual commuting square. -/
structure Hom (F : DomainEndofunctor.{u}) (A B : FunctorAlgebra F) where
  map : OrderedDomain.ContFunCarrier A.object B.object
  commutes :
    ∀ x : (F.mapObj A.object).carrier,
      map (A.structureMap x) = B.structureMap (F.mapHom map x)

/-- An isomorphism of `F`-algebras.  Both directions are algebra
homomorphisms, so this is stronger than an order isomorphism of the carriers. -/
structure Iso (F : DomainEndofunctor.{u}) (A B : FunctorAlgebra F) where
  hom : Hom F A B
  inv : Hom F B A
  hom_inv_id : ∀ x : B.object.carrier, hom.map (inv.map x) = x
  inv_hom_id : ∀ x : A.object.carrier, inv.map (hom.map x) = x

/-- The identity homomorphism of an `F`-algebra. -/
def idHom (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F) : Hom F A A where
  map := OrderedDomain.idContFun A.object
  commutes := by
    intro x
    change A.structureMap x = A.structureMap (F.mapHom (OrderedDomain.idContFun A.object) x)
    rw [F.mapHom_id]

/-- Composition of `F`-algebra homomorphisms. -/
def compHom
    (F : DomainEndofunctor.{u}) {A B C : FunctorAlgebra F}
    (g : Hom F B C) (f : Hom F A B) : Hom F A C where
  map := OrderedDomain.compContFun g.map f.map
  commutes := by
    intro x
    change g.map (f.map (A.structureMap x)) =
      C.structureMap (F.mapHom (OrderedDomain.compContFun g.map f.map) x)
    rw [f.commutes, g.commutes, F.mapHom_comp]

/-- Apply an endofunctor to the carrier and structure map of an algebra. -/
def mapAlgebra (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F) :
    FunctorAlgebra F where
  object := F.mapObj A.object
  structureMap := F.mapHom A.structureMap

/-- The structure map of an algebra, viewed as a homomorphism from its image
algebra. -/
def structureHom (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F) :
    Hom F (mapAlgebra F A) A where
  map := A.structureMap
  commutes := by
    intro x
    rfl

end FunctorAlgebra

/-- A homomorphism which is below every other homomorphism. -/
def IsLeastAlgebraHom
    (F : DomainEndofunctor.{u}) (A C : FunctorAlgebra F)
    (h : FunctorAlgebra.Hom F A C) : Prop :=
  ∀ k : FunctorAlgebra.Hom F A C, h.map ≤ k.map

namespace FunctorAlgebra

/-- The Lambek structure-map isomorphism for an algebra: the algebra map
`F A -> A` has a continuous inverse with the two inverse laws. -/
structure AlgebraStructureIso (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F) where
  inverse : OrderedDomain.ContFunCarrier A.object (F.mapObj A.object)
  left_inverse : ∀ x : A.object.carrier, A.structureMap (inverse x) = x
  right_inverse :
    ∀ x : (F.mapObj A.object).carrier, inverse (A.structureMap x) = x

/-- Compatibility name for the structure-map isomorphism used in Section 5.3.

Earlier versions also stored the least-homomorphism and invariance conclusions
of Section 5.3 in this input package.  Those conclusions are theorems, not part
of the hypothesis that `F A` and `A` are isomorphic. -/
abbrev StructureIso (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F) :=
  AlgebraStructureIso F A

/-- Initiality of an `F`-algebra: every target algebra admits a unique
homomorphism from it. -/
structure IsInitial (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F) : Prop where
  unique_hom :
    ∀ B : FunctorAlgebra F,
      ∃ h : Hom F A B, ∀ k : Hom F A B,
        ∀ x : A.object.carrier, k.map x = h.map x

/-- The bundled assertion that the algebra structure map has the Lambek
isomorphism package from Lemma 5.1.2. -/
def HasStructureIso (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F) : Prop :=
  Nonempty (AlgebraStructureIso F A)

end FunctorAlgebra

/-- Turn a solution of `D = F D` into the associated `F`-algebra. -/
def DomainEquationSolution.toAlgebra
    {F : DomainEndofunctor.{u}} (S : DomainEquationSolution F) :
    FunctorAlgebra F where
  object := S.object
  structureMap := S.fold

/-- Coalgebras for an endofunctor on the bundled domain interface. -/
structure FunctorCoalgebra (F : DomainEndofunctor.{u}) where
  object : OrderedDomain.{u}
  destruct : OrderedDomain.ContFunCarrier object (F.mapObj object)

/-- Turn a solution of `D = F D` into the associated `F`-coalgebra. -/
def DomainEquationSolution.toCoalgebra
    {F : DomainEndofunctor.{u}} (S : DomainEquationSolution F) :
    FunctorCoalgebra F where
  object := S.object
  destruct := S.unfold

/-- Finality of a coalgebra: unique coalgebra morphisms into it. -/
def IsFinalCoalgebra
    (F : DomainEndofunctor.{u}) (A : FunctorCoalgebra F) : Prop :=
  ∀ B : FunctorCoalgebra F,
    ∃! h : OrderedDomain.ContFunCarrier B.object A.object,
      ∀ x : B.object.carrier,
        A.destruct (h x) = F.mapHom h (B.destruct x)

/-- A parameterized recursive equation `D p = F p (D p)`. -/
structure ParameterizedEquation (Param : Type u) where
  body : Param → DomainEndofunctor.{u}

/-- A family of solutions for a parameterized equation. -/
structure ParameterizedSolution {Param : Type u} (E : ParameterizedEquation Param) where
  solution : ∀ p : Param, DomainEquationSolution (E.body p)

/-- The embedding-projection approximation chain used to construct solutions. -/
structure ApproximationChain where
  object : Nat → OrderedDomain.{u}
  step :
    ∀ n : Nat,
      Chapter3.EPPair (object n).carrier (object (n + 1)).carrier

/-- A subdomain witness represented by an embedding-projection pair. -/
structure SubdomainOf (D E : OrderedDomain.{u}) where
  ep : Chapter3.EPPair D.carrier E.carrier

/-- The object sequence `A, F A, F² A, ...` generated by an endofunctor. -/
def FunctorIterationObject
    (F : DomainEndofunctor.{u}) (A : OrderedDomain.{u}) : Nat → OrderedDomain.{u}
  | 0 => A
  | n + 1 => F.mapObj (FunctorIterationObject F A n)

/-- The embedding component of an e-p-pair as a bundled continuous map. -/
def epEmbeddingContFun
    {D E : OrderedDomain.{u}} (ep : Chapter3.EPPair D.carrier E.carrier) :
    OrderedDomain.ContFunCarrier D E where
  toFun := ep.e
  continuous := ep.continuous_e

/-- The projection component of an e-p-pair as a bundled continuous map. -/
def epProjectionContFun
    {D E : OrderedDomain.{u}} (ep : Chapter3.EPPair D.carrier E.carrier) :
    OrderedDomain.ContFunCarrier E D where
  toFun := ep.p
  continuous := ep.continuous_p

/-- The approximation endomap `e ∘ p` associated with an e-p-pair. -/
def epApproximationContFun
    {D E : OrderedDomain.{u}} (ep : Chapter3.EPPair D.carrier E.carrier) :
    OrderedDomain.ContFunCarrier E E :=
  OrderedDomain.compContFun (epEmbeddingContFun ep) (epProjectionContFun ep)

/-- Construction evidence for a canonical solution of `D ≅ F D`.

The adjacent embedding-projection pairs are required to be the initial pair and
its successive functor images.  The full expanding-sequence laws are supplied
by Chapter 3's `ExpandingSequence`, and the proposed solution carrier is
identified with its bilimit.  This package deliberately does not contain the
later initiality, finality, or minimality conclusions. -/
structure CanonicalSolutionConstruction
    (F : DomainEndofunctor.{u}) (S : DomainEquationSolution F) where
  locallyContinuous : LocallyContinuous F
  base : OrderedDomain.{u}
  initial : Chapter3.EPPair base.carrier (F.mapObj base).carrier
  sequence :
    Chapter3.ExpandingSequence
      (fun n : Nat => (FunctorIterationObject F base n).carrier)
  initial_embedding :
    ∀ x : base.carrier, sequence.e (Nat.le_succ 0) x = initial.e x
  initial_projection :
    ∀ x : (F.mapObj base).carrier, sequence.p (Nat.le_succ 0) x = initial.p x
  successor_embedding :
    ∀ (n : Nat) (x : (F.mapObj (FunctorIterationObject F base n)).carrier),
      sequence.e (Nat.le_succ (n + 1)) x =
        F.mapHom
          { toFun := sequence.e (Nat.le_succ n)
            continuous := sequence.continuous_e (Nat.le_succ n) }
          x
  successor_projection :
    ∀ (n : Nat) (x :
        (F.mapObj (F.mapObj (FunctorIterationObject F base n))).carrier),
      sequence.p (Nat.le_succ (n + 1)) x =
        F.mapHom
          { toFun := sequence.p (Nat.le_succ n)
            continuous := sequence.continuous_p (Nat.le_succ n) }
          x
  stage_dcpo :
    ∀ n : Nat, Chapter3.IsDcpo (FunctorIterationObject F base n).carrier
  stage_antisymm :
    ∀ (n : Nat) (x y : (FunctorIterationObject F base n).carrier),
      x ≤ y → y ≤ x → x = y
  solution_bilimit_iso :
    Chapter3.OrderIsoData S.object.carrier (Chapter3.Bilimit sequence)
  base_orderBot : OrderBot base.carrier
  base_subsingleton : ∀ x y : base.carrier, x = y
  solution_orderBot : OrderBot S.object.carrier
  solution_dcpo : Chapter3.IsDcpo S.object.carrier
  solution_antisymm :
    ∀ x y : S.object.carrier, x ≤ y → y ≤ x → x = y
  functor_solution_dcpo : Chapter3.IsDcpo (F.mapObj S.object).carrier
  stagePair :
    ∀ n : Nat,
      Chapter3.EPPair (FunctorIterationObject F base n).carrier S.object.carrier
  stage_compatible :
    ∀ (n : Nat) (x : (FunctorIterationObject F base n).carrier),
      (stagePair (n + 1)).e (sequence.e (Nat.le_succ n) x) =
        (stagePair n).e x
  stage_zero_strict :
    @Chapter2.StrictMap base.carrier S.object.carrier inferInstance inferInstance
      base_orderBot solution_orderBot (stagePair 0).e
  unfold_stage_embedding :
    ∀ (n : Nat) (x : (FunctorIterationObject F base (n + 1)).carrier),
      S.unfold ((stagePair (n + 1)).e x) =
        F.mapHom (epEmbeddingContFun (stagePair n)) x
  fold_stage_projection :
    ∀ (n : Nat) (x : (F.mapObj S.object).carrier),
      (stagePair (n + 1)).p (S.fold x) =
        F.mapHom (epProjectionContFun (stagePair n)) x
  identity_is_sup_stage_approximations :
    Chapter3.IsSup
      (Set.range fun n : Nat => epApproximationContFun (stagePair n))
      (OrderedDomain.idContFun S.object)
  stage_approximations_directed :
    Chapter3.DirectedSet
      (Set.range fun n : Nat => epApproximationContFun (stagePair n))

namespace CanonicalSolutionConstruction

/-- The complete Chapter 3 bilimit package determined by canonical construction
evidence. -/
noncomputable def bilimitData
    {F : DomainEndofunctor.{u}} {S : DomainEquationSolution F}
    (C : CanonicalSolutionConstruction F S) :
    Chapter3.ExpandingSequence.BilimitTheoremFullData C.sequence
      C.stage_dcpo C.stage_antisymm :=
  Chapter3.theorem_3_3_7_expanding_sequence_bilimit
    C.sequence C.stage_dcpo C.stage_antisymm

end CanonicalSolutionConstruction

/-- A canonical solution together with its functor-iteration bilimit
construction. -/
structure CanonicalSolution (F : DomainEndofunctor.{u}) where
  solution : DomainEquationSolution F
  construction : CanonicalSolutionConstruction F solution

/-- An admissible predicate on a pointed domain: it contains bottom and is
closed under suprema of increasing omega-chains. -/
structure AdmissiblePredicate
    (D : OrderedDomain.{u}) [OrderBot D.carrier]
    (P : Set D.carrier) : Prop where
  contains_bottom : (⊥ : D.carrier) ∈ P
  closed_omega_chains :
    ∀ (c : Nat → D.carrier) (s : D.carrier),
      (∀ n : Nat, c n ∈ P) →
        (∀ n : Nat, c n ≤ c (n + 1)) →
          Chapter3.IsSup (Set.range c) s → s ∈ P

/-- A binary relation closed under directed suprema in both coordinates. -/
def AdmissibleRelation (D E : OrderedDomain.{u})
    (R : D.carrier → E.carrier → Prop) : Prop :=
  (∀ ⦃A : Set D.carrier⦄ ⦃s : D.carrier⦄ ⦃y : E.carrier⦄,
      Chapter3.DirectedSet A →
        (∀ x ∈ A, R x y) → Chapter3.IsSup A s → R s y) ∧
    ∀ ⦃B : Set E.carrier⦄ ⦃t : E.carrier⦄ ⦃x : D.carrier⦄,
      Chapter3.DirectedSet B →
        (∀ y ∈ B, R x y) → Chapter3.IsSup B t → R x t

/-- Structural induction data for terms interpreted in a recursive solution. -/
structure StructuralInductionData
    (D : OrderedDomain.{u}) [OrderBot D.carrier] where
  predicate : Set D.carrier
  admissible : AdmissiblePredicate D predicate
  constructors_preserve : Prop

/-- Coinduction data for relations interpreted in a recursive solution. -/
structure CoinductionData (D E : OrderedDomain.{u}) where
  relation : D.carrier → E.carrier → Prop
  admissible : AdmissibleRelation D E relation
  destructors_preserve : Prop

end Chapter5
end AbramskyJung

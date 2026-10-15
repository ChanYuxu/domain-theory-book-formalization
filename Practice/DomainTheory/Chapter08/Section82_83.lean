import Practice.DomainTheory.Chapter08.Core
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monad.Basic

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Sections 8.2--8.3

Stability and the three reformulations of domain theory discussed in Chapter 8:
partial maps, computational monads, and linear types.  The two algebraic
characterizations of stable maps are stated exactly at the level supported by
the preceding chapters; the survey gives no proofs, so their proof terms remain
classified `admit`s.
-/

universe u v w

namespace AbramskyJung
namespace Chapter8

open Chapter4

/-! ## 8.2 Stability and sequentiality -/

/-- The witness condition supplied by Proposition 2.2.11.  For
`e in C_(f x)`, a basis approximant `d in B_x` is sufficient when every input
extending `d` makes the output extend `e`. -/
def IsContinuityWitness {D E : OrderedDomain.{u}}
    (B : Set D.carrier) (f : OrderedDomain.ContFunCarrier D E)
    (x : D.carrier) (e : E.carrier) (d : D.carrier) : Prop :=
  d ∈ Chapter2.Approximants B x ∧
    ∀ y : D.carrier, d ≤ y → e ≤ f y

/-- Section 8.2, the modulus-of-stability data.  `modulus x e` is the least
continuity witness for the output approximation `e`. -/
structure StabilityModulus {D E : OrderedDomain.{u}}
    (B : Set D.carrier) (C : Set E.carrier)
    (f : OrderedDomain.ContFunCarrier D E) where
  modulus :
    ∀ (x : D.carrier) (e : E.carrier),
      e ∈ Chapter2.Approximants C (f x) → D.carrier
  modulus_spec :
    ∀ (x : D.carrier) (e : E.carrier)
      (he : e ∈ Chapter2.Approximants C (f x)),
      IsContinuityWitness B f x e (modulus x e he)
  modulus_least :
    ∀ (x : D.carrier) (e : E.carrier)
      (he : e ∈ Chapter2.Approximants C (f x)) (d : D.carrier),
      IsContinuityWitness B f x e d → modulus x e he ≤ d

/-- A continuous map is stable when its modulus exists for every basis output
approximation. -/
def IsStable {D E : OrderedDomain.{u}}
    (B : Set D.carrier) (C : Set E.carrier)
    (f : OrderedDomain.ContFunCarrier D E) : Prop :=
  Nonempty (StabilityModulus B C f)

/-- The pointwise part of the stable ordering transports output approximants
from `f x` to `g x`. -/
theorem approximant_of_pointwise_le {D E : OrderedDomain.{u}}
    {C : Set E.carrier} {f g : OrderedDomain.ContFunCarrier D E}
    (hfg : f ≤ g) (x : D.carrier) (e : E.carrier)
    (he : e ∈ Chapter2.Approximants C (f x)) :
    e ∈ Chapter2.Approximants C (g x) := by
  exact ⟨he.1, Chapter2.prop_2_2_2_2 le_rfl he.2 (hfg x)⟩

/-- Section 8.2, displayed stable order
`f <=_s g` iff `f <= g` and the two moduli agree on every output
approximation of `f x`. -/
def StableOrder {D E : OrderedDomain.{u}}
    {B : Set D.carrier} {C : Set E.carrier}
    {f g : OrderedDomain.ContFunCarrier D E}
    (Mf : StabilityModulus B C f) (Mg : StabilityModulus B C g) : Prop :=
  ∃ hfg : f ≤ g,
    ∀ (x : D.carrier) (e : E.carrier)
      (he : e ∈ Chapter2.Approximants C (f x)),
      Mf.modulus x e he =
        Mg.modulus x e (approximant_of_pointwise_le hfg x e he)

/-- Preservation of every bounded nonempty infimum, expressed relationally so
the statement does not assume a global lattice instance. -/
def PreservesBoundedNonemptyInfima {D E : OrderedDomain.{u}}
    (f : OrderedDomain.ContFunCarrier D E) : Prop :=
  ∀ (A : Set D.carrier) (i : D.carrier),
    A.Nonempty → (∃ upper : D.carrier, Chapter2.IsUpperBound A upper) →
      Chapter3.IsInf A i → Chapter3.IsInf (f '' A) (f i)

/-- Section 8.2 survey assertion: between L-domains, stability is equivalent
to preservation of bounded nonempty infima.  The chapter states the result but
does not supply a proof. -/
theorem stable_iff_preserves_bounded_nonempty_infima
    {D E : OrderedDomain.{u}} (B : Set D.carrier) (C : Set E.carrier)
    (hB : Chapter2.IsBasis B) (hC : Chapter2.IsBasis C)
    (_hD : Chapter4.IsLDomain D) (_hE : Chapter4.IsLDomain E)
    (f : OrderedDomain.ContFunCarrier D E) :
    IsStable B C f ↔ PreservesBoundedNonemptyInfima f := by
  admit

/-- The relational spelling of `f(x) = f(y) meet g(x)` used in the source.
The meet is represented by its universal property. -/
def StableMeetEquation {D E : OrderedDomain.{u}}
    (f g : OrderedDomain.ContFunCarrier D E) : Prop :=
  ∀ x y : D.carrier, x ≤ y →
    ∃ i : E.carrier,
      Chapter3.IsInf ({z : E.carrier | z = f y ∨ z = g x}) i ∧ f x = i

/-- Section 8.2 survey assertion: for stable maps between L-domains, the
stable order is characterized by `f(x) = f(y) meet g(x)` whenever `x <= y`.
No proof is included in the chapter. -/
theorem stableOrder_iff_meet_equation
    {D E : OrderedDomain.{u}} {B : Set D.carrier} {C : Set E.carrier}
    (_hD : Chapter4.IsLDomain D) (_hE : Chapter4.IsLDomain E)
    {f g : OrderedDomain.ContFunCarrier D E}
    (Mf : StabilityModulus B C f) (Mg : StabilityModulus B C g) :
    StableOrder Mf Mg ↔ StableMeetEquation f g := by
  admit

/-! ## 8.3.1 Predomains and partial functions -/

/-- Section 8.3.1, partial continuous maps.  The domain of definition is
Scott-open and the restricted total map is Scott-continuous. -/
structure PartialContinuousMap (D : OrderedDomain.{u}) (E : OrderedDomain.{v}) where
  domain : Set D.carrier
  domain_scottOpen : Chapter2.ScottOpen domain
  toFun : domain → E.carrier
  continuous : Chapter3.ScottContinuous toFun

namespace PartialContinuousMap

instance (D : OrderedDomain.{u}) (E : OrderedDomain.{v}) :
    CoeFun (PartialContinuousMap D E) (fun f => f.domain → E.carrier) :=
  ⟨toFun⟩

end PartialContinuousMap

/-- The hom-set data needed to express the source's natural isomorphism
`[D -> E_bot] ~= [D ⇀ E]`.  Naturality belongs to the category-level theory
referenced by the source and is deliberately not invented here. -/
structure LiftingPartialMapComparison (D : OrderedDomain.{u}) (E : OrderedDomain.{u}) where
  toPartial :
    Chapter3.ContFun D.carrier (Chapter3.Lifting E.carrier) →
      PartialContinuousMap D E
  toLifted :
    PartialContinuousMap D E →
      Chapter3.ContFun D.carrier (Chapter3.Lifting E.carrier)
  toPartial_toLifted : ∀ f, toPartial (toLifted f) = f
  toLifted_toPartial : ∀ f, toLifted (toPartial f) = f

/-! ## 8.3.2 Computational monads -/

open CategoryTheory
open CategoryTheory.Limits

/-- The natural-transformation part of a tensorial strength
`t_(A,B) : A x T B -> T (A x B)`.  The chapter refers to, but does not print,
the unit and associativity coherence equations; hence this declaration is
explicitly the raw strength interface rather than a claim that those omitted
axioms have been reconstructed. -/
structure RawTensorialStrength (C : Type u) [Category.{v} C] [HasBinaryProducts C]
    (T : CategoryTheory.Monad C) where
  app : ∀ A B : C, A ⨯ T.obj B ⟶ T.obj (A ⨯ B)
  naturality :
    ∀ {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B'),
      Limits.prod.map f (T.map g) ≫ app A' B' =
        app A B ≫ T.map (Limits.prod.map f g)

/-- Section 8.3.2, the data printed for a computational monad: a categorical
monad together with its raw tensorial strength. -/
structure ComputationalMonad (C : Type u) [Category.{v} C] [HasBinaryProducts C] where
  monad : CategoryTheory.Monad C
  strength : RawTensorialStrength C monad

namespace ComputationalMonad

/-- The displayed Kleisli composite
`A -f-> T B -Tg-> T T C -mu_C-> T C`. -/
def kleisliComp {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    (M : ComputationalMonad C) {A B D : C}
    (f : A ⟶ M.monad.obj B) (g : B ⟶ M.monad.obj D) :
    A ⟶ M.monad.obj D :=
  f ≫ M.monad.map g ≫ M.monad.μ.app D

@[simp]
theorem kleisliComp_unit_left {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    (M : ComputationalMonad C) {A B : C} (f : A ⟶ M.monad.obj B) :
    M.kleisliComp (M.monad.η.app A) f = f := by
  unfold kleisliComp
  calc
    M.monad.η.app A ≫ M.monad.map f ≫ M.monad.μ.app B =
        (M.monad.η.app A ≫ M.monad.map f) ≫ M.monad.μ.app B :=
      (Category.assoc _ _ _).symm
    _ = (f ≫ M.monad.η.app (M.monad.obj B)) ≫ M.monad.μ.app B := by
      exact congrArg (fun k => k ≫ M.monad.μ.app B)
        (CategoryTheory.Monad.unit_naturality C M.monad f).symm
    _ = f ≫ (M.monad.η.app (M.monad.obj B) ≫ M.monad.μ.app B) :=
      Category.assoc _ _ _
    _ = f ≫ 𝟙 (M.monad.obj B) :=
      congrArg (fun k => f ≫ k) (M.monad.left_unit B)
    _ = f := Category.comp_id f

@[simp]
theorem kleisliComp_unit_right {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    (M : ComputationalMonad C) {A B : C} (f : A ⟶ M.monad.obj B) :
    M.kleisliComp f (M.monad.η.app B) = f := by
  unfold kleisliComp
  calc
    f ≫ M.monad.map (M.monad.η.app B) ≫ M.monad.μ.app B =
        f ≫ 𝟙 (M.monad.obj B) :=
      congrArg (fun k => f ≫ k) (M.monad.right_unit B)
    _ = f := Category.comp_id f

end ComputationalMonad

/-- Survey record for examples asserted to carry strong-monad structure. -/
structure StrongMonadExample where
  construction : String
  unitDescription : String
  multiplicationDescription : String
  citations : List SurveyCitation
deriving DecidableEq, Repr

/-- The examples explicitly mentioned in Section 8.3.2. -/
def strongMonadExamples : List StrongMonadExample :=
  [ { construction := "lifting"
      unitDescription := "up"
      multiplicationDescription := "flatten nested liftings"
      citations := [{ key := "Mog91", role := "computational monads" }] },
    { construction := "Hoare, Smyth, and Plotkin powerdomains"
      unitDescription := "singleton"
      multiplicationDescription := "big union"
      citations := [{ key := "CP92", role := "fixpoint objects and recursion" }] } ]

/-! ## 8.3.3 Linear types -/

/-- The source's linear decomposition
`[A -> B] ~= [!A -o B]`, represented as an equivalence between ordinary
continuous maps and strict continuous maps out of `!A`. -/
structure LinearFunctionSpaceComparison
    (bang : OrderedDomain.{u} → OrderedDomain.{u})
    (A B : OrderedDomain.{u}) where
  toLinear :
    OrderedDomain.ContFunCarrier A B →
      Chapter3.StrictContFun (bang A).carrier B.carrier
  toNonlinear :
    Chapter3.StrictContFun (bang A).carrier B.carrier →
      OrderedDomain.ContFunCarrier A B
  toLinear_toNonlinear : ∀ f, toLinear (toNonlinear f) = f
  toNonlinear_toLinear : ∀ f, toNonlinear (toLinear f) = f

/-- Section 8.3.3 interface for a linear domain model.  Products, coproducts,
smash product, strict function space, and the lifting comonad are recorded as
named structure because the chapter only surveys their categorical laws. -/
structure LinearDomainModel where
  strictObjects : DomainClass.{u}
  bang : OrderedDomain.{u} → OrderedDomain.{u}
  functionSpaceComparison :
    ∀ A B : OrderedDomain.{u}, LinearFunctionSpaceComparison bang A B
  productName : String
  coproductName : String
  tensorName : String
  internalHomName : String
  comonadName : String
  citations : List SurveyCitation

/-- The complete-lattice example described at the end of Section 8.3.3. -/
def completeLatticeLinearExample : StrongMonadExample :=
  { construction := "complete lattices and arbitrary-supremum homomorphisms"
    unitDescription := "!L is the Hoare powerdomain P_H(L)"
    multiplicationDescription := "linear decomposition of continuous maps"
    citations :=
      [ { key := "Hoo92", role := "linear domain models" },
        { key := "Ehr93", role := "stable and linear semantics" },
        { key := "Hut94", role := "linear decomposition examples" } ] }

end Chapter8
end AbramskyJung

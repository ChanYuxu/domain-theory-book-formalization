import Practice.DomainTheory.Chapter03

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 4

This chapter packages the material on cartesian closed categories of domains:
lattice-like domains, compactness conditions, bifinite and FS domains, coherence,
and the hierarchy of domain categories.

`Chapter04/Core.lean` is the shared base interface imported by the split section
files. Numbered item declarations live in `Chapter04/Section*.lean`, aggregated
by `Chapter04/NumberedItems.lean`; the per-item PDF anchor and semantic-strength
audit is recorded in `formalization_status.md`.
-/

universe u v

namespace AbramskyJung
namespace Chapter4

/-- A bundled ordered carrier used for categorical interfaces. -/
structure OrderedDomain where
  carrier : Type u
  preorder : Preorder carrier

namespace OrderedDomain

instance (D : OrderedDomain.{u}) : Preorder D.carrier := D.preorder

/-- The product object with the coordinatewise order. -/
def prod (D E : OrderedDomain.{u}) : OrderedDomain.{u} where
  carrier := D.carrier × E.carrier
  preorder := inferInstance

/-- The type of Scott-continuous maps between two ordered domains. -/
abbrev ContFunCarrier (D E : OrderedDomain.{u}) : Type u :=
  Chapter3.ContFun D.carrier E.carrier

instance contFunPreorder (D E : OrderedDomain.{u}) :
    Preorder (ContFunCarrier D E) where
  le f g := ∀ x : D.carrier, f x ≤ g x
  le_refl f x := le_rfl
  le_trans f g h hfg hgh x := le_trans (hfg x) (hgh x)

/-- The continuous function-space object, ordered pointwise. -/
def functionSpace (D E : OrderedDomain.{u}) : OrderedDomain.{u} where
  carrier := ContFunCarrier D E
  preorder := contFunPreorder D E

/-- Identity as a bundled Scott-continuous map. -/
def idContFun (D : OrderedDomain.{u}) : ContFunCarrier D D where
  toFun := fun x => x
  continuous := Chapter3.scottContinuous_id

/-- Composition of bundled Scott-continuous maps. -/
def compContFun {D E F : OrderedDomain.{u}}
    (g : ContFunCarrier E F) (f : ContFunCarrier D E) : ContFunCarrier D F :=
  Chapter3.ContFun.comp g f

end OrderedDomain

/-- A class of ordered domains, presented extensionally as a predicate on objects. -/
structure DomainClass where
  Obj : OrderedDomain.{u} → Prop

namespace DomainClass

def ClosedUnderProducts (C : DomainClass.{u}) : Prop :=
  ∀ ⦃D E : OrderedDomain.{u}⦄,
    C.Obj D → C.Obj E → C.Obj (OrderedDomain.prod D E)

def ClosedUnderFunctionSpaces (C : DomainClass.{u}) : Prop :=
  ∀ ⦃D E : OrderedDomain.{u}⦄,
    C.Obj D → C.Obj E → C.Obj (OrderedDomain.functionSpace D E)

/-- Legacy object-closure interface.  It is useful as a projection of genuine
cartesian-closed data, but by itself does not state a categorical universal
property. -/
structure CartesianClosed (C : DomainClass.{u}) where
  products : ClosedUnderProducts C
  exponentials : ClosedUnderFunctionSpaces C

/-- Source-facing cartesian-closed full-subcategory data.  The universal
properties are inherited from Chapter 3's Scott-continuous-map category model;
`object_iff` identifies its objects with the Chapter 4 object predicate. -/
structure CartesianClosedFullSubcategoryData (C : DomainClass.{u}) : Type (u + 1) where
  universal : Chapter3.CartesianClosedFullSubcategoryOfDCPO.{u}
  object_iff :
    ∀ D : Type u, ∀ [Preorder D],
      universal.object D ↔ C.Obj ⟨D, inferInstance⟩
  legacyClosure : CartesianClosed C

/-- Forget the categorical universal properties and retain object closure. -/
def CartesianClosedFullSubcategoryData.toLegacy
    {C : DomainClass.{u}} (hC : CartesianClosedFullSubcategoryData C) :
    CartesianClosed C :=
  hC.legacyClosure

/-- Every object in source-facing cartesian-closed data is a partial-order
dcpo, as required by the ambient category `DCPO`. -/
theorem CartesianClosedFullSubcategoryData.object_dcpoOrder
    {C : DomainClass.{u}} (hC : CartesianClosedFullSubcategoryData C)
    (D : OrderedDomain.{u}) (hD : C.Obj D) :
    Chapter2.IsDcpoOrder D.carrier := by
  have hObj : hC.universal.object D.carrier :=
    (hC.object_iff D.carrier).2 hD
  exact
    ⟨hC.universal.object_dcpo D.carrier hObj,
      hC.universal.object_antisymmetric D.carrier hObj⟩

end DomainClass

/-- The finite binary join/meet interface for lattice-like domains. -/
structure LatticeLikeDomain where
  object : OrderedDomain.{u}
  binary_sup :
    ∀ x y : object.carrier,
      ∃ z : object.carrier,
        Chapter3.IsSup ({w | w = x ∨ w = y} : Set object.carrier) z
  binary_inf :
    ∀ x y : object.carrier,
      ∃ z : object.carrier,
        Chapter3.IsInf ({w | w = x ∨ w = y} : Set object.carrier) z

/-- A finite continuous projection as used in the definition of bifinite domains. -/
structure FiniteProjection (D : OrderedDomain.{u}) where
  toFun : D.carrier → D.carrier
  continuous : Chapter3.ScottContinuous toFun
  idem : ∀ x : D.carrier, toFun (toFun x) = toFun x
  below : ∀ x : D.carrier, toFun x ≤ x
  finite_range : (Set.range toFun).Finite

/-- Bifinite domains in the current interface are represented by an increasing
`Nat`-indexed sequence of finite projections whose pointwise suprema recover the
original points. This is the sequence-style presentation used by later files, not
the full compact-basis/Plotkin-order definition from the PDF. -/
structure BifiniteDomain where
  object : OrderedDomain.{u}
  projection : Nat → FiniteProjection object
  increasing :
    ∀ n : Nat, ∀ x : object.carrier,
      (projection n).toFun x ≤ (projection (n + 1)).toFun x
  approximates :
    ∀ x : object.carrier,
      Chapter3.IsSup (Set.range (fun n : Nat => (projection n).toFun x)) x

/-- Definition 4.2.9, finite separation. PDF text: if `D` is a dcpo and
`f : D -> D` is Scott-continuous, then `f` is finitely separated from the
identity on `D` if there exists a finite set `M` such that for every `x ∈ D`
there is `m ∈ M` with `f x <= m <= x`. -/
structure FinitelySeparatedSelfMap (D : OrderedDomain.{u}) where
  toFun : D.carrier → D.carrier
  continuous : Chapter3.ScottContinuous toFun
  separators : Set D.carrier
  finite_separators : separators.Finite
  separated : ∀ x : D.carrier, ∃ m ∈ separators, toFun x ≤ m ∧ m ≤ x

/-- Definition 4.2.9, strong separation. PDF text: strong separation means
that for each `x` there are elements `m, m' ∈ M` with
`f x <= m << m' <= x`. -/
structure StronglySeparatedSelfMap (D : OrderedDomain.{u}) where
  toFun : D.carrier → D.carrier
  continuous : Chapter3.ScottContinuous toFun
  separators : Set D.carrier
  finite_separators : separators.Finite
  strongly_separated :
    ∀ x : D.carrier,
      ∃ m ∈ separators, ∃ m' ∈ separators, toFun x ≤ m ∧ Chapter3.WayBelow m m' ∧ m' ≤ x

/-- Definition 4.2.9, FS-domain. PDF text: a pointed dcpo `D` is an FS-domain
if there is a directed collection `(f_i)` of continuous functions on `D`, each
finitely separated from `id_D`, with the identity map as their supremum. -/
structure FSDomain where
  object : OrderedDomain.{u}
  dcpo : Chapter3.IsDcpo object.carrier
  pointed : Chapter3.HasLeastElement object.carrier
  maps : Set (FinitelySeparatedSelfMap object)
  nonempty : maps.Nonempty
  directed :
    ∀ f ∈ maps, ∀ g ∈ maps,
      ∃ h ∈ maps, ∀ x : object.carrier, f.toFun x ≤ h.toFun x ∧ g.toFun x ≤ h.toFun x
  approximates :
    ∀ x : object.carrier,
      Chapter3.IsSup ({y : object.carrier | ∃ f ∈ maps, y = f.toFun x}) x

/-- Pairwise compatibility in an ordered domain. -/
def Compatible {D : OrderedDomain.{u}} (x y : D.carrier) : Prop :=
  ∃ z : D.carrier, x ≤ z ∧ y ≤ z

/-- Coherence: compatible compact elements have a compact common upper bound. -/
structure CoherentDomain where
  object : OrderedDomain.{u}
  compact_compatible :
    ∀ ⦃x y : object.carrier⦄,
      Chapter3.Compact x → Chapter3.Compact y → Compatible x y →
        ∃ z : object.carrier, Chapter3.Compact z ∧ x ≤ z ∧ y ≤ z

/-- Category names appearing in the hierarchy of Chapter 4. -/
inductive CategoryName where
  | DCPO
  | DCPOBot
  | CONT
  | CONTBot
  | ALG
  | ALGBot
  | Bifinite
  | FS
  | Coherent
  | LatticeLike
deriving DecidableEq, Repr

/-- A named inclusion edge in the hierarchy of domain categories. -/
structure CategoryInclusion where
  smaller : CategoryName
  larger : CategoryName

/-- Reflexive inclusions are always available. -/
def CategoryName.reflInclusion (C : CategoryName) : CategoryInclusion where
  smaller := C
  larger := C

end Chapter4
end AbramskyJung

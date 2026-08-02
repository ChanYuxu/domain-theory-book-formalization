import Practice.DomainTheory.Chapter04.Section40_41
import Practice.DomainTheory.Chapter04.Section42
import Practice.DomainTheory.Chapter06.Section61

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Chapter 6.2: powerdomains

This section records the numbered powerdomain items.  Some order-theoretic
lemmas are proved directly, while most representation theorems are represented
as visible proof debt with auxiliary packages or lightweight representation
witnesses.
-/

universe u v w

namespace AbramskyJung
namespace Chapter6

open Chapter4

/-- Finite non-empty subsets, used as bases for the three classical
powerdomains. -/
structure FiniteNonemptySet (α : Type u) where
  carrier : Set α
  finite : carrier.Finite
  nonempty : carrier.Nonempty

/-- Finite non-empty subsets of a specified basis. -/
structure FiniteNonemptySubset {α : Type u} (B : Set α) where
  carrier : Set α
  subset_basis : carrier ⊆ B
  finite : carrier.Finite
  nonempty : carrier.Nonempty

/-- Lower, or Hoare, half of the Egli-Milner relation. -/
def LowerApprox {α : Type u} (R : α → α → Prop) (M N : Set α) : Prop :=
  ∀ a ∈ M, ∃ b ∈ N, R a b

/-- Upper, or Smyth, half of the Egli-Milner relation. -/
def UpperApprox {α : Type u} (R : α → α → Prop) (M N : Set α) : Prop :=
  ∀ b ∈ N, ∃ a ∈ M, R a b

/-- Definition 6.2.2: the Egli-Milner relation between two subsets of a set
equipped with a relation. -/
def EgliMilner {α : Type u} (R : α → α → Prop) (M N : Set α) : Prop :=
  LowerApprox R M N ∧ UpperApprox R M N

/-- The symmetric Egli-Milner equivalence used in Proposition 6.2.5, written
`=EM` in the PDF. -/
def EgliMilnerEquivalent {α : Type u} (R : α → α → Prop)
    (M N : Set α) : Prop :=
  EgliMilner R M N ∧ EgliMilner R N M

/-- Definition 6.2.2: named entry point for the Egli-Milner relation. -/
abbrev def_6_2_2_egli_milner_relation {α : Type u} :
    (α → α → Prop) → Set α → Set α → Prop :=
  EgliMilner

/-- Hoare equivalence induced by a preorder on subsets. -/
def HoareEquivalent {α : Type u} (R : α → α → Prop) (M N : Set α) : Prop :=
  LowerApprox R M N ∧ LowerApprox R N M

/-- Smyth equivalence induced by a preorder on subsets. -/
def SmythEquivalent {α : Type u} (R : α → α → Prop) (M N : Set α) : Prop :=
  UpperApprox R M N ∧ UpperApprox R N M

/-- Ideals for an arbitrary relation, reused by ideal-completion presentations. -/
def RelationLower {α : Type u} (r : α → α → Prop) (I : Set α) : Prop :=
  ∀ ⦃x y : α⦄, y ∈ I → r x y → x ∈ I

/-- Directedness for an arbitrary relation. -/
def RelationDirected {α : Type u} (r : α → α → Prop) (I : Set α) : Prop :=
  I.Nonempty ∧
    ∀ ⦃x : α⦄, x ∈ I → ∀ ⦃y : α⦄, y ∈ I →
      ∃ z ∈ I, r x z ∧ r y z

/-- Ideals for an arbitrary relation. -/
def IsIdealRelation {α : Type u} (r : α → α → Prop) (I : Set α) : Prop :=
  RelationLower r I ∧ RelationDirected r I

/-- A binary formal-union dcpo-algebra satisfying the semilattice equations. -/
structure FormalUnionAlgebra (D : OrderedDomain.{u}) where
  carrier_dcpo : Chapter3.IsDcpo D.carrier
  union : D.carrier → D.carrier → D.carrier
  continuous : Chapter3.ScottContinuous (fun p : D.carrier × D.carrier => union p.1 p.2)
  continuous_left : ∀ y : D.carrier, Chapter3.ScottContinuous (fun x => union x y)
  continuous_right : ∀ x : D.carrier, Chapter3.ScottContinuous (fun y => union x y)
  comm : ∀ x y : D.carrier, union x y = union y x
  assoc : ∀ x y z : D.carrier, union (union x y) z = union x (union y z)
  idem : ∀ x : D.carrier, union x x = x

/-- The single binary operation symbol of the Plotkin powertheory. -/
inductive PlotkinOperation : Type where
  | formalUnion

/-- The signature of the Plotkin powertheory: one binary operation. -/
def plotkinSignature : Signature where
  Op := PlotkinOperation
  arity := fun _ => Fin 2
  arity_finite := by
    intro _o
    infer_instance

/-- The variables used to write the three Plotkin semilattice equations. -/
abbrev PlotkinEquationVar := Fin 3

/-- Formal union as a term former for the Plotkin signature. -/
def plotkinUnionTerm {Var : Type u}
    (x y : Term plotkinSignature Var) : Term plotkinSignature Var :=
  Term.op PlotkinOperation.formalUnion (fun i : Fin 2 => if i = 0 then x else y)

/-- The six inequations representing the three Plotkin equations. -/
inductive PlotkinInequation where
  | comm_le
  | comm_ge
  | assoc_le
  | assoc_ge
  | idem_le
  | idem_ge

/-- Each Plotkin equation is represented as both inequational directions. -/
def PlotkinInequation.toInequation :
    PlotkinInequation → Inequation plotkinSignature PlotkinEquationVar
  | comm_le =>
      { lhs := plotkinUnionTerm (Term.var (0 : PlotkinEquationVar))
          (Term.var (1 : PlotkinEquationVar))
        rhs := plotkinUnionTerm (Term.var (1 : PlotkinEquationVar))
          (Term.var (0 : PlotkinEquationVar)) }
  | comm_ge =>
      { lhs := plotkinUnionTerm (Term.var (1 : PlotkinEquationVar))
          (Term.var (0 : PlotkinEquationVar))
        rhs := plotkinUnionTerm (Term.var (0 : PlotkinEquationVar))
          (Term.var (1 : PlotkinEquationVar)) }
  | assoc_le =>
      { lhs := plotkinUnionTerm
          (plotkinUnionTerm (Term.var (0 : PlotkinEquationVar))
            (Term.var (1 : PlotkinEquationVar)))
          (Term.var (2 : PlotkinEquationVar))
        rhs := plotkinUnionTerm (Term.var (0 : PlotkinEquationVar))
          (plotkinUnionTerm (Term.var (1 : PlotkinEquationVar))
            (Term.var (2 : PlotkinEquationVar))) }
  | assoc_ge =>
      { lhs := plotkinUnionTerm (Term.var (0 : PlotkinEquationVar))
          (plotkinUnionTerm (Term.var (1 : PlotkinEquationVar))
            (Term.var (2 : PlotkinEquationVar)))
        rhs := plotkinUnionTerm
          (plotkinUnionTerm (Term.var (0 : PlotkinEquationVar))
            (Term.var (1 : PlotkinEquationVar)))
          (Term.var (2 : PlotkinEquationVar)) }
  | idem_le =>
      { lhs := plotkinUnionTerm (Term.var (0 : PlotkinEquationVar))
          (Term.var (0 : PlotkinEquationVar))
        rhs := Term.var (0 : PlotkinEquationVar) }
  | idem_ge =>
      { lhs := Term.var (0 : PlotkinEquationVar)
        rhs := plotkinUnionTerm (Term.var (0 : PlotkinEquationVar))
          (Term.var (0 : PlotkinEquationVar)) }

/-- Definition 6.2.1: the convex or Plotkin powertheory, as a signature with
one binary operation and the commutativity, associativity, and idempotence
equations represented inequationally. -/
def plotkinPowertheory : Theory plotkinSignature PlotkinEquationVar where
  inequations :=
    {e : Inequation plotkinSignature PlotkinEquationVar |
      ∃ ax : PlotkinInequation, PlotkinInequation.toInequation ax = e}

/-- Definition 6.2.1: named entry point for the syntactic Plotkin powertheory. -/
abbrev def_6_2_1_plotkin_powertheory :=
  plotkinPowertheory

/-- A dcpo-semilattice model of the Plotkin powertheory on a fixed dcpo. -/
structure PlotkinDcpoSemilattice (D : OrderedDomain.{u}) extends FormalUnionAlgebra D

/-- The Hoare one-sided inequality `x <= x union y`. -/
def hoareInequation : Inequation plotkinSignature PlotkinEquationVar where
  lhs := Term.var (0 : PlotkinEquationVar)
  rhs := plotkinUnionTerm (Term.var (0 : PlotkinEquationVar))
    (Term.var (1 : PlotkinEquationVar))

/-- The Smyth one-sided inequality `x >= x union y`, equivalently
`x union y <= x`. -/
def smythInequation : Inequation plotkinSignature PlotkinEquationVar where
  lhs := plotkinUnionTerm (Term.var (0 : PlotkinEquationVar))
    (Term.var (1 : PlotkinEquationVar))
  rhs := Term.var (0 : PlotkinEquationVar)

/-- The Hoare/lower powertheory: Plotkin plus `x <= x union y`. -/
def hoarePowertheory : Theory plotkinSignature PlotkinEquationVar where
  inequations :=
    {e : Inequation plotkinSignature PlotkinEquationVar |
      e ∈ plotkinPowertheory.inequations ∨ e = hoareInequation}

/-- The Smyth/upper powertheory: Plotkin plus `x >= x union y`. -/
def smythPowertheory : Theory plotkinSignature PlotkinEquationVar where
  inequations :=
    {e : Inequation plotkinSignature PlotkinEquationVar |
      e ∈ plotkinPowertheory.inequations ∨ e = smythInequation}

/-- A basis presentation of a powerdomain as an ideal completion. -/
structure PowerdomainBasisPresentation
    (D : OrderedDomain.{u}) (kind : PowerdomainKind)
    (α : Type u) (rel : α → α → Prop) where
  powerdomain : Powerdomain D
  kind_eq : powerdomain.kind = kind
  ideal_equiv :
    powerdomain.carrier.carrier ≃ {I : Set α // IsIdealRelation rel I}

/-- The Egli-Milner relation on finite non-empty subsets using way-below. -/
def FiniteEgliMilnerApprox {α : Type u} [Preorder α]
    (M N : FiniteNonemptySet α) : Prop :=
  EgliMilner (fun a b : α => Chapter3.WayBelow a b) M.carrier N.carrier

/-- The Egli-Milner relation on finite non-empty subsets of a fixed basis. -/
def BasisFiniteEgliMilnerApprox {α : Type u} [Preorder α] {B : Set α}
    (M N : FiniteNonemptySubset B) : Prop :=
  EgliMilner (fun a b : α => Chapter3.WayBelow a b) M.carrier N.carrier

/-- Theorem 6.2.3.  PDF text: the Plotkin powerdomain of a continuous domain
with basis `B` is the ideal completion of finite subsets ordered by
Egli-Milner approximation.

The ideal-completion representation is registered as local proof debt. -/
theorem theorem_6_2_3_plotkin_powerdomain_continuous
    (D : OrderedDomain.{u}) (B : Set D.carrier)
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hB : Chapter3.IsBasis B) :
    Nonempty
      (PowerdomainBasisPresentation D PowerdomainKind.plotkin
        (FiniteNonemptySubset B) BasisFiniteEgliMilnerApprox) := by
  admit

/-- Definition 6.2.4: convex hull in a preordered set. -/
def ConvexHull {α : Type u} [Preorder α] (M : Set α) : Set α :=
  {a : α | ∃ m ∈ M, ∃ n ∈ M, m ≤ a ∧ a ≤ n}

/-- Definition 6.2.4: a subset is convex when it is equal to its convex hull. -/
def ConvexSet {α : Type u} [Preorder α] (M : Set α) : Prop :=
  ConvexHull M = M

/-- Definition 6.2.4: named entry point for convex hulls and convex subsets. -/
abbrev def_6_2_4_convex_hull {α : Type u} [Preorder α] :
    (Set α → Set α) × (Set α → Prop) :=
  (ConvexHull, ConvexSet)

/-- Finitely generated convex subsets. -/
def FinitelyGeneratedConvexSet {α : Type u} [Preorder α] (C : Set α) : Prop :=
  ∃ M : Set α, M.Finite ∧ C = ConvexHull M

/-- Finitely generated convex subsets generated by compact elements of a domain. -/
def FinitelyGeneratedCompactConvexSet (D : OrderedDomain.{u})
    (C : Set D.carrier) : Prop :=
  ∃ M : Set D.carrier,
    M.Finite ∧ (∀ x ∈ M, Chapter3.Compact x) ∧ C = ConvexHull M

/-- Proposition 6.2.5: convex-hull and Egli-Milner properties in preorders. -/
theorem prop_6_2_5_convex_egli_milner_properties
    {α : Type u} [Preorder α] (M N : Set α) :
    ConvexHull M = Chapter2.upperClosure M ∩ Chapter2.lowerClosure M ∧
      M ⊆ ConvexHull M ∧
      ConvexHull (ConvexHull M) = ConvexHull M ∧
      (M ⊆ N → ConvexHull M ⊆ ConvexHull N) ∧
      EgliMilnerEquivalent (fun x y : α => x ≤ y) M (ConvexHull M) ∧
      (EgliMilnerEquivalent (fun x y : α => x ≤ y) M N ↔
        ConvexHull M = ConvexHull N) := by
  have hSubsetSelf : ∀ A : Set α, A ⊆ ConvexHull A := by
    intro A a ha
    exact ⟨a, ha, a, ha, le_rfl, le_rfl⟩
  have hMonotone :
      ∀ {A B : Set α}, A ⊆ B → ConvexHull A ⊆ ConvexHull B := by
    intro A B hAB a ha
    rcases ha with ⟨m, hm, n, hn, hma, han⟩
    exact ⟨m, hAB hm, n, hAB hn, hma, han⟩
  have hClosureEq :
      ConvexHull M = Chapter2.upperClosure M ∩ Chapter2.lowerClosure M := by
    ext a
    constructor
    · intro ha
      rcases ha with ⟨m, hm, n, hn, hma, han⟩
      exact ⟨⟨m, hm, hma⟩, ⟨n, hn, han⟩⟩
    · intro ha
      rcases ha with ⟨⟨m, hm, hma⟩, ⟨n, hn, han⟩⟩
      exact ⟨m, hm, n, hn, hma, han⟩
  have hIdem : ConvexHull (ConvexHull M) = ConvexHull M := by
    apply Set.Subset.antisymm
    · intro a ha
      rcases ha with ⟨p, hp, q, hq, hpa, haq⟩
      rcases hp with ⟨m, hm, _n, _hn, hmp, _hpn⟩
      rcases hq with ⟨_m, _hm, n, hn, _hmq, hqn⟩
      exact ⟨m, hm, n, hn, le_trans hmp hpa, le_trans haq hqn⟩
    · exact hMonotone (hSubsetSelf M)
  have hEgliSelf : EgliMilner (fun x y : α => x ≤ y) M (ConvexHull M) := by
    constructor
    · intro a ha
      exact ⟨a, hSubsetSelf M ha, le_rfl⟩
    · intro b hb
      rcases hb with ⟨m, hm, _n, _hn, hmb, _hbn⟩
      exact ⟨m, hm, hmb⟩
  have hEgliSelfSymm : EgliMilner (fun x y : α => x ≤ y) (ConvexHull M) M := by
    constructor
    · intro a ha
      rcases ha with ⟨_m, _hm, n, hn, _hma, han⟩
      exact ⟨n, hn, han⟩
    · intro b hb
      exact ⟨b, hSubsetSelf M hb, le_rfl⟩
  have hEgliIff :
      (EgliMilnerEquivalent (fun x y : α => x ≤ y) M N ↔
        ConvexHull M = ConvexHull N) := by
    constructor
    · intro h
      apply Set.Subset.antisymm
      · intro a ha
        rcases ha with ⟨m, hm, n, hn, hma, han⟩
        rcases h.2.2 m hm with ⟨nLo, hnLo, hnLo_le_m⟩
        rcases h.1.1 n hn with ⟨nHi, hnHi, hn_le_nHi⟩
        exact ⟨nLo, hnLo, nHi, hnHi, le_trans hnLo_le_m hma,
          le_trans han hn_le_nHi⟩
      · intro a ha
        rcases ha with ⟨n, hn, n', hn', hna, han'⟩
        rcases h.1.2 n hn with ⟨mLo, hmLo, hmLo_le_n⟩
        rcases h.2.1 n' hn' with ⟨mHi, hmHi, hn'_le_mHi⟩
        exact ⟨mLo, hmLo, mHi, hmHi, le_trans hmLo_le_n hna,
          le_trans han' hn'_le_mHi⟩
    · intro hEq
      constructor
      · constructor
        · intro m hm
          have hmConv : m ∈ ConvexHull N := by
            have hmSelf : m ∈ ConvexHull M := hSubsetSelf M hm
            exact hEq ▸ hmSelf
          rcases hmConv with ⟨_nLo, _hnLo, nHi, hnHi, _hnLo_le_m, hm_le_nHi⟩
          exact ⟨nHi, hnHi, hm_le_nHi⟩
        · intro n hn
          have hnConv : n ∈ ConvexHull M := by
            have hnSelf : n ∈ ConvexHull N := hSubsetSelf N hn
            exact hEq.symm ▸ hnSelf
          rcases hnConv with ⟨mLo, hmLo, _mHi, _hmHi, hmLo_le_n, _hn_le_mHi⟩
          exact ⟨mLo, hmLo, hmLo_le_n⟩
      · constructor
        · intro n hn
          have hnConv : n ∈ ConvexHull M := by
            have hnSelf : n ∈ ConvexHull N := hSubsetSelf N hn
            exact hEq.symm ▸ hnSelf
          rcases hnConv with ⟨_mLo, _hmLo, mHi, hmHi, _hmLo_le_n, hn_le_mHi⟩
          exact ⟨mHi, hmHi, hn_le_mHi⟩
        · intro m hm
          have hmConv : m ∈ ConvexHull N := by
            have hmSelf : m ∈ ConvexHull M := hSubsetSelf M hm
            exact hEq ▸ hmSelf
          rcases hmConv with ⟨nLo, hnLo, _nHi, _hnHi, hnLo_le_m, _hm_le_nHi⟩
          exact ⟨nLo, hnLo, hnLo_le_m⟩
  exact
    ⟨hClosureEq, hSubsetSelf M, hIdem, hMonotone (A := M) (B := N),
      ⟨hEgliSelf, hEgliSelfSymm⟩, hEgliIff⟩

/-- Proposition 6.2.6.  PDF text: for an algebraic domain, the Plotkin
powerdomain is the ideal completion of finitely generated convex compact
subsets with Egli-Milner ordering.

This representation theorem is registered as local proof debt. -/
theorem prop_6_2_6_plotkin_powerdomain_algebraic
    (D : OrderedDomain.{u})
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsAlgebraicDomain D.carrier) :
    Nonempty
      (PowerdomainBasisPresentation D PowerdomainKind.plotkin
        {C : Set D.carrier // FinitelyGeneratedCompactConvexSet D C}
        (fun C E => EgliMilner (fun x y : D.carrier => x ≤ y) C.1 E.1)) := by
  admit

/-- Hoare, or lower, powertheory: formal union is inflationary. -/
structure HoarePowertheory (D : OrderedDomain.{u}) extends FormalUnionAlgebra D where
  inflationary_left : ∀ x y : D.carrier, x ≤ union x y
  inflationary_right : ∀ x y : D.carrier, y ≤ union x y

/-- Smyth, or upper, powertheory: formal union is deflationary. -/
structure SmythPowertheory (D : OrderedDomain.{u}) extends FormalUnionAlgebra D where
  deflationary_left : ∀ x y : D.carrier, union x y ≤ x
  deflationary_right : ∀ x y : D.carrier, union x y ≤ y

/-- Definition 6.2.7: Hoare and Smyth powertheories, represented syntactically
as Plotkin's powertheory augmented by the one-sided inequalities `x <= x ∪ y`
and `x ∪ y <= x`. -/
def def_6_2_7_hoare_smyth_powertheories :
    Theory plotkinSignature PlotkinEquationVar ×
      Theory plotkinSignature PlotkinEquationVar :=
  (hoarePowertheory, smythPowertheory)

/-- Existence of all non-empty suprema. -/
def HasNonemptySuprema (D : OrderedDomain.{u}) : Prop :=
  ∀ A : Set D.carrier, A.Nonempty → ∃ s : D.carrier, Chapter3.IsSup A s

/-- Existence of bounded infima for non-empty sets. -/
def HasBoundedInfima (D : OrderedDomain.{u}) : Prop :=
  ∀ A : Set D.carrier,
    A.Nonempty → (∃ u : D.carrier, Chapter3.IsUpperBound A u) →
      ∃ i : D.carrier, Chapter3.IsInf A i

/-- Existence of binary infima. -/
def HasBinaryInfima (D : OrderedDomain.{u}) : Prop :=
  ∀ x y : D.carrier,
    ∃ z : D.carrier,
      Chapter3.IsInf ({w : D.carrier | w = x ∨ w = y} : Set D.carrier) z

/-- Formal union gives binary suprema in a powerdomain carrier. -/
def FormalUnionBinarySup {D : OrderedDomain.{u}} (P : Powerdomain D) : Prop :=
  ∀ x y : P.carrier.carrier,
    Chapter3.IsSup ({z : P.carrier.carrier | z = x ∨ z = y} : Set P.carrier.carrier)
      (P.unionLike x y)

/-- Formal union gives binary infima in a powerdomain carrier. -/
def FormalUnionBinaryInf {D : OrderedDomain.{u}} (P : Powerdomain D) : Prop :=
  ∀ x y : P.carrier.carrier,
    Chapter3.IsInf ({z : P.carrier.carrier | z = x ∨ z = y} : Set P.carrier.carrier)
      (P.unionLike x y)

/-- Proposition 6.2.8.  PDF text: Hoare powerdomains have non-empty suprema and
bounded infima; Smyth powerdomains have binary infima, with formal union giving
the corresponding binary suprema/infima.

The lattice-property theorem is registered as local proof debt. -/
theorem prop_6_2_8_hoare_smyth_powerdomain_lattice
    (D : OrderedDomain.{u})
    (hDdcpo : Chapter3.IsDcpo D.carrier) :
    (∀ P : Powerdomain D, P.kind = PowerdomainKind.hoare →
      HasNonemptySuprema P.carrier ∧ HasBoundedInfima P.carrier ∧
        FormalUnionBinarySup P) ∧
      (∀ P : Powerdomain D, P.kind = PowerdomainKind.smyth →
        HasBinaryInfima P.carrier ∧ FormalUnionBinaryInf P) := by
  admit

/-- Compatibility alias for the older one-sided name.  The statement covers
both the Hoare and Smyth halves of Proposition 6.2.8. -/
theorem prop_6_2_8_hoare_powerdomain_lattice
    (D : OrderedDomain.{u})
    (hDdcpo : Chapter3.IsDcpo D.carrier) :
    (∀ P : Powerdomain D, P.kind = PowerdomainKind.hoare →
      HasNonemptySuprema P.carrier ∧ HasBoundedInfima P.carrier ∧
        FormalUnionBinarySup P) ∧
      (∀ P : Powerdomain D, P.kind = PowerdomainKind.smyth →
        HasBinaryInfima P.carrier ∧ FormalUnionBinaryInf P) :=
  prop_6_2_8_hoare_smyth_powerdomain_lattice D hDdcpo

/-- Hoare approximation on finite subsets of a basis. -/
def FiniteHoareApprox {α : Type u} [Preorder α]
    (M N : FiniteNonemptySet α) : Prop :=
  LowerApprox (fun a b : α => Chapter3.WayBelow a b) M.carrier N.carrier

/-- Smyth approximation on finite subsets of a basis. -/
def FiniteSmythApprox {α : Type u} [Preorder α]
    (M N : FiniteNonemptySet α) : Prop :=
  UpperApprox (fun a b : α => Chapter3.WayBelow a b) M.carrier N.carrier

/-- Hoare approximation on finite non-empty subsets of a specified basis. -/
def BasisFiniteHoareApprox {α : Type u} [Preorder α] {B : Set α}
    (M N : FiniteNonemptySubset B) : Prop :=
  LowerApprox (fun a b : α => Chapter3.WayBelow a b) M.carrier N.carrier

/-- Smyth approximation on finite non-empty subsets of a specified basis. -/
def BasisFiniteSmythApprox {α : Type u} [Preorder α] {B : Set α}
    (M N : FiniteNonemptySubset B) : Prop :=
  UpperApprox (fun a b : α => Chapter3.WayBelow a b) M.carrier N.carrier

/-- Proposition 6.2.9, definitional form: the finite-basis approximations for
Hoare and Smyth powerdomains are represented by the two halves of
Egli-Milner approximation.  The inequational preorder characterization from
the PDF is not separately constructed. -/
theorem prop_6_2_9_hoare_smyth_finite_basis_approximation
    {α : Type u} [Preorder α] (M N : FiniteNonemptySet α) :
    FiniteHoareApprox M N =
        LowerApprox (fun a b : α => Chapter3.WayBelow a b) M.carrier N.carrier ∧
      FiniteSmythApprox M N =
        UpperApprox (fun a b : α => Chapter3.WayBelow a b) M.carrier N.carrier := by
  constructor <;> rfl

/-- Theorem 6.2.10.  PDF text: Hoare and Smyth powerdomains of a continuous
domain are ideal completions of finite subsets with the corresponding
one-sided approximations.

The Hoare/Smyth ideal-completion representations are registered as local proof
debt. -/
theorem theorem_6_2_10_hoare_smyth_powerdomain_continuous
    (D : OrderedDomain.{u}) (B : Set D.carrier)
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hB : Chapter3.IsBasis B) :
    Nonempty
        (PowerdomainBasisPresentation D PowerdomainKind.hoare
          (FiniteNonemptySubset B) BasisFiniteHoareApprox) ∧
      Nonempty
        (PowerdomainBasisPresentation D PowerdomainKind.smyth
          (FiniteNonemptySubset B) BasisFiniteSmythApprox) := by
  admit

/-- Compatibility alias for the older one-sided name.  The statement covers
both Hoare and Smyth continuous powerdomain presentations. -/
theorem theorem_6_2_10_hoare_powerdomain_continuous
    (D : OrderedDomain.{u}) (B : Set D.carrier)
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hB : Chapter3.IsBasis B) :
    Nonempty
        (PowerdomainBasisPresentation D PowerdomainKind.hoare
          (FiniteNonemptySubset B) BasisFiniteHoareApprox) ∧
      Nonempty
        (PowerdomainBasisPresentation D PowerdomainKind.smyth
          (FiniteNonemptySubset B) BasisFiniteSmythApprox) :=
  theorem_6_2_10_hoare_smyth_powerdomain_continuous D B hDdcpo hB

/-- Proposition 6.2.11: subset approximation facts for Hoare and Smyth
preorders. -/
theorem prop_6_2_11_subset_approximation_preorders
    {α : Type u} [Preorder α] (M N : Set α) :
    HoareEquivalent (fun x y : α => x ≤ y) M (Chapter2.lowerClosure M) ∧
      (LowerApprox (fun x y : α => x ≤ y) M N ↔
        Chapter2.lowerClosure M ⊆ Chapter2.lowerClosure N) ∧
      SmythEquivalent (fun x y : α => x ≤ y) M (Chapter2.upperClosure M) ∧
      (UpperApprox (fun x y : α => x ≤ y) M N ↔
        Chapter2.upperClosure N ⊆ Chapter2.upperClosure M) := by
  constructor
  · constructor
    · intro a ha
      exact ⟨a, ⟨a, ha, le_rfl⟩, le_rfl⟩
    · intro a ha
      rcases ha with ⟨m, hm, ham⟩
      exact ⟨m, hm, ham⟩
  constructor
  · constructor
    · intro h x hx
      rcases hx with ⟨m, hm, hxm⟩
      rcases h m hm with ⟨n, hn, hmn⟩
      exact ⟨n, hn, le_trans hxm hmn⟩
    · intro h a ha
      have haLower : a ∈ Chapter2.lowerClosure M := ⟨a, ha, le_rfl⟩
      exact h haLower
  constructor
  · constructor
    · intro b hb
      rcases hb with ⟨a, ha, hab⟩
      exact ⟨a, ha, hab⟩
    · intro b hb
      exact ⟨b, ⟨b, hb, le_rfl⟩, le_rfl⟩
  · constructor
    · intro h x hx
      rcases hx with ⟨n, hn, hnx⟩
      rcases h n hn with ⟨m, hm, hmn⟩
      exact ⟨m, hm, le_trans hmn hnx⟩
    · intro h b hb
      have hbUpper : b ∈ Chapter2.upperClosure N := ⟨b, hb, le_rfl⟩
      exact h hbUpper

/-- Finitely generated lower subsets. -/
def FinitelyGeneratedLowerSet {α : Type u} [Preorder α] (L : Set α) : Prop :=
  ∃ M : Set α, M.Finite ∧ L = Chapter2.lowerClosure M

/-- Finitely generated upper subsets. -/
def FinitelyGeneratedUpperSet {α : Type u} [Preorder α] (U : Set α) : Prop :=
  ∃ M : Set α, M.Finite ∧ U = Chapter2.upperClosure M

/-- Finitely generated lower subsets generated by compact elements. -/
def FinitelyGeneratedCompactLowerSet (D : OrderedDomain.{u})
    (L : Set D.carrier) : Prop :=
  ∃ M : Set D.carrier,
    M.Finite ∧ (∀ x ∈ M, Chapter3.Compact x) ∧ L = Chapter2.lowerClosure M

/-- Finitely generated upper subsets generated by compact elements. -/
def FinitelyGeneratedCompactUpperSet (D : OrderedDomain.{u})
    (U : Set D.carrier) : Prop :=
  ∃ M : Set D.carrier,
    M.Finite ∧ (∀ x ∈ M, Chapter3.Compact x) ∧ U = Chapter2.upperClosure M

/-- Proposition 6.2.12.  PDF text: algebraic Hoare and Smyth powerdomains are
ideal completions of finitely generated lower and upper compact subsets.

This algebraic representation theorem is registered as local proof debt. -/
theorem prop_6_2_12_hoare_smyth_powerdomain_algebraic
    (D : OrderedDomain.{u})
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsAlgebraicDomain D.carrier) :
    Nonempty
        (PowerdomainBasisPresentation D PowerdomainKind.hoare
          {L : Set D.carrier // FinitelyGeneratedCompactLowerSet D L}
          (fun L M => L.1 ⊆ M.1)) ∧
      Nonempty
        (PowerdomainBasisPresentation D PowerdomainKind.smyth
          {U : Set D.carrier // FinitelyGeneratedCompactUpperSet D U}
          (fun U V => V.1 ⊆ U.1)) := by
  admit

/-- Compatibility alias for the older one-sided name.  The statement covers
both Hoare and Smyth algebraic powerdomain presentations. -/
theorem prop_6_2_12_smyth_powerdomain_algebraic
    (D : OrderedDomain.{u})
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsAlgebraicDomain D.carrier) :
    Nonempty
        (PowerdomainBasisPresentation D PowerdomainKind.hoare
          {L : Set D.carrier // FinitelyGeneratedCompactLowerSet D L}
          (fun L M => L.1 ⊆ M.1)) ∧
      Nonempty
        (PowerdomainBasisPresentation D PowerdomainKind.smyth
          {U : Set D.carrier // FinitelyGeneratedCompactUpperSet D U}
          (fun U V => V.1 ⊆ U.1)) :=
  prop_6_2_12_hoare_smyth_powerdomain_algebraic D hDdcpo hD

/-- Scott-compactness for subsets, phrased by Scott-open covers. -/
def ScottCompactSet (D : OrderedDomain.{u}) (K : Set D.carrier) : Prop :=
  ∀ cover : Set (Set D.carrier),
    (∀ U ∈ cover, Chapter2.ScottOpen U) →
      K ⊆ ⋃₀ cover →
        ∃ finiteCover : Set (Set D.carrier),
          finiteCover.Finite ∧ finiteCover ⊆ cover ∧ K ⊆ ⋃₀ finiteCover

/-- Saturated subsets for the Scott specialization order are upper sets. -/
def SaturatedSet (D : OrderedDomain.{u}) (K : Set D.carrier) : Prop :=
  Chapter2.IsUpperSet K

/-- Non-empty Scott-closed subsets. -/
structure NonemptyScottClosedSet (D : OrderedDomain.{u}) where
  carrier : Set D.carrier
  nonempty : carrier.Nonempty
  scott_closed : Chapter2.ScottClosed carrier

private theorem scottClosed_union
    {D : OrderedDomain.{u}} {C E : Set D.carrier}
    (hC : Chapter2.ScottClosed C) (hE : Chapter2.ScottClosed E) :
    Chapter2.ScottClosed (C ∪ E) := by
  constructor
  · intro x y hy hxy
    rcases hy with hyC | hyE
    · exact Or.inl (hC.1 hyC hxy)
    · exact Or.inr (hE.1 hyE hxy)
  · intro A s hdir hA hs
    by_cases hExists : ∃ a : D.carrier, a ∈ A ∧ a ∉ C
    · rcases hExists with ⟨a, haA, haNotC⟩
      have hAE : A ⊆ E := by
        intro b hbA
        rcases hdir.2 haA hbA with ⟨c, hcA, hac, hbc⟩
        rcases hA hcA with hcC | hcE
        · have haC : a ∈ C := hC.1 hcC hac
          exact False.elim (haNotC haC)
        · exact hE.1 hcE hbc
      exact Or.inr (hE.2 hdir hAE hs)
    · have hAC : A ⊆ C := by
        intro a haA
        by_contra haNotC
        exact hExists ⟨a, haA, haNotC⟩
      exact Or.inl (hC.2 hdir hAC hs)

def nonemptyScottClosedUnion
    (D : OrderedDomain.{u}) (A B : NonemptyScottClosedSet D) :
    NonemptyScottClosedSet D where
  carrier := A.carrier ∪ B.carrier
  nonempty := by
    rcases A.nonempty with ⟨x, hx⟩
    exact ⟨x, Or.inl hx⟩
  scott_closed := scottClosed_union A.scott_closed B.scott_closed

/-- Inclusion order on non-empty Scott-closed subsets, as used by the Hoare
powerdomain representation. -/
def NonemptyScottClosedInclusion
    {D : OrderedDomain.{u}} (A B : NonemptyScottClosedSet D) : Prop :=
  A.carrier ⊆ B.carrier

/-- Non-empty Scott-compact saturated subsets. -/
structure CompactSaturatedSet (D : OrderedDomain.{u}) where
  carrier : Set D.carrier
  nonempty : carrier.Nonempty
  compact : ScottCompactSet D carrier
  saturated : SaturatedSet D carrier

private theorem scottCompact_union
    {D : OrderedDomain.{u}} {A B : Set D.carrier}
    (hA : ScottCompactSet D A) (hB : ScottCompactSet D B) :
    ScottCompactSet D (A ∪ B) := by
  intro cover hOpen hCover
  have hAcover : A ⊆ ⋃₀ cover := by
    intro x hx
    exact hCover (Or.inl hx)
  have hBcover : B ⊆ ⋃₀ cover := by
    intro x hx
    exact hCover (Or.inr hx)
  rcases hA cover hOpen hAcover with ⟨coverA, hcoverAfinite, hcoverAsub, hAcovered⟩
  rcases hB cover hOpen hBcover with ⟨coverB, hcoverBfinite, hcoverBsub, hBcovered⟩
  refine ⟨coverA ∪ coverB, hcoverAfinite.union hcoverBfinite, ?_, ?_⟩
  · intro U hU
    rcases hU with hU | hU
    · exact hcoverAsub hU
    · exact hcoverBsub hU
  · intro x hx
    rcases hx with hxA | hxB
    · rcases hAcovered hxA with ⟨U, hU, hxU⟩
      exact ⟨U, Or.inl hU, hxU⟩
    · rcases hBcovered hxB with ⟨U, hU, hxU⟩
      exact ⟨U, Or.inr hU, hxU⟩

private theorem saturated_union
    {D : OrderedDomain.{u}} {A B : Set D.carrier}
    (hA : SaturatedSet D A) (hB : SaturatedSet D B) :
    SaturatedSet D (A ∪ B) := by
  intro x y hx hxy
  rcases hx with hxA | hxB
  · exact Or.inl (hA hxA hxy)
  · exact Or.inr (hB hxB hxy)

/-- Actual union of non-empty compact saturated subsets. -/
def compactSaturatedUnion
    (D : OrderedDomain.{u}) (A B : CompactSaturatedSet D) :
    CompactSaturatedSet D where
  carrier := A.carrier ∪ B.carrier
  nonempty := by
    rcases A.nonempty with ⟨x, hx⟩
    exact ⟨x, Or.inl hx⟩
  compact := scottCompact_union A.compact B.compact
  saturated := saturated_union A.saturated B.saturated

/-- Reverse inclusion order on compact saturated subsets, as used by the Smyth
powerdomain representation. -/
def CompactSaturatedReverseInclusion
    {D : OrderedDomain.{u}} (A B : CompactSaturatedSet D) : Prop :=
  B.carrier ⊆ A.carrier

/-- A lightweight topological representation of a powerdomain.  It records a
carrier equivalence with the representation type, agreement with the specified
order on the representation, and a concrete formal-union interpretation on the
representation type. -/
structure TopologicalPowerdomainRepresentation
    (D : OrderedDomain.{u}) (kind : PowerdomainKind)
    (Rep : Type u) (order : Rep → Rep → Prop) where
  powerdomain : Powerdomain D
  kind_eq : powerdomain.kind = kind
  equiv : powerdomain.carrier.carrier ≃ Rep
  formal_union : Rep → Rep → Rep
  order_agrees :
    ∀ x y : powerdomain.carrier.carrier, x ≤ y ↔ order (equiv x) (equiv y)
  formal_union_interpretation :
    ∀ x y : powerdomain.carrier.carrier,
      equiv (powerdomain.unionLike x y) = formal_union (equiv x) (equiv y)

/-- A Hoare closed-set representation with the PDF's order and formal-union
semantics fixed explicitly. -/
structure HoareClosedSetRepresentation (D : OrderedDomain.{u}) where
  representation :
    TopologicalPowerdomainRepresentation D PowerdomainKind.hoare
      (NonemptyScottClosedSet D) NonemptyScottClosedInclusion
  formal_union_is_union :
    ∀ A B : NonemptyScottClosedSet D,
      representation.formal_union A B = nonemptyScottClosedUnion D A B

/-- A Smyth compact-saturated representation with the PDF's reverse-inclusion
order and formal-union semantics fixed explicitly. -/
structure SmythCompactSaturatedRepresentation (D : OrderedDomain.{u}) where
  representation :
    TopologicalPowerdomainRepresentation D PowerdomainKind.smyth
      (CompactSaturatedSet D) CompactSaturatedReverseInclusion
  formal_union_is_union :
    ∀ A B : CompactSaturatedSet D,
      representation.formal_union A B = compactSaturatedUnion D A B

/-- Theorem 6.2.13.  PDF text: the Hoare powerdomain of a continuous domain is
the lattice of non-empty Scott-closed subsets ordered by inclusion, and formal
union is actual union.

This representation theorem is registered as local proof debt. -/
theorem theorem_6_2_13_hoare_powerdomain_closed_sets
    (D : OrderedDomain.{u})
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) :
    Nonempty (HoareClosedSetRepresentation D) := by
  admit

/-- Theorem 6.2.14.  PDF text: the Smyth powerdomain of a continuous domain is
represented by non-empty compact saturated subsets ordered by reverse inclusion,
and formal union is actual union.

This representation theorem is registered as local proof debt. -/
theorem theorem_6_2_14_smyth_powerdomain_compact_saturated
    (D : OrderedDomain.{u})
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) :
    Nonempty (SmythCompactSaturatedRepresentation D) := by
  admit

/-- A bc-domain predicate used for the Smyth-powerdomain corollary, reusing
Chapter 4's bc-domain predicate rather than duplicating a weaker local variant. -/
abbrev BcDomain (D : OrderedDomain.{u}) : Prop :=
  Chapter4.IsBcDomain D

/-- Corollary 6.2.15.  PDF text: the Smyth powerdomain of a coherent domain
with bottom is a bc-domain.

This corollary is registered as local proof debt until the Smyth representation
and bc-domain argument are formalized directly. -/
theorem cor_6_2_15_smyth_powerdomain_coherent_bc
    (D : OrderedDomain.{u})
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier)
    (hcoherent : Chapter4.IsCoherentDomain D)
    (hbottom : ∃ bottom : D.carrier, ∀ x : D.carrier, bottom ≤ x) :
    ∀ R : SmythCompactSaturatedRepresentation D,
      BcDomain R.representation.powerdomain.carrier := by
  admit

/-- Scott closure as a set-valued operator. -/
def ScottClosure (D : OrderedDomain.{u}) (A : Set D.carrier) : Set D.carrier :=
  {x : D.carrier | Chapter2.ScottClosureMem A x}

/-- Definition 6.2.16: lenses are non-empty intersections of a Scott-closed set
and a compact saturated set. -/
structure Lens (D : OrderedDomain.{u}) where
  carrier : Set D.carrier
  nonempty : carrier.Nonempty
  closedPart : Set D.carrier
  compactPart : Set D.carrier
  closed_scott : Chapter2.ScottClosed closedPart
  compact_saturated : ScottCompactSet D compactPart ∧ SaturatedSet D compactPart
  eq_inter : carrier = closedPart ∩ compactPart

/-- Definition 6.2.16: topological Egli-Milner ordering on lenses. -/
def TopologicalEgliMilner {D : OrderedDomain.{u}} (K L : Lens D) : Prop :=
  L.carrier ⊆ Chapter2.upperClosure K.carrier ∧
    K.carrier ⊆ ScottClosure D L.carrier

/-- Definition 6.2.16: lenses.  The associated topological Egli-Milner ordering
is defined separately as `TopologicalEgliMilner`. -/
def def_6_2_16_lenses (D : OrderedDomain.{u}) : Type u :=
  Lens D

/-- Order-convex subsets. -/
def OrderConvexSet {α : Type u} [Preorder α] (A : Set α) : Prop :=
  ∀ ⦃x y z : α⦄, x ∈ A → z ∈ A → x ≤ y → y ≤ z → y ∈ A

namespace Lens

/-- The compact saturated component contains the upward closure of a lens. -/
theorem upperClosure_subset_compactPart
    {D : OrderedDomain.{u}} (L : Lens D) :
    Chapter2.upperClosure L.carrier ⊆ L.compactPart := by
  intro x hx
  rcases hx with ⟨y, hy, hyx⟩
  have hyInter : y ∈ L.closedPart ∩ L.compactPart := by
    simpa [L.eq_inter] using hy
  exact L.compact_saturated.2 hyInter.2 hyx

/-- The Scott closure of a lens is contained in its Scott-closed component. -/
theorem scottClosure_subset_closedPart
    {D : OrderedDomain.{u}} (L : Lens D) :
    ScottClosure D L.carrier ⊆ L.closedPart := by
  intro x hx
  exact hx L.closedPart L.closed_scott (by
    intro y hy
    have hyInter : y ∈ L.closedPart ∩ L.compactPart := by
      simpa [L.eq_inter] using hy
    exact hyInter.1)

/-- Every lens is order-convex: the closed part supplies downward closure and
the saturated part supplies upward closure. -/
theorem orderConvex {D : OrderedDomain.{u}} (L : Lens D) :
    OrderConvexSet L.carrier := by
  intro x y z hx hz hxy hyz
  have hxInter : x ∈ L.closedPart ∩ L.compactPart := by
    simpa [L.eq_inter] using hx
  have hzInter : z ∈ L.closedPart ∩ L.compactPart := by
    simpa [L.eq_inter] using hz
  have hyClosed : y ∈ L.closedPart := L.closed_scott.1 hzInter.1 hyz
  have hyCompact : y ∈ L.compactPart := L.compact_saturated.2 hxInter.2 hxy
  simpa [L.eq_inter] using And.intro hyClosed hyCompact

/-- The carrier of a lens is Scott-compact.  A cover of the carrier is extended
by the Scott-open complement of the closed part to cover the compact saturated
part, then the extra open is removed from the finite subcover. -/
theorem scottCompact {D : OrderedDomain.{u}} (L : Lens D) :
    ScottCompactSet D L.carrier := by
  intro cover hOpen hCover
  let augmented : Set (Set D.carrier) := cover ∪ {L.closedPartᶜ}
  have hAugmentedOpen : ∀ U ∈ augmented, Chapter2.ScottOpen U := by
    intro U hU
    rcases hU with hU | hU
    · exact hOpen U hU
    · have hUeq : U = L.closedPartᶜ := by simpa using hU
      simpa [hUeq, Chapter2.ScottOpen] using L.closed_scott
  have hAugmentedCover : L.compactPart ⊆ ⋃₀ augmented := by
    intro x hxCompact
    by_cases hxClosed : x ∈ L.closedPart
    · have hxCarrier : x ∈ L.carrier := by
        simpa [L.eq_inter] using And.intro hxClosed hxCompact
      rcases hCover hxCarrier with ⟨U, hUcover, hxU⟩
      exact ⟨U, Or.inl hUcover, hxU⟩
    · exact ⟨L.closedPartᶜ, Or.inr (by simp), hxClosed⟩
  rcases L.compact_saturated.1 augmented hAugmentedOpen hAugmentedCover with
    ⟨finiteCover, hfiniteCover, hfiniteSub, hfiniteCovers⟩
  refine ⟨finiteCover ∩ cover,
    hfiniteCover.subset (by intro U hU; exact hU.1), ?_, ?_⟩
  · intro U hU
    exact hU.2
  · intro x hxCarrier
    have hxInter : x ∈ L.closedPart ∩ L.compactPart := by
      simpa [L.eq_inter] using hxCarrier
    rcases hfiniteCovers hxInter.2 with ⟨U, hUfinite, hxU⟩
    have hUaugmented : U ∈ augmented := hfiniteSub hUfinite
    rcases hUaugmented with hUcover | hUclosedCompl
    · exact ⟨U, ⟨hUfinite, hUcover⟩, hxU⟩
    · have hUeq : U = L.closedPartᶜ := by simpa using hUclosedCompl
      exact False.elim (by
        have hxNotClosed : x ∉ L.closedPart := by simpa [hUeq] using hxU
        exact hxNotClosed hxInter.1)

/-- A lens is exactly the intersection of the upward closure of its carrier and
the Scott closure of its carrier. -/
theorem carrier_eq_upperClosure_inter_scottClosure
    {D : OrderedDomain.{u}} (L : Lens D) :
    L.carrier = Chapter2.upperClosure L.carrier ∩ ScottClosure D L.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    constructor
    · exact ⟨x, hx, le_rfl⟩
    · intro C hC hLC
      exact hLC hx
  · intro x hx
    have hxClosed : x ∈ L.closedPart := L.scottClosure_subset_closedPart hx.2
    have hxCompact : x ∈ L.compactPart := L.upperClosure_subset_compactPart hx.1
    simpa [L.eq_inter] using And.intro hxClosed hxCompact

/-- Membership criterion obtained from the canonical lens representation. -/
theorem mem_of_upperClosure_and_scottClosure
    {D : OrderedDomain.{u}} {L : Lens D} {x : D.carrier}
    (hUpper : x ∈ Chapter2.upperClosure L.carrier)
    (hClosure : x ∈ ScottClosure D L.carrier) :
    x ∈ L.carrier := by
  have hx : x ∈ Chapter2.upperClosure L.carrier ∩ ScottClosure D L.carrier :=
    ⟨hUpper, hClosure⟩
  rw [L.carrier_eq_upperClosure_inter_scottClosure]
  exact hx

end Lens

/-- Proposition 6.2.17.  PDF text: every lens is convex and Scott-compact, has
canonical representation `↑L ∩ Cl(L)`, and topological Egli-Milner is
antisymmetric.
-/
theorem prop_6_2_17_lens_closure_properties
    (D : OrderedDomain.{u})
    (_hDdcpo : Chapter3.IsDcpo D.carrier) :
    (∀ L : Lens D,
      OrderConvexSet L.carrier ∧
        ScottCompactSet D L.carrier ∧
          L.carrier = Chapter2.upperClosure L.carrier ∩ ScottClosure D L.carrier) ∧
      (∀ K L : Lens D,
        TopologicalEgliMilner K L → TopologicalEgliMilner L K →
          K.carrier = L.carrier) := by
  constructor
  · intro L
    exact ⟨L.orderConvex, L.scottCompact, L.carrier_eq_upperClosure_inter_scottClosure⟩
  · intro K L hKL hLK
    apply Set.Subset.antisymm
    · intro x hxK
      exact Lens.mem_of_upperClosure_and_scottClosure (hLK.1 hxK) (hKL.2 hxK)
    · intro x hxL
      exact Lens.mem_of_upperClosure_and_scottClosure (hKL.1 hxL) (hLK.2 hxL)

/-- The union of all finite sets belonging to an ideal of finite subsets. -/
def IdealUnion (D : OrderedDomain.{u})
    {B : Set D.carrier} (I : Set (FiniteNonemptySubset B)) : Set D.carrier :=
  {x : D.carrier | ∃ M ∈ I, x ∈ M.carrier}

/-- The compact-saturated part generated by a Plotkin ideal. -/
def IdealSmythPart (D : OrderedDomain.{u})
    {B : Set D.carrier} (I : Set (FiniteNonemptySubset B)) : Set D.carrier :=
  {x : D.carrier | ∀ M ∈ I, x ∈ Chapter2.upperClosure M.carrier}

/-- The lens associated with a Plotkin ideal over a chosen basis, by combining
the Hoare and Smyth parts. -/
def PlotkinLensFromIdeal (D : OrderedDomain.{u})
    {B : Set D.carrier} (I : Set (FiniteNonemptySubset B)) : Set D.carrier :=
  ScottClosure D (IdealUnion D I) ∩ IdealSmythPart D I

/-- A set meets every finite set in an ideal. -/
def MeetsEveryIdealElement (D : OrderedDomain.{u})
    {B : Set D.carrier} (A : Set D.carrier)
    (I : Set (FiniteNonemptySubset B)) : Prop :=
  ∀ M ∈ I, ∃ x ∈ A, x ∈ M.carrier

/-- Directed-supremum representation used in Lemma 6.2.18.  An element is
represented as the supremum of a directed subset of the ideal union that meets
every finite set in the ideal. -/
def DirectedSupremumRepresentation (D : OrderedDomain.{u})
    {B : Set D.carrier} (I : Set (FiniteNonemptySubset B)) : Set D.carrier :=
  {x : D.carrier |
    ∃ A : Set D.carrier,
      Chapter3.DirectedSet A ∧ A ⊆ IdealUnion D I ∧
        MeetsEveryIdealElement D A I ∧
          Chapter3.IsSup A x}

/-- Directed-supremum representatives lie in the Scott closure of the ideal
union. -/
theorem directedSupremumRepresentation_subset_scottClosure
    {D : OrderedDomain.{u}} {B : Set D.carrier}
    {I : Set (FiniteNonemptySubset B)} :
    DirectedSupremumRepresentation D I ⊆ ScottClosure D (IdealUnion D I) := by
  intro x hx C hC hUnionC
  rcases hx with ⟨A, hAdir, hAideal, _hmeets, hsup⟩
  exact hC.2 hAdir (fun a ha => hUnionC (hAideal ha)) hsup

/-- Directed-supremum representatives lie in the Smyth component generated by
the same ideal. -/
theorem directedSupremumRepresentation_subset_idealSmythPart
    {D : OrderedDomain.{u}} {B : Set D.carrier}
    {I : Set (FiniteNonemptySubset B)} :
    DirectedSupremumRepresentation D I ⊆ IdealSmythPart D I := by
  intro x hx M hMI
  rcases hx with ⟨A, _hAdir, _hAideal, hmeets, hsup⟩
  rcases hmeets M hMI with ⟨a, haA, haM⟩
  exact ⟨a, haM, hsup.1 haA⟩

/-- One inclusion in Lemma 6.2.18 is purely local: every directed-supremum
representative belongs to the lens generated by the ideal. -/
theorem directedSupremumRepresentation_subset_plotkinLensFromIdeal
    {D : OrderedDomain.{u}} {B : Set D.carrier}
    {I : Set (FiniteNonemptySubset B)} :
    DirectedSupremumRepresentation D I ⊆ PlotkinLensFromIdeal D I := by
  intro x hx
  exact
    ⟨directedSupremumRepresentation_subset_scottClosure hx,
      directedSupremumRepresentation_subset_idealSmythPart hx⟩

/-- Lemma 6.2.18.  PDF text: the lens generated by a Plotkin ideal over a basis
can be represented by directed suprema of sets meeting every ideal element.

This representation lemma is registered as local proof debt. -/
theorem lemma_6_2_18_plotkin_ideal_lens_representation
    (D : OrderedDomain.{u}) (B : Set D.carrier)
    (I : Set (FiniteNonemptySubset B))
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier)
    (hB : Chapter3.IsBasis B)
    (hI :
      IsIdealRelation
        (fun M N : FiniteNonemptySubset B => BasisFiniteEgliMilnerApprox M N) I) :
    PlotkinLensFromIdeal D I = DirectedSupremumRepresentation D I := by
  admit

/-- Omega-continuity as existence of a countable basis. -/
def OmegaContinuousOrderedDomain (D : OrderedDomain.{u}) : Prop :=
  Chapter3.IsDcpo D.carrier ∧ ∃ B : Set D.carrier, B.Countable ∧ Chapter3.IsBasis B

/-- Topological convex closure: upper closure followed by Scott closure, used
for the omega-continuous lens presentation of Plotkin powerdomains. -/
def TopologicalConvexClosure (D : OrderedDomain.{u}) (A : Set D.carrier) :
    Set D.carrier :=
  Chapter2.upperClosure A ∩ ScottClosure D A

/-- Order-theoretic convex closure, used for the coherent-domain lens
presentation of Plotkin powerdomains. -/
def PlainConvexClosure (D : OrderedDomain.{u}) (A : Set D.carrier) :
    Set D.carrier :=
  ConvexHull A

/-- A lightweight lens representation of a powerdomain with a chosen order and
closure operation on lenses.  It records order agreement with the chosen lens
order and that formal union is interpreted as union followed by the chosen
closure operation. -/
structure LensPowerdomainRepresentation
    (D : OrderedDomain.{u}) (kind : PowerdomainKind)
    (order : Lens D → Lens D → Prop)
    (unionClosure : Set D.carrier → Set D.carrier) where
  powerdomain : Powerdomain D
  kind_eq : powerdomain.kind = kind
  equiv : powerdomain.carrier.carrier ≃ Lens D
  order_agrees :
    ∀ x y : powerdomain.carrier.carrier, x ≤ y ↔ order (equiv x) (equiv y)
  formal_union_interpretation :
    ∀ x y : powerdomain.carrier.carrier,
      (equiv (powerdomain.unionLike x y)).carrier =
        unionClosure ((equiv x).carrier ∪ (equiv y).carrier)

/-- Theorem 6.2.19.  PDF text: for an omega-continuous domain, the Plotkin
powerdomain is represented by lenses with topological Egli-Milner order.

This omega-continuous lens representation is registered as local proof debt. -/
theorem theorem_6_2_19_plotkin_powerdomain_omega_lenses
    (D : OrderedDomain.{u})
    (hD : OmegaContinuousOrderedDomain D) :
    Nonempty
      (LensPowerdomainRepresentation D PowerdomainKind.plotkin
        TopologicalEgliMilner (TopologicalConvexClosure D)) := by
  admit

/-- Principal upper set. -/
def PrincipalUpper (D : OrderedDomain.{u}) (x : D.carrier) : Set D.carrier :=
  {y : D.carrier | x ≤ y}

/-- Lawson subbasic opens: Scott opens and complements of principal upper sets. -/
def LawsonSubbasicOpen (D : OrderedDomain.{u}) (U : Set D.carrier) : Prop :=
  Chapter2.ScottOpen U ∨ ∃ x : D.carrier, U = (PrincipalUpper D x)ᶜ

/-- Lawson-open subsets generated from the standard subbasis. -/
def LawsonOpen (D : OrderedDomain.{u}) (U : Set D.carrier) : Prop :=
  ∀ x ∈ U,
    ∃ F : Set (Set D.carrier),
      F.Finite ∧ (∀ V ∈ F, LawsonSubbasicOpen D V) ∧
        x ∈ ⋂₀ F ∧ ⋂₀ F ⊆ U

/-- Lawson-compact subsets, using Lawson-open covers. -/
def LawsonCompactSet (D : OrderedDomain.{u}) (K : Set D.carrier) : Prop :=
  ∀ cover : Set (Set D.carrier),
    (∀ U ∈ cover, LawsonOpen D U) →
      K ⊆ ⋃₀ cover →
        ∃ finiteCover : Set (Set D.carrier),
          finiteCover.Finite ∧ finiteCover ⊆ cover ∧ K ⊆ ⋃₀ finiteCover

/-- Each Lawson subbasic open is Lawson-open for the generated topology. -/
theorem lawsonOpen_of_subbasic
    {D : OrderedDomain.{u}} {U : Set D.carrier}
    (hU : LawsonSubbasicOpen D U) : LawsonOpen D U := by
  intro x hx
  refine ⟨{U}, Set.finite_singleton U, ?_, ?_, ?_⟩
  · intro V hV
    have hVU : V = U := by simpa using hV
    simpa [hVU] using hU
  · intro V hV
    have hVU : V = U := by simpa using hV
    simpa [hVU] using hx
  · intro y hy
    exact hy U (by simp)

/-- Complements of principal upper sets are Lawson-open. -/
theorem principalUpper_compl_lawsonOpen
    (D : OrderedDomain.{u}) (x : D.carrier) :
    LawsonOpen D ((PrincipalUpper D x)ᶜ) :=
  lawsonOpen_of_subbasic (Or.inr ⟨x, rfl⟩)

/-- Lemma 6.2.20.  PDF text: Lawson-compact lower closures in continuous domains
are Scott-closed.

This topological lemma is registered as local proof debt. -/
theorem lemma_6_2_20_lawson_compact_lower_scott_closed
    (D : OrderedDomain.{u}) (L : Set D.carrier)
    (_hDdcpo : Chapter3.IsDcpo D.carrier)
    (_hD : Chapter3.IsContinuousDomain D.carrier)
    (hL : LawsonCompactSet D L) :
    Chapter2.ScottClosed (Chapter2.lowerClosure L) := by
  constructor
  · intro x y hy hxy
    rcases hy with ⟨l, hlL, hyl⟩
    exact ⟨l, hlL, le_trans hxy hyl⟩
  · intro A s hAdir hAsub hs
    by_contra hsLower
    let cover : Set (Set D.carrier) :=
      {U | ∃ a ∈ A, U = (PrincipalUpper D a)ᶜ}
    have hCoverOpen : ∀ U ∈ cover, LawsonOpen D U := by
      intro U hU
      rcases hU with ⟨a, _haA, rfl⟩
      exact principalUpper_compl_lawsonOpen D a
    have hCoverL : L ⊆ ⋃₀ cover := by
      intro l hlL
      have hNotUpper : ¬ Chapter3.IsUpperBound A l := by
        intro hUpper
        exact hsLower ⟨l, hlL, hs.2 l hUpper⟩
      have hExists : ∃ a ∈ A, ¬ a ≤ l := by
        by_contra hNone
        exact hNotUpper (by
          intro a haA
          by_contra haNotLe
          exact hNone ⟨a, haA, haNotLe⟩)
      rcases hExists with ⟨a, haA, haNotLe⟩
      exact ⟨(PrincipalUpper D a)ᶜ, ⟨a, haA, rfl⟩, haNotLe⟩
    rcases hL cover hCoverOpen hCoverL with
      ⟨finiteCover, hfiniteCover, hfiniteSub, hfiniteCovers⟩
    letI : Fintype {U : Set D.carrier // U ∈ finiteCover} :=
      Set.Finite.fintype hfiniteCover
    let rep : {U : Set D.carrier // U ∈ finiteCover} → D.carrier :=
      fun U => Classical.choose (hfiniteSub U.2)
    have hrep_spec :
        ∀ U : {U : Set D.carrier // U ∈ finiteCover},
          rep U ∈ A ∧ U.1 = (PrincipalUpper D (rep U))ᶜ := by
      intro U
      exact Classical.choose_spec (hfiniteSub U.2)
    let indices : Set D.carrier := Set.range rep
    have hindicesFin : indices.Finite := Set.finite_range rep
    have hindicesSub : indices ⊆ A := by
      intro a ha
      rcases ha with ⟨U, rfl⟩
      exact (hrep_spec U).1
    rcases Chapter2.DirectedSet.exists_upper_finite hAdir hindicesFin hindicesSub with
      ⟨a₀, ha₀A, ha₀Upper⟩
    rcases hAsub ha₀A with ⟨l₀, hl₀L, ha₀l₀⟩
    rcases hfiniteCovers hl₀L with ⟨U, hUfinite, hl₀U⟩
    let Usub : {U : Set D.carrier // U ∈ finiteCover} := ⟨U, hUfinite⟩
    have hRepLea₀ : rep Usub ≤ a₀ :=
      ha₀Upper (rep Usub) ⟨Usub, rfl⟩
    have hRepL₀ : rep Usub ≤ l₀ := le_trans hRepLea₀ ha₀l₀
    have hUnot : ¬ rep Usub ≤ l₀ := by
      have hUeq : U = (PrincipalUpper D (rep Usub))ᶜ := (hrep_spec Usub).2
      simpa [hUeq, PrincipalUpper] using hl₀U
    exact hUnot hRepL₀

/-- Scott-open sets are Lawson-open subbasic opens. -/
theorem scottOpen_lawsonOpen
    {D : OrderedDomain.{u}} {U : Set D.carrier}
    (hU : Chapter2.ScottOpen U) : LawsonOpen D U :=
  lawsonOpen_of_subbasic (Or.inl hU)

/-- Upward closure preserves compactness from Lawson-compact sets to
Scott-compact saturated sets. -/
theorem upperClosure_scottCompact_of_lawsonCompact
    (D : OrderedDomain.{u}) {A : Set D.carrier}
    (hA : LawsonCompactSet D A) :
    ScottCompactSet D (Chapter2.upperClosure A) := by
  intro cover hOpen hCover
  have hLawsonOpen : ∀ U ∈ cover, LawsonOpen D U := by
    intro U hU
    exact scottOpen_lawsonOpen (hOpen U hU)
  have hCoverA : A ⊆ ⋃₀ cover := by
    intro a ha
    exact hCover ⟨a, ha, le_rfl⟩
  rcases hA cover hLawsonOpen hCoverA with
    ⟨finiteCover, hfiniteCover, hfiniteSub, hfiniteCoversA⟩
  refine ⟨finiteCover, hfiniteCover, hfiniteSub, ?_⟩
  intro y hy
  rcases hy with ⟨a, haA, hay⟩
  rcases hfiniteCoversA haA with ⟨U, hUfinite, haU⟩
  exact ⟨U, hUfinite, Chapter2.scottOpen_upper (hOpen U (hfiniteSub hUfinite)) haU hay⟩

/-- Upward closures are saturated. -/
theorem upperClosure_saturated
    (D : OrderedDomain.{u}) (A : Set D.carrier) :
    SaturatedSet D (Chapter2.upperClosure A) := by
  intro x y hx hxy
  rcases hx with ⟨a, haA, hax⟩
  exact ⟨a, haA, le_trans hax hxy⟩

/-- A non-empty order-convex Lawson-compact set carries the lens structure
whose closed and compact-saturated parts are respectively its lower and upper
closures.  This is the constructive direction used by Corollary 6.2.21. -/
theorem convexLawsonCompactSet_exists_lens
    (D : OrderedDomain.{u}) (A : Set D.carrier)
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier)
    (hAne : A.Nonempty)
    (hConvex : OrderConvexSet A)
    (hCompact : LawsonCompactSet D A) :
    ∃ L : Lens D, L.carrier = A := by
  refine ⟨{
    carrier := A
    nonempty := hAne
    closedPart := Chapter2.lowerClosure A
    compactPart := Chapter2.upperClosure A
    closed_scott := lemma_6_2_20_lawson_compact_lower_scott_closed D A hDdcpo hD hCompact
    compact_saturated :=
      ⟨upperClosure_scottCompact_of_lawsonCompact D hCompact,
        upperClosure_saturated D A⟩
    eq_inter := ?_
  }, rfl⟩
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨⟨x, hx, le_rfl⟩, ⟨x, hx, le_rfl⟩⟩
  · intro x hx
    rcases hx.1 with ⟨hi, hhiA, hxhi⟩
    rcases hx.2 with ⟨lo, hloA, hlox⟩
    exact hConvex hloA hhiA hlox hxhi

/-- Coherence predicate for continuous dcpos, reusing Chapter 4 Section 4.2's
compact-saturated intersection formulation. -/
def IsCoherentOrderedDomain (D : OrderedDomain.{u}) : Prop :=
  Chapter3.IsDcpo D.carrier ∧
    Chapter3.IsContinuousDomain D.carrier ∧
      Chapter4.IsCoherentDomain D

/-- Plain Egli-Milner order on lenses. -/
def LensEgliMilner {D : OrderedDomain.{u}} (K L : Lens D) : Prop :=
  EgliMilner (fun x y : D.carrier => x ≤ y) K.carrier L.carrier

/-- Topological Egli-Milner comparison immediately contains the upper
one-sided approximation from ordinary Egli-Milner. -/
theorem topologicalEgliMilner_upperApprox
    {D : OrderedDomain.{u}} {K L : Lens D}
    (h : TopologicalEgliMilner K L) :
    UpperApprox (fun x y : D.carrier => x ≤ y) K.carrier L.carrier := by
  intro y hyL
  exact h.1 hyL

/-- Ordinary Egli-Milner comparison implies the topological Egli-Milner
comparison.  The reverse implication is the coherence-sensitive part of
Corollary 6.2.21. -/
theorem lensEgliMilner_topologicalEgliMilner
    {D : OrderedDomain.{u}} {K L : Lens D}
    (h : LensEgliMilner K L) :
    TopologicalEgliMilner K L := by
  constructor
  · intro y hyL
    rcases h.2 y hyL with ⟨x, hxK, hxy⟩
    exact ⟨x, hxK, hxy⟩
  · intro x hxK C hC hLC
    rcases h.1 x hxK with ⟨y, hyL, hxy⟩
    exact hC.1 (hLC hyL) hxy

/-- Ordinary Egli-Milner equivalence is antisymmetric on lens carriers, via the
canonical topological representation of lenses. -/
theorem lensEgliMilner_equiv_carrier_eq
    {D : OrderedDomain.{u}} {K L : Lens D}
    (hKL : LensEgliMilner K L) (hLK : LensEgliMilner L K) :
    K.carrier = L.carrier := by
  have hTopKL : TopologicalEgliMilner K L :=
    lensEgliMilner_topologicalEgliMilner hKL
  have hTopLK : TopologicalEgliMilner L K :=
    lensEgliMilner_topologicalEgliMilner hLK
  apply Set.Subset.antisymm
  · intro x hxK
    exact Lens.mem_of_upperClosure_and_scottClosure (hTopLK.1 hxK) (hTopKL.2 hxK)
  · intro x hxL
    exact Lens.mem_of_upperClosure_and_scottClosure (hTopKL.1 hxL) (hTopLK.2 hxL)

/-- Corollary 6.2.21.  PDF text: in coherent domains, lenses are precisely
convex Lawson-compact subsets, and topological and ordinary Egli-Milner orders
agree.

This characterization is registered as local proof debt. -/
theorem cor_6_2_21_lenses_convex_lawson_compact
    (D : OrderedDomain.{u}) (hD : IsCoherentOrderedDomain D) :
    (∀ A : Set D.carrier,
      (∃ L : Lens D, L.carrier = A) ↔
        A.Nonempty ∧ OrderConvexSet A ∧ LawsonCompactSet D A) ∧
      (∀ K L : Lens D,
        TopologicalEgliMilner K L ↔ LensEgliMilner K L) := by
  admit

/-- Theorem 6.2.22.  PDF text: for a coherent domain, the Plotkin powerdomain is
represented by lenses with ordinary Egli-Milner order.

This coherent-domain lens representation is registered as local proof debt. -/
theorem theorem_6_2_22_plotkin_powerdomain_lenses
    (D : OrderedDomain.{u}) (hD : IsCoherentOrderedDomain D) :
    Nonempty
      (LensPowerdomainRepresentation D PowerdomainKind.plotkin LensEgliMilner
        (PlainConvexClosure D)) := by
  admit

end Chapter6
end AbramskyJung

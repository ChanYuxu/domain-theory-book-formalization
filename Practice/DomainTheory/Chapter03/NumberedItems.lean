import Practice.DomainTheory.Chapter03.Section31_Retractions
import Practice.DomainTheory.Chapter03.Section31_Adjunctions
import Practice.DomainTheory.Chapter03.Section31_EmbeddingProjection
import Practice.DomainTheory.Chapter03.Section32_Products
import Practice.DomainTheory.Chapter03.Section32_FunctionSpace
import Practice.DomainTheory.Chapter03.Section32_SumsSmashLifting
import Practice.DomainTheory.Chapter03.Section33_Diagrams
import Practice.DomainTheory.Chapter03.Section33_ExpandingSequences
import Practice.DomainTheory.Chapter03.CategoryNames

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 3 numbered-item coverage

This file supplies declarations for numbered Chapter 3 items whose detailed
formalization is not yet present in the split section files.  Some categorical
items are currently lightweight interfaces rather than full category-theoretic
universal properties; the per-item semantic-strength audit is tracked in
`formalization_status.md`.
-/

universe u v w z l

namespace AbramskyJung
namespace Chapter3

/-- Lemma 3.1.3: the retraction image of a basis along a continuous s-r-pair is a basis. -/
theorem lemma_3_1_3_retraction_image_basis
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (sr : ContinuousSectionRetractionPair D E) {B : Set E}
    (hB : IsBasis B) : IsBasis (sr.r '' B) := by
  apply Chapter2.prop_2_2_4_1
  intro x
  let A : Set E := Approximants B (sr.s x)
  refine ⟨sr.r '' A, ?_, ?_, ?_⟩
  · intro y hy
    rcases hy with ⟨b, hb, rfl⟩
    refine ⟨⟨b, hb.1, rfl⟩, ?_⟩
    intro C s hC hs hxs
    have hImageDir : DirectedSet (sr.s '' C) :=
      DirectedSet.image sr.continuous_s.1 hC
    have hImageSup : IsSup (sr.s '' C) (sr.s s) :=
      sr.continuous_s.2 hC hs
    have hsx : sr.s x ≤ sr.s s := sr.continuous_s.1 hxs
    rcases hb.2 hImageDir hImageSup hsx with ⟨c', hc', hbc'⟩
    rcases hc' with ⟨c, hc, rfl⟩
    refine ⟨c, hc, ?_⟩
    calc
      sr.r b ≤ sr.r (sr.s c) := sr.continuous_r.1 hbc'
      _ = c := sr.retract c
  · exact DirectedSet.image sr.continuous_r.1 (hB (sr.s x)).1
  · have hsup : IsSup (sr.r '' A) (sr.r (sr.s x)) :=
      sr.continuous_r.2 (hB (sr.s x)).1 (hB (sr.s x)).2
    simpa [A, sr.retract x] using hsup

/-- Basis component of Theorem 3.1.4, retained for preorder-valued downstream
lemmas that carry directed completeness and antisymmetry separately. -/
theorem theorem_3_1_4_retract_continuous_domain_basis
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (sr : ContinuousSectionRetractionPair D E)
    (hE : IsContinuousDomain E) : IsContinuousDomain D := by
  rcases hE with ⟨B, hB⟩
  exact ⟨sr.r '' B, lemma_3_1_3_retraction_image_basis sr hB⟩

/-- Theorem 3.1.4: a continuous retract of a continuous dcpo is a continuous
dcpo.  The conclusion includes directed completeness and antisymmetry, as in
the book's definition of a domain. -/
theorem theorem_3_1_4_retract_continuous_domain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (sr : ContinuousSectionRetractionPair D E)
    (hE : Chapter2.IsContinuousDcpo E) : Chapter2.IsContinuousDcpo D := by
  refine ⟨⟨sr.toSectionRetractionPair.isDcpo_of_isDcpo hE.1.1, ?_⟩, ?_⟩
  · intro x y hxy hyx
    have hsxy : sr.s x ≤ sr.s y := sr.continuous_s.1 hxy
    have hsyx : sr.s y ≤ sr.s x := sr.continuous_s.1 hyx
    have hs : sr.s x = sr.s y := hE.1.2 _ _ hsxy hsyx
    calc
      x = sr.r (sr.s x) := (sr.retract x).symm
      _ = sr.r (sr.s y) := congrArg sr.r hs
      _ = y := sr.retract y
  · rcases hE.2 with ⟨B, hB⟩
    rcases theorem_3_1_4_retract_continuous_domain_basis sr
        ⟨B, Chapter2.prop_2_2_4_1 hB⟩ with ⟨C, hC⟩
    exact ⟨C, Chapter2.basis_to_raw hC⟩

/-- Theorem 3.1.4, dcpo-domain form: a continuous retract of a continuous dcpo
inherits both the dcpo structure and the basis-continuity predicate. -/
theorem theorem_3_1_4_retract_continuous_domain_with_dcpo
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (sr : ContinuousSectionRetractionPair D E)
    (hEdcpo : IsDcpo E) (hE : IsContinuousDomain E) :
    IsDcpo D ∧ IsContinuousDomain D :=
  ⟨sr.toSectionRetractionPair.isDcpo_of_isDcpo hEdcpo,
    theorem_3_1_4_retract_continuous_domain_basis sr hE⟩

/-- Proposition 3.1.6 support: a concrete basis, ordered by the inherited order,
is a reflexive abstract basis.  This is the `B` in the PDF's `Idl(B, ⊑)`. -/
def basisOrderAbstractBasis {D : Type u} [Preorder D] (Basis : Set D) :
    Chapter2.AbstractBasis.{u} where
  carrier := Basis
  rel x y := (x : D) ≤ y
  trans := by
    intro x y z hxy hyz
    exact le_trans hxy hyz
  interpolation := by
    intro x M _hM hMx
    exact ⟨x, hMx, le_rfl⟩

/-- Proposition 3.1.6 support: the ideal completion `Idl(B, ⊑)` of a concrete
basis ordered by the inherited order. -/
abbrev BasisOrderIdeal {D : Type u} [Preorder D] (Basis : Set D) : Type u :=
  (basisOrderAbstractBasis Basis).Ideal

/-- Proposition 3.1.6 support: the set of underlying domain points represented
by an ideal of the inherited-order basis. -/
def basisOrderIdealValues {D : Type u} [Preorder D] {Basis : Set D}
    (I : BasisOrderIdeal Basis) : Set D :=
  {x | ∃ b : (basisOrderAbstractBasis Basis).carrier, b ∈ I.1 ∧ x = b.1}

/-- Proposition 3.1.6 support: values of a basis ideal form a directed subset of
the original domain. -/
theorem basisOrderIdealValues_directed
    {D : Type u} [Preorder D] {Basis : Set D} (I : BasisOrderIdeal Basis) :
    DirectedSet (basisOrderIdealValues I) := by
  constructor
  · rcases I.property.2.1 with ⟨b, hb⟩
    exact ⟨b.1, ⟨b, hb, rfl⟩⟩
  · intro x hx y hy
    rcases hx with ⟨b, hbI, rfl⟩
    rcases hy with ⟨c, hcI, rfl⟩
    rcases I.property.2.2 hbI hcI with ⟨d, hdI, hbd, hcd⟩
    exact ⟨d.1, ⟨d, hdI, rfl⟩,
      by simpa [basisOrderAbstractBasis] using hbd,
      by simpa [basisOrderAbstractBasis] using hcd⟩

/-- Proposition 3.1.6 support: the section `s x = B_x` into `Idl(B, ⊑)`. -/
def basisIdealSection
    {D : Type u} [Preorder D] {Basis : Set D} (hBasis : IsBasis Basis) (x : D) :
    BasisOrderIdeal Basis where
  val := {b : (basisOrderAbstractBasis Basis).carrier | b.1 ≪ x}
  property := by
    constructor
    · intro b c hc hbc
      exact Chapter2.prop_2_2_2_2 (by simpa [basisOrderAbstractBasis] using hbc) hc le_rfl
    · constructor
      · rcases (hBasis x).1.1 with ⟨b, hb⟩
        exact ⟨⟨b, hb.1⟩, hb.2⟩
      · intro b hb c hc
        have hbApp : b.1 ∈ Approximants Basis x := by
          exact ⟨b.2, hb⟩
        have hcApp : c.1 ∈ Approximants Basis x := by
          exact ⟨c.2, hc⟩
        rcases (hBasis x).1.2 hbApp hcApp with ⟨d, hdApp, hbd, hcd⟩
        exact ⟨⟨d, hdApp.1⟩, hdApp.2, hbd, hcd⟩

/-- Proposition 3.1.6 support: the retraction `r A = sup A` from `Idl(B, ⊑)`
back to the original dcpo. -/
noncomputable def basisIdealRetraction
    {D : Type u} [Preorder D] {Basis : Set D} (hDdcpo : IsDcpo D)
    (I : BasisOrderIdeal Basis) : D :=
  Classical.choose (hDdcpo (basisOrderIdealValues I) (basisOrderIdealValues_directed I))

/-- Proposition 3.1.6 support: `basisIdealRetraction` is the supremum of the
underlying basis elements in the ideal. -/
theorem basisIdealRetraction_isSup
    {D : Type u} [Preorder D] {Basis : Set D} (hDdcpo : IsDcpo D)
    (I : BasisOrderIdeal Basis) :
    IsSup (basisOrderIdealValues I) (basisIdealRetraction hDdcpo I) :=
  Classical.choose_spec (hDdcpo (basisOrderIdealValues I) (basisOrderIdealValues_directed I))

/-- Proposition 3.1.6 support: the section `x ↦ B_x` is monotone. -/
theorem basisIdealSection_monotone
    {D : Type u} [Preorder D] {Basis : Set D} (hBasis : IsBasis Basis) :
    Monotone (basisIdealSection hBasis) := by
  intro x y hxy b hb
  exact Chapter2.prop_2_2_2_2 le_rfl hb hxy

/-- Proposition 3.1.6 support: the supremum retraction is monotone. -/
theorem basisIdealRetraction_monotone
    {D : Type u} [Preorder D] {Basis : Set D} (hDdcpo : IsDcpo D) :
    Monotone (basisIdealRetraction (Basis := Basis) hDdcpo) := by
  intro I J hIJ
  exact (basisIdealRetraction_isSup hDdcpo I).2 (basisIdealRetraction hDdcpo J) (by
    intro x hx
    rcases hx with ⟨b, hbI, rfl⟩
    exact (basisIdealRetraction_isSup hDdcpo J).1 ⟨b, hIJ hbI, rfl⟩)

/-- Proposition 3.1.6 support: `r (s x) = x`. -/
theorem basisIdeal_retract
    {D : Type u} [PartialOrder D] {Basis : Set D} (hDdcpo : IsDcpo D)
    (hBasis : IsBasis Basis) :
    ∀ x : D, basisIdealRetraction hDdcpo (basisIdealSection hBasis x) = x := by
  intro x
  apply IsSup.unique (basisIdealRetraction_isSup hDdcpo (basisIdealSection hBasis x))
  constructor
  · intro y hy
    rcases hy with ⟨b, hb, rfl⟩
    exact Chapter2.prop_2_2_2_1 hb
  · intro y hy
    exact (hBasis x).2.2 y (by
      intro b hb
      exact hy ⟨⟨b, hb.1⟩, hb.2, rfl⟩)

/-- Proposition 3.1.6 support: `x ↦ B_x` is Scott-continuous. -/
theorem basisIdealSection_scottContinuous
    {D : Type u} [Preorder D] {Basis : Set D} (hBasis : IsBasis Basis) :
    ScottContinuous (basisIdealSection hBasis) := by
  constructor
  · exact basisIdealSection_monotone hBasis
  · intro A x hA hx
    constructor
    · intro I hI
      rcases hI with ⟨a, haA, rfl⟩
      exact basisIdealSection_monotone hBasis (hx.1 haA)
    · intro Y hY b hb
      have hcont : Chapter2.IsContinuousDomain D :=
        ⟨Basis, Chapter2.basis_to_raw hBasis⟩
      rcases Chapter2.cor_2_2_16_wayBelow_directed_sup hcont hA hx hb with
        ⟨a, haA, hba⟩
      exact hY ⟨a, haA, rfl⟩ hba

/-- Proposition 3.1.6 support: `A ↦ sup A` is Scott-continuous. -/
theorem basisIdealRetraction_scottContinuous
    {D : Type u} [Preorder D] {Basis : Set D} (hDdcpo : IsDcpo D) :
    ScottContinuous (basisIdealRetraction (Basis := Basis) hDdcpo) := by
  constructor
  · exact basisIdealRetraction_monotone hDdcpo
  · intro A S hA hS
    constructor
    · intro x hx
      rcases hx with ⟨I, hIA, rfl⟩
      exact basisIdealRetraction_monotone hDdcpo (hS.1 hIA)
    · intro y hy
      exact (basisIdealRetraction_isSup hDdcpo S).2 y (by
        intro x hx
        rcases hx with ⟨b, hbS, rfl⟩
        let U : BasisOrderIdeal Basis :=
          ⟨{b : (basisOrderAbstractBasis Basis).carrier | ∃ I ∈ A, b ∈ I.1},
            (basisOrderAbstractBasis Basis).directedUnionIdeal hA⟩
        have hUupper : IsUpperBound A U := by
          intro I hIA b hbI
          exact ⟨I, hIA, hbI⟩
        have hSU : S ≤ U := hS.2 U hUupper
        rcases hSU hbS with ⟨I, hIA, hbI⟩
        have hb_le_rI : b.1 ≤ basisIdealRetraction hDdcpo I :=
          (basisIdealRetraction_isSup hDdcpo I).1 ⟨b, hbI, rfl⟩
        exact le_trans hb_le_rI (hy ⟨I, hIA, rfl⟩))

/-- Proposition 3.1.6 support: the concrete `Idl(B, ⊑)` construction forms a
continuous section-retraction pair. -/
noncomputable def basisIdealContinuousSectionRetractionPair
    {D : Type u} [PartialOrder D] {Basis : Set D}
    (hDdcpo : IsDcpo D) (hBasis : IsBasis Basis) :
    ContinuousSectionRetractionPair D (BasisOrderIdeal Basis) where
  s := basisIdealSection hBasis
  r := basisIdealRetraction hDdcpo
  monotone_s := basisIdealSection_monotone hBasis
  monotone_r := basisIdealRetraction_monotone hDdcpo
  retract := basisIdeal_retract hDdcpo hBasis
  continuous_s := basisIdealSection_scottContinuous hBasis
  continuous_r := basisIdealRetraction_scottContinuous hDdcpo

/-- Proposition 3.1.6 support: `Idl(B, ⊑)` is a dcpo. -/
theorem basisOrderIdeal_isDcpo {D : Type u} [Preorder D] (Basis : Set D) :
    IsDcpo (BasisOrderIdeal Basis) :=
  (basisOrderAbstractBasis Basis).prop_2_2_22_1_ideal_completion_dcpo

/-- Proposition 3.1.6 support: `Idl(B, ⊑)` is algebraic because the inherited
order on `B` is reflexive. -/
theorem basisOrderIdeal_isAlgebraic {D : Type u} [Preorder D] (Basis : Set D) :
    IsAlgebraicDomain (BasisOrderIdeal Basis) :=
  Chapter2.prop_2_2_4_1
    ((basisOrderAbstractBasis Basis).prop_2_2_22_4_reflexive_ideal_completion_algebraic
      (by intro x; exact le_rfl))

/-- Proposition 3.1.6 omega support: when `B` is countable, the compact
elements of `Idl(B, ⊑)` are countable.  Chapter 2 identifies the compact
elements of a reflexive poset-basis ideal completion with the basis elements. -/
theorem basisOrderIdeal_compactSet_countable
    {D : Type u} [PartialOrder D] {Basis : Set D} (hBcount : Basis.Countable) :
    (@Chapter2.CompactSet (BasisOrderIdeal Basis) inferInstance).Countable := by
  haveI : Countable (basisOrderAbstractBasis Basis).carrier := hBcount.to_subtype
  have hantisymm :
      ∀ ⦃x y : (basisOrderAbstractBasis Basis).carrier⦄,
        (basisOrderAbstractBasis Basis).rel x y →
          (basisOrderAbstractBasis Basis).rel y x → x = y := by
    intro x y hxy hyx
    exact Subtype.ext (le_antisymm
      (by simpa [basisOrderAbstractBasis] using hxy)
      (by simpa [basisOrderAbstractBasis] using hyx))
  rcases (basisOrderAbstractBasis Basis).prop_2_2_22_5_poset_compacts
      (by intro x; exact le_rfl) hantisymm with ⟨e⟩
  exact Countable.of_equiv (basisOrderAbstractBasis Basis).carrier e

/-- Proposition 3.1.6 omega support: `Idl(B, ⊑)` is omega-algebraic when `B`
is countable. -/
theorem basisOrderIdeal_isOmegaAlgebraic
    {D : Type u} [PartialOrder D] {Basis : Set D} (hBcount : Basis.Countable) :
    Chapter2.IsOmegaAlgebraicDomain (BasisOrderIdeal Basis) :=
  ⟨basisOrderIdeal_compactSet_countable hBcount,
    Chapter2.basis_to_raw (basisOrderIdeal_isAlgebraic Basis)⟩

/-- Proposition 3.1.6, concrete package: the PDF maps `x ↦ B_x` and
`A ↦ sup A` give a continuous s-r-pair between `D` and `Idl(B, ⊑)`. -/
theorem prop_3_1_6_basis_ideal_section_retraction_concrete
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D) {Basis : Set D}
    (hBasis : IsBasis Basis) :
    IsDcpo (BasisOrderIdeal Basis) ∧
      IsAlgebraicDomain (BasisOrderIdeal Basis) ∧
        Nonempty (ContinuousSectionRetractionPair D (BasisOrderIdeal Basis)) :=
  ⟨basisOrderIdeal_isDcpo Basis, basisOrderIdeal_isAlgebraic Basis,
    ⟨basisIdealContinuousSectionRetractionPair hDdcpo hBasis⟩⟩

/-- Theorem 3.1.5, continuous branch.

PDF: "Every (ω-) continuous domain is the retract of an (ω-) algebraic domain
via a continuous s-r-pair."

This declaration records the continuous/algebraic branch over the PDF's
explicit domain context.  The target dcpo proof is stated separately from
algebraicity because the local algebraicity predicate is a compact-basis
predicate.  The proof uses Proposition 3.1.6's concrete `Idl(B, ⊑)` maps. -/
theorem theorem_3_1_5_continuous_retract_of_algebraic
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D) (hD : IsContinuousDomain D) :
    ∃ (E : Type u), ∃ (inst : Preorder E),
      @IsDcpo E inst ∧ @IsAlgebraicDomain E inst ∧
        Nonempty (@ContinuousSectionRetractionPair D E _ inst) := by
  rcases hD with ⟨Basis, hBasis⟩
  refine ⟨BasisOrderIdeal Basis, inferInstance, ?_⟩
  exact prop_3_1_6_basis_ideal_section_retraction_concrete hDdcpo hBasis

/-- Theorem 3.1.5, omega branch.

PDF: "Every (ω-) continuous domain is the retract of an (ω-) algebraic domain
via a continuous s-r-pair."

This is the omega-continuous/omega-algebraic branch of the book statement,
proved from the same concrete `Idl(B, ⊑)` construction as the continuous branch.
The target dcpo proof is explicit for the same reason as in the continuous
branch. -/
theorem theorem_3_1_5_omega_continuous_retract_of_omega_algebraic
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D)
    (hD : Chapter2.IsOmegaContinuousDomain D) :
    ∃ (E : Type u), ∃ (inst : Preorder E),
      @IsDcpo E inst ∧ @Chapter2.IsOmegaAlgebraicDomain E inst ∧
        Nonempty (@ContinuousSectionRetractionPair D E _ inst) := by
  rcases hD with ⟨Basis, hBcount, hBraw⟩
  have hBasis : IsBasis Basis := Chapter2.prop_2_2_4_1 hBraw
  refine ⟨BasisOrderIdeal Basis, inferInstance, ?_⟩
  exact ⟨basisOrderIdeal_isDcpo Basis,
    basisOrderIdeal_isOmegaAlgebraic hBcount,
    ⟨basisIdealContinuousSectionRetractionPair hDdcpo hBasis⟩⟩

/-- Proposition 3.1.6 audit predicate.

The PDF constructs concrete maps `x ↦ B_x` and `A ↦ sup A` between `D` and the
ideal completion `Idl(B, ⊑)`.  The Lean predicate now names exactly that
completion and the concrete continuous s-r-pair package above. -/
def HasBasisIdealCompletionRetraction
    {D : Type u} [PartialOrder D] (_hDdcpo : IsDcpo D) (Basis : Set D) : Prop :=
  IsDcpo (BasisOrderIdeal Basis) ∧
    IsAlgebraicDomain (BasisOrderIdeal Basis) ∧
      Nonempty (ContinuousSectionRetractionPair D (BasisOrderIdeal Basis))

/-- Proposition 3.1.6: a basis yields the concrete `Idl(B, ⊑)` continuous
section-retraction pair from the PDF. -/
theorem prop_3_1_6_basis_ideal_section_retraction
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D) {B : Set D} (hB : IsBasis B)
    : HasBasisIdealCompletionRetraction hDdcpo B := by
  exact prop_3_1_6_basis_ideal_section_retraction_concrete hDdcpo hB

/-- Ambient Scott opens restricted to the image of an idempotent.  This is the
subspace topology side of Proposition 3.1.8. -/
def IsIdempotentImageSubspaceOpen
    {D : Type u} [Preorder D] (e : ContinuousIdempotent D)
    (U : Set (ContinuousIdempotent.ImageCarrier e)) : Prop :=
  ∃ V : Set D, Chapter2.ScottOpen V ∧ U = {x | x.1 ∈ V}

/-- One direction of Proposition 3.1.8: every Scott-open set in the image of a
continuous idempotent is induced by a Scott-open set of the ambient domain. -/
theorem prop_3_1_8_scott_open_to_subspace_open
    {D : Type u} [Preorder D] (e : ContinuousIdempotent D)
    (U : Set (ContinuousIdempotent.ImageCarrier e))
    (hU : Chapter2.ScottOpen U) :
    IsIdempotentImageSubspaceOpen e U := by
  let g : D → ContinuousIdempotent.ImageCarrier e :=
    fun x => ⟨e.f x, ⟨x, rfl⟩⟩
  have hg : ScottContinuous g := by
    constructor
    · intro x y hxy
      exact e.continuous.1 hxy
    · intro A s hA hs
      constructor
      · intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        exact e.continuous.1 (hs.1 ha)
      · intro y hy
        exact (e.continuous.2 hA hs).2 y.1 (by
          intro z hz
          rcases hz with ⟨a, ha, rfl⟩
          exact hy ⟨a, ha, rfl⟩)
  refine ⟨{x : D | g x ∈ U}, Chapter2.prop_2_3_4_forward hg U hU, ?_⟩
  ext x
  have hxFixed : e.f x.1 = x.1 := (e.mem_range_iff_fixed).1 x.2
  have hgx : g x.1 = x := by
    apply Subtype.ext
    exact hxFixed
  constructor
  · intro hx
    change g x.1 ∈ U
    simpa [hgx] using hx
  · intro hx
    change g x.1 ∈ U at hx
    simpa [hgx] using hx

/-- Proposition 3.1.8. PDF text: "If f is a continuous idempotent function on a
dcpo D then the Scott-topology on im(f) is the restriction of the Scott-topology
on D to im(f)."

Lean spelling: a subset of the image carrier is Scott-open iff it is the
restriction of an ambient Scott-open set.  The reverse direction uses
Scott-continuity of the image inclusion from Proposition 3.1.7. -/
theorem prop_3_1_8_idempotent_image_scott_topology
    {D : Type u} [PartialOrder D] (hD : IsDcpo D) (e : ContinuousIdempotent D) :
    ∀ U : Set (ContinuousIdempotent.ImageCarrier e),
      Chapter2.ScottOpen U ↔ IsIdempotentImageSubspaceOpen e U := by
  intro U
  constructor
  · exact prop_3_1_8_scott_open_to_subspace_open e U
  · intro hU
    rcases hU with ⟨V, hV, rfl⟩
    exact Chapter2.prop_2_3_4_forward (e.inclusion_scottContinuous hD) V hV

/-- Definition 3.1.9: preliminary adjunction by least elements of inverse upper sets. -/
structure PreliminaryAdjunction
    {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]
    (l : P → Q) (u : Q → P) : Prop where
  monotone_l : Monotone l
  monotone_u : Monotone u
  lower_mem : ∀ x : P, x ≤ u (l x)
  lower_is_least_preimage_upper :
    ∀ x : P, IsInf ({y : Q | x ≤ u y} : Set Q) (l x)

/-- Proposition 3.1.10, form (2): the upper adjoint is the greatest element of
the inverse lower set. -/
structure UpperPreliminaryAdjunction
    {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]
    (l : P → Q) (u : Q → P) : Prop where
  monotone_l : Monotone l
  monotone_u : Monotone u
  upper_mem : ∀ y : Q, l (u y) ≤ y
  upper_is_greatest_preimage_lower :
    ∀ y : Q, IsSup ({x : P | l x ≤ y} : Set P) (u y)

/-- Proposition 3.1.10, form (3): the unit/counit inequalities plus monotonicity. -/
structure UnitCounitAdjunction
    {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]
    (l : P → Q) (u : Q → P) : Prop where
  monotone_l : Monotone l
  monotone_u : Monotone u
  unit : ∀ x : P, x ≤ u (l x)
  counit : ∀ y : Q, l (u y) ≤ y

/-- Proposition 3.1.10: the preliminary least-preimage form, the dual
greatest-preimage form, the unit/counit form, and the official adjunction
equivalence are equivalent. -/
theorem prop_3_1_10_adjunction_equivalent_forms
    {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]
    {l : P → Q} {u : Q → P} :
    (PreliminaryAdjunction l u ↔ Adjunction l u) ∧
      (UpperPreliminaryAdjunction l u ↔ Adjunction l u) ∧
        (UnitCounitAdjunction l u ↔ Adjunction l u) := by
  constructor
  · constructor
    · intro h
      constructor
      intro x y
      constructor
      · intro hxy
        exact (h.lower_is_least_preimage_upper x).1 hxy
      · intro hlxy
        exact le_trans (h.lower_mem x) (h.monotone_u hlxy)
    · intro h
      exact {
        monotone_l := Adjunction.monotone_l h
        monotone_u := Adjunction.monotone_u h
        lower_mem := fun x => Adjunction.unit h x
        lower_is_least_preimage_upper := by
          intro x
          constructor
          · intro y hy
            exact (h.adj x y).1 hy
          · intro z hz
            exact hz (a := l x) (Adjunction.unit h x)
      }
  · constructor
    · constructor
      · intro h
        constructor
        intro x y
        constructor
        · intro hxy
          exact le_trans (h.monotone_l hxy) (h.upper_mem y)
        · intro hlxy
          exact (h.upper_is_greatest_preimage_lower y).1 hlxy
      · intro h
        exact {
          monotone_l := Adjunction.monotone_l h
          monotone_u := Adjunction.monotone_u h
          upper_mem := fun y => Adjunction.counit h y
          upper_is_greatest_preimage_lower := by
            intro y
            constructor
            · intro x hx
              exact (h.adj x y).2 hx
            · intro z hz
              exact hz (a := u y) (Adjunction.counit h y)
        }
    · constructor
      · intro h
        exact adjunction_of_unit_counit h.monotone_l h.monotone_u h.unit h.counit
      · intro h
        exact {
          monotone_l := Adjunction.monotone_l h
          monotone_u := Adjunction.monotone_u h
          unit := fun x => Adjunction.unit h x
          counit := fun y => Adjunction.counit h y
        }

/-- A monotone map preserves all existing infima. -/
def PreservesAllInfima
    {L : Type u} {P : Type v} [Preorder L] [Preorder P] (f : L → P) : Prop :=
  ∀ A : Set L, ∀ s : L, IsInf A s → IsInf (f '' A) (f s)

/-- A map has a lower adjoint. -/
def HasLowerAdjoint
    {L : Type u} {P : Type v} [Preorder L] [Preorder P] (f : L → P) : Prop :=
  ∃ g : P → L, Adjunction g f

/-- Proposition 3.1.13: complete-lattice adjoint criterion for monotone maps. -/
theorem prop_3_1_13_complete_lattice_adjoint_criterion
    {L : Type u} {P : Type v} [CompleteLattice L] [Preorder P]
    (f : L → P) (hf : Monotone f) :
    PreservesAllInfima f ↔ HasLowerAdjoint f := by
  constructor
  · intro hpres
    let g : P → L := fun y => sInf ({x : L | y ≤ f x} : Set L)
    refine ⟨g, ?_⟩
    constructor
    intro y x
    constructor
    · intro hyfx
      exact sInf_le hyfx
    · intro hgx
      let A : Set L := {z : L | y ≤ f z}
      have hginf : IsInf A (g y) := by
        constructor
        · intro a ha
          exact sInf_le ha
        · intro z hz
          exact le_sInf (by
            intro a ha
            exact hz ha)
      have hfinf : IsInf (f '' A) (f (g y)) := hpres A (g y) hginf
      have hyLower : IsLowerBound (f '' A) y := by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact ha
      exact le_trans (hfinf.2 y hyLower) (hf hgx)
  · intro h
    rcases h with ⟨g, hg⟩
    intro A s hs
    exact has_lower_adjoint_preserves_inf hg hs

/-- Proposition 3.1.13, dual criterion: a monotone map out of a complete
lattice preserves all suprema iff it has an upper adjoint. -/
theorem prop_3_1_13_complete_lattice_upper_adjoint_criterion
    {L : Type u} {P : Type v} [CompleteLattice L] [Preorder P]
    (f : L → P) (hf : Monotone f) :
    PreservesAllSuprema f ↔ HasUpperAdjoint f := by
  constructor
  · intro hpres
    let g : P → L := fun y => sSup ({x : L | f x ≤ y} : Set L)
    refine ⟨g, ?_⟩
    constructor
    intro x y
    constructor
    · intro hxg
      let A : Set L := {z : L | f z ≤ y}
      have hgsup : IsSup A (g y) := by
        constructor
        · intro a ha
          exact le_sSup ha
        · intro z hz
          exact sSup_le (by
            intro a ha
            exact hz ha)
      have hfsup : IsSup (f '' A) (f (g y)) := hpres A (g y) hgsup
      have hyUpper : IsUpperBound (f '' A) y := by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact ha
      exact le_trans (hf hxg) (hfsup.2 y hyUpper)
    · intro hfxy
      exact le_sSup hfxy
  · intro h
    rcases h with ⟨g, hg⟩
    intro A s hs
    exact has_upper_adjoint_preserves_sup hg hs

/-- A subset is closed under directed suprema calculated in the ambient dcpo. -/
def IsDirectedSupClosed
    {D : Type u} [Preorder D] (A : Set D) : Prop :=
  ∀ B : Set D, B ⊆ A → DirectedSet B →
    ∀ s : D, IsSup B s → s ∈ A

/-- Proposition 3.1.18 raw closure-operator interface: monotone idempotents
above the identity, matching the PDF premise before any Scott-continuity
assumption is added. -/
structure RawClosureOperator (D : Type u) [Preorder D] where
  c : D → D
  monotone : Monotone c
  idem : ∀ x : D, c (c x) = c x
  above : ∀ x : D, x ≤ c x

namespace RawClosureOperator

/-- The image of a raw closure operator. -/
def ImageCarrier
    {D : Type u} [Preorder D] (c : RawClosureOperator D) : Type u :=
  {x : D // x ∈ Set.range c.c}

instance imageCarrierPreorder
    {D : Type u} [Preorder D] (c : RawClosureOperator D) :
    Preorder (ImageCarrier c) where
  le x y := x.1 ≤ y.1
  le_refl x := le_rfl
  le_trans x y z hxy hyz := le_trans hxy hyz

/-- Fixed-point characterization of the image of a raw closure operator. -/
theorem mem_range_iff_fixed {D : Type u} [Preorder D] (c : RawClosureOperator D)
    {y : D} : y ∈ Set.range c.c ↔ c.c y = y := by
  constructor
  · intro hy
    rcases hy with ⟨x, rfl⟩
    exact c.idem x
  · intro hy
    exact ⟨y, hy⟩

/-- For a raw closure operator, `c x` is the least image element above `x`. -/
theorem closure_le_of_le_mem_range {D : Type u} [Preorder D] (c : RawClosureOperator D)
    {x y : D} (hy : y ∈ Set.range c.c) (hxy : x ≤ y) : c.c x ≤ y := by
  have hfix : c.c y = y := (c.mem_range_iff_fixed).1 hy
  calc
    c.c x ≤ c.c y := c.monotone hxy
    _ = y := hfix

/-- The inclusion of a raw closure image into its ambient carrier. -/
def inclusion
    {D : Type u} [Preorder D] (c : RawClosureOperator D) :
    ImageCarrier c → D :=
  fun x => x.1

/-- The raw closure map corestricted to its image. -/
def projection
    {D : Type u} [Preorder D] (c : RawClosureOperator D) :
    D → ImageCarrier c :=
  fun x => ⟨c.c x, ⟨x, rfl⟩⟩

/-- Suprema in a directed-sup-closed raw closure image coincide with ambient
suprema. -/
theorem image_isSup_iff_ambient_isSup_of_closed
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D)
    (c : RawClosureOperator D) (hClosed : IsDirectedSupClosed (Set.range c.c))
    {A : Set (ImageCarrier c)} {s : ImageCarrier c}
    (hA : DirectedSet A) :
    IsSup A s ↔ IsSup (c.inclusion '' A) (c.inclusion s) := by
  constructor
  · intro hs
    have hImageDirected : DirectedSet (c.inclusion '' A) :=
      DirectedSet.image (by intro x y hxy; exact hxy) hA
    rcases hDdcpo (c.inclusion '' A) hImageDirected with ⟨t, ht⟩
    have htMem : t ∈ Set.range c.c := by
      exact hClosed (c.inclusion '' A) (by
        intro z hz
        rcases hz with ⟨a, _ha, rfl⟩
        exact a.2) hImageDirected t ht
    let tImage : ImageCarrier c := ⟨t, htMem⟩
    have hst : s ≤ tImage := hs.2 tImage (by
      intro a ha
      exact ht.1 ⟨a, ha, rfl⟩)
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact hs.1 ha
    · intro y hy
      exact le_trans hst (ht.2 y hy)
  · intro hs
    constructor
    · intro a ha
      exact hs.1 ⟨a, ha, rfl⟩
    · intro y hy
      exact hs.2 y.1 (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hy ha)

/-- If the raw closure image is closed under ambient directed suprema, then the
image carrier is a dcpo with the inherited order. -/
theorem image_isDcpo_of_directedSupClosed
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D)
    (c : RawClosureOperator D) (hClosed : IsDirectedSupClosed (Set.range c.c)) :
    IsDcpo (ImageCarrier c) := by
  intro A hA
  have hImageDirected : DirectedSet (c.inclusion '' A) :=
    DirectedSet.image (by intro x y hxy; exact hxy) hA
  rcases hDdcpo (c.inclusion '' A) hImageDirected with ⟨s, hs⟩
  have hsMem : s ∈ Set.range c.c := by
    exact hClosed (c.inclusion '' A) (by
      intro z hz
      rcases hz with ⟨a, _ha, rfl⟩
      exact a.2) hImageDirected s hs
  let sImage : ImageCarrier c := ⟨s, hsMem⟩
  exact ⟨sImage, (c.image_isSup_iff_ambient_isSup_of_closed hDdcpo hClosed hA).2 hs⟩

/-- A compact ambient element remains compact after applying a raw closure
operator, provided the image is closed under directed suprema. -/
theorem image_compact_of_ambient_compact
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D)
    (c : RawClosureOperator D) (hClosed : IsDirectedSupClosed (Set.range c.c))
    {k : D} (hk : Compact k) :
    Compact (c.projection k) := by
  intro A s hA hs hle
  have hAmbSup :
      IsSup (c.inclusion '' A) (c.inclusion s) :=
    (c.image_isSup_iff_ambient_isSup_of_closed hDdcpo hClosed hA).1 hs
  have hk_le_s : k ≤ c.inclusion s := le_trans (c.above k) hle
  rcases hk (DirectedSet.image (by intro x y hxy; exact hxy) hA) hAmbSup hk_le_s with
    ⟨a, ha, hka⟩
  rcases ha with ⟨aImage, haImage, rfl⟩
  exact ⟨aImage, haImage, c.closure_le_of_le_mem_range aImage.2 hka⟩

/-- Proposition 3.1.18 raw backward direction: if the image of a monotone
idempotent above the identity is closed under directed suprema, then ambient
compact approximants close up to compact image approximants. -/
theorem image_algebraic_of_directedSupClosed
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D)
    (hAlg : IsAlgebraicDomain D) (c : RawClosureOperator D)
    (hClosed : IsDirectedSupClosed (Set.range c.c)) :
    IsAlgebraicDomain (ImageCarrier c) := by
  apply Chapter2.prop_2_2_4_1
  intro x
  let A : Set (ImageCarrier c) :=
    {y | ∃ k : D, k ∈ (Chapter2.CompactSet : Set D) ∧ k ≪ x.1 ∧
      y = c.projection k}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro y hy
    rcases hy with ⟨k, hkCompact, hkx, rfl⟩
    have hCompactImage : Compact (c.projection k) :=
      c.image_compact_of_ambient_compact hDdcpo hClosed hkCompact
    have hImageLe : c.projection k ≤ x :=
      c.closure_le_of_le_mem_range x.2 (Chapter2.prop_2_2_2_1 hkx)
    constructor
    · exact hCompactImage
    · exact Chapter2.prop_2_2_2_2 le_rfl hCompactImage hImageLe
  · have hAmbientDir : DirectedSet (Chapter2.Approximants (Chapter2.CompactSet : Set D) x.1) :=
      (hAlg x.1).1
    constructor
    · rcases hAmbientDir.1 with ⟨k, hk⟩
      exact ⟨c.projection k, k, hk.1, hk.2, rfl⟩
    · intro y hy z hz
      rcases hy with ⟨k, hkCompact, hkx, rfl⟩
      rcases hz with ⟨l, hlCompact, hlx, rfl⟩
      rcases hAmbientDir.2 ⟨hkCompact, hkx⟩ ⟨hlCompact, hlx⟩ with
        ⟨m, hm, hkm, hlm⟩
      refine ⟨c.projection m, ?_, ?_, ?_⟩
      · exact ⟨m, hm.1, hm.2, rfl⟩
      · exact c.monotone hkm
      · exact c.monotone hlm
  · constructor
    · intro y hy
      rcases hy with ⟨k, hkCompact, hkx, rfl⟩
      exact c.closure_le_of_le_mem_range x.2 (Chapter2.prop_2_2_2_1 hkx)
    · intro y hy
      have hAmbientUpper :
          IsUpperBound (Chapter2.Approximants (Chapter2.CompactSet : Set D) x.1) y.1 := by
        intro k hk
        have hA : c.projection k ∈ A := ⟨k, hk.1, hk.2, rfl⟩
        exact le_trans (c.above k) (hy hA)
      exact (hAlg x.1).2.2 y.1 hAmbientUpper

/-- Proposition 3.1.18 image-domain target: the raw closure image is an
algebraic subdomain of the ambient algebraic domain, with directed suprema
inherited from the ambient dcpo.  This is stronger than merely saying that the
subtype has some internal algebraic-domain structure; it is the inherited-image
reading used by the PDF statement. -/
def ImageAlgebraicSubdomain
    {D : Type u} [PartialOrder D] (c : RawClosureOperator D) : Prop :=
  IsDirectedSupClosed (Set.range c.c) ∧
    IsDcpo (ImageCarrier c) ∧ IsAlgebraicDomain (ImageCarrier c)

/-- Proposition 3.1.18, raw PDF-premise form: for a monotone idempotent
`c ≥ id` on an algebraic dcpo, the image is an algebraic subdomain exactly when
it is closed under directed suprema inherited from the ambient dcpo. -/
theorem imageAlgebraicSubdomain_iff_directedSupClosed
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D)
    (hAlg : IsAlgebraicDomain D) (c : RawClosureOperator D) :
    c.ImageAlgebraicSubdomain ↔ IsDirectedSupClosed (Set.range c.c) := by
  constructor
  · intro h
    exact h.1
  · intro hClosed
    exact ⟨hClosed, c.image_isDcpo_of_directedSupClosed hDdcpo hClosed,
      c.image_algebraic_of_directedSupClosed hDdcpo hAlg hClosed⟩

/-- Raw converse support for Proposition 3.1.18.  The missing bridge between
the image's internal algebraic-domain basis and ambient directed suprema is
made explicit: directed suprema computed in the image carrier must remain
ambient suprema after inclusion. -/
theorem directedSupClosed_range_of_image_algebraic_of_sup_agrees
    {D : Type u} [PartialOrder D] (c : RawClosureOperator D)
    (hImageAlg : IsAlgebraicDomain (ImageCarrier c))
    (hSupAgrees :
      ∀ {A : Set (ImageCarrier c)} {s : ImageCarrier c},
        DirectedSet A → IsSup A s → IsSup (c.inclusion '' A) (c.inclusion s)) :
    IsDirectedSupClosed (Set.range c.c) := by
  intro B hBsub hBdir s hs
  let x : ImageCarrier c := c.projection s
  let Bimg : Set (ImageCarrier c) := {y | y.1 ∈ B}
  have hBimgDir : DirectedSet Bimg := by
    constructor
    · rcases hBdir.1 with ⟨b, hb⟩
      exact ⟨⟨b, hBsub hb⟩, hb⟩
    · intro y hy z hz
      rcases hBdir.2 hy hz with ⟨w, hw, hyw, hzw⟩
      exact ⟨⟨w, hBsub hw⟩, hw, hyw, hzw⟩
  have hBimgSup : IsSup Bimg x := by
    constructor
    · intro y hy
      change y.1 ≤ c.c s
      exact le_trans (hs.1 (by simpa [Bimg] using hy)) (c.above s)
    · intro y hy
      exact c.closure_le_of_le_mem_range y.2 (hs.2 y.1 (by
        intro b hb
        have hbimg : (⟨b, hBsub hb⟩ : ImageCarrier c) ∈ Bimg := by
          simpa [Bimg] using hb
        exact hy (a := (⟨b, hBsub hb⟩ : ImageCarrier c)) hbimg))
  have hImageBasis : IsBasis (Chapter2.CompactSet : Set (ImageCarrier c)) :=
    by simpa [IsAlgebraicDomain, Chapter2.CompactSet] using hImageAlg
  have hApproxSup :
      IsSup (Chapter2.Approximants (Chapter2.CompactSet : Set (ImageCarrier c)) x) x :=
    (hImageBasis x).2
  have hApproxDir :
      DirectedSet (Chapter2.Approximants (Chapter2.CompactSet : Set (ImageCarrier c)) x) :=
    (hImageBasis x).1
  have hAmbientApproxSup :
      IsSup
        (c.inclusion '' Chapter2.Approximants (Chapter2.CompactSet : Set (ImageCarrier c)) x)
        (c.c s) :=
    hSupAgrees hApproxDir hApproxSup
  have hApproxUpperByS :
      IsUpperBound
        (c.inclusion '' Chapter2.Approximants (Chapter2.CompactSet : Set (ImageCarrier c)) x)
        s := by
    intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    rcases ha with ⟨_haCompact, haWayBelow⟩
    rcases haWayBelow hBimgDir hBimgSup le_rfl with ⟨b, hbBimg, hab⟩
    exact le_trans hab (hs.1 hbBimg)
  have hcs_le_s : c.c s ≤ s := hAmbientApproxSup.2 s hApproxUpperByS
  exact ⟨s, le_antisymm hcs_le_s (c.above s)⟩

end RawClosureOperator

/-- A Scott-continuous closure operator is a raw closure operator. -/
def ClosureOperator.toRaw
    {D : Type u} [Preorder D] (c : ClosureOperator D) : RawClosureOperator D where
  c := c.c
  monotone := c.continuous.1
  idem := c.idem
  above := c.above

/-- The image of a closure operator. -/
def ClosureOperator.ImageCarrier
    {D : Type u} [Preorder D] (c : ClosureOperator D) : Type u :=
  {x : D // x ∈ Set.range c.c}

instance ClosureOperator.imageCarrierPreorder
    {D : Type u} [Preorder D] (c : ClosureOperator D) :
    Preorder (ClosureOperator.ImageCarrier c) where
  le x y := x.1 ≤ y.1
  le_refl x := le_rfl
  le_trans x y z hxy hyz := le_trans hxy hyz

/-- The inclusion of a closure image into its ambient carrier. -/
def ClosureOperator.inclusion
    {D : Type u} [Preorder D] (c : ClosureOperator D) :
    ClosureOperator.ImageCarrier c → D :=
  fun x => x.1

/-- The closure map corestricted to its image. -/
def ClosureOperator.projection
    {D : Type u} [Preorder D] (c : ClosureOperator D) :
    D → ClosureOperator.ImageCarrier c :=
  fun x => ⟨c.c x, ⟨x, rfl⟩⟩

/-- Suprema in a directed-sup-closed closure image coincide with ambient
suprema. -/
theorem ClosureOperator.image_isSup_iff_ambient_isSup_of_closed
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D)
    (c : ClosureOperator D) (hClosed : IsDirectedSupClosed (Set.range c.c))
    {A : Set (ClosureOperator.ImageCarrier c)} {s : ClosureOperator.ImageCarrier c}
    (hA : DirectedSet A) :
    IsSup A s ↔ IsSup (c.inclusion '' A) (c.inclusion s) := by
  constructor
  · intro hs
    have hImageDirected : DirectedSet (c.inclusion '' A) :=
      DirectedSet.image (by intro x y hxy; exact hxy) hA
    rcases hDdcpo (c.inclusion '' A) hImageDirected with ⟨t, ht⟩
    have htMem : t ∈ Set.range c.c := by
      exact hClosed (c.inclusion '' A) (by
        intro z hz
        rcases hz with ⟨a, _ha, rfl⟩
        exact a.2) hImageDirected t ht
    let tImage : ClosureOperator.ImageCarrier c := ⟨t, htMem⟩
    have hst : s ≤ tImage := hs.2 tImage (by
      intro a ha
      exact ht.1 ⟨a, ha, rfl⟩)
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact hs.1 ha
    · intro y hy
      exact le_trans hst (ht.2 y hy)
  · intro hs
    constructor
    · intro a ha
      exact hs.1 ⟨a, ha, rfl⟩
    · intro y hy
      exact hs.2 y.1 (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hy ha)

/-- A compact ambient element remains compact after applying a closure operator,
provided the image is closed under directed suprema. -/
theorem ClosureOperator.image_compact_of_ambient_compact
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D)
    (c : ClosureOperator D) (hClosed : IsDirectedSupClosed (Set.range c.c))
    {k : D} (hk : Compact k) :
    Compact (c.projection k) := by
  intro A s hA hs hle
  have hAmbSup :
      IsSup (c.inclusion '' A) (c.inclusion s) :=
    (c.image_isSup_iff_ambient_isSup_of_closed hDdcpo hClosed hA).1 hs
  have hk_le_s : k ≤ c.inclusion s := le_trans (c.above k) hle
  rcases hk (DirectedSet.image (by intro x y hxy; exact hxy) hA) hAmbSup hk_le_s with
    ⟨a, ha, hka⟩
  rcases ha with ⟨aImage, haImage, rfl⟩
  exact ⟨aImage, haImage, c.closure_le_of_le_mem_range aImage.2 hka⟩

/-- If a closure image is closed under directed suprema, then compact ambient
approximants close up to compact image approximants. -/
theorem ClosureOperator.image_algebraic_of_directedSupClosed
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D)
    (hAlg : IsAlgebraicDomain D) (c : ClosureOperator D)
    (hClosed : IsDirectedSupClosed (Set.range c.c)) :
    IsAlgebraicDomain (ClosureOperator.ImageCarrier c) := by
  apply Chapter2.prop_2_2_4_1
  intro x
  let A : Set (ClosureOperator.ImageCarrier c) :=
    {y | ∃ k : D, k ∈ (Chapter2.CompactSet : Set D) ∧ k ≪ x.1 ∧
      y = c.projection k}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro y hy
    rcases hy with ⟨k, hkCompact, hkx, rfl⟩
    have hCompactImage : Compact (c.projection k) :=
      c.image_compact_of_ambient_compact hDdcpo hClosed hkCompact
    have hImageLe : c.projection k ≤ x :=
      c.closure_le_of_le_mem_range x.2 (Chapter2.prop_2_2_2_1 hkx)
    constructor
    · exact hCompactImage
    · exact Chapter2.prop_2_2_2_2 le_rfl hCompactImage hImageLe
  · have hAmbientDir : DirectedSet (Chapter2.Approximants (Chapter2.CompactSet : Set D) x.1) :=
      (hAlg x.1).1
    constructor
    · rcases hAmbientDir.1 with ⟨k, hk⟩
      exact ⟨c.projection k, k, hk.1, hk.2, rfl⟩
    · intro y hy z hz
      rcases hy with ⟨k, hkCompact, hkx, rfl⟩
      rcases hz with ⟨l, hlCompact, hlx, rfl⟩
      rcases hAmbientDir.2 ⟨hkCompact, hkx⟩ ⟨hlCompact, hlx⟩ with
        ⟨m, hm, hkm, hlm⟩
      refine ⟨c.projection m, ?_, ?_, ?_⟩
      · exact ⟨m, hm.1, hm.2, rfl⟩
      · exact c.continuous.1 hkm
      · exact c.continuous.1 hlm
  · constructor
    · intro y hy
      rcases hy with ⟨k, hkCompact, hkx, rfl⟩
      exact c.closure_le_of_le_mem_range x.2 (Chapter2.prop_2_2_2_1 hkx)
    · intro y hy
      have hAmbientUpper :
          IsUpperBound (Chapter2.Approximants (Chapter2.CompactSet : Set D) x.1) y.1 := by
        intro k hk
        have hA : c.projection k ∈ A := ⟨k, hk.1, hk.2, rfl⟩
        exact le_trans (c.above k) (hy hA)
      exact (hAlg x.1).2.2 y.1 hAmbientUpper

/-- A Scott-continuous closure operator has a directed-sup-closed image. -/
theorem ClosureOperator.directedSupClosed_range
    {D : Type u} [PartialOrder D] (c : ClosureOperator D) :
    IsDirectedSupClosed (Set.range c.c) := by
  intro B hBsub hBdir s hs
  have hfixedB : ∀ b ∈ B, c.c b = b := by
    intro b hb
    exact (c.mem_range_iff_fixed).1 (hBsub hb)
  have hImageEq : c.c '' B = B := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨b, hb, rfl⟩
      simpa [hfixedB b hb] using hb
    · intro hz
      exact ⟨z, hz, hfixedB z hz⟩
  have hcsSup : IsSup (c.c '' B) (c.c s) := c.continuous.2 hBdir hs
  have hcsSupB : IsSup B (c.c s) := by
    simpa [hImageEq] using hcsSup
  have hEq : c.c s = s := IsSup.unique hcsSupB hs
  exact ⟨s, hEq⟩

/-- Proposition 3.1.18. PDF text: "Let D be an algebraic domain and let
c : D -> D be a monotone idempotent function above idD. Then im(c) is again an
algebraic domain if and only if it is closed under directed suprema."

Current Lean spelling: this compatibility theorem proves the biconditional for
the older `ClosureOperator` interface, which is stronger than the PDF premise
because it also requires Scott-continuity.  The raw PDF-premise variants below
state the non-continuous closure-operator directions explicitly. -/
theorem prop_3_1_18_closure_image_algebraic_iff_directed_sup_closed
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D) (hD : IsAlgebraicDomain D)
    (c : ClosureOperator D) :
    IsAlgebraicDomain (ClosureOperator.ImageCarrier c) ↔ IsDirectedSupClosed (Set.range c.c) := by
  constructor
  · intro _hImage
    exact c.directedSupClosed_range
  · intro hClosed
    exact c.image_algebraic_of_directedSupClosed hDdcpo hD hClosed

/-- Proposition 3.1.18, raw PDF-premise subdomain form. -/
theorem prop_3_1_18_raw_closure_image_algebraic_subdomain_iff_directed_sup_closed
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D) (hD : IsAlgebraicDomain D)
    (c : RawClosureOperator D) :
    c.ImageAlgebraicSubdomain ↔ IsDirectedSupClosed (Set.range c.c) :=
  c.imageAlgebraicSubdomain_iff_directedSupClosed hDdcpo hD

/-- Proposition 3.1.18, raw backward direction matching the PDF hypotheses:
for a monotone idempotent `c` above `idD`, directed-sup-closedness of `im(c)`
is enough to make the image algebraic.  The converse direction for the raw
internal-carrier interface is not claimed here; the PDF subdomain reading is
captured by
`prop_3_1_18_raw_closure_image_algebraic_subdomain_iff_directed_sup_closed`. -/
theorem prop_3_1_18_raw_closure_image_algebraic_of_directed_sup_closed
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D) (hD : IsAlgebraicDomain D)
    (c : RawClosureOperator D) :
    IsDirectedSupClosed (Set.range c.c) →
      IsAlgebraicDomain (RawClosureOperator.ImageCarrier c) :=
  c.image_algebraic_of_directedSupClosed hDdcpo hD

/-- Proposition 3.1.18 raw converse support: under an explicit bridge saying
that image-carrier directed suprema remain ambient suprema after inclusion, the
algebraicity of the raw closure image implies directed-sup-closedness of the
range. -/
theorem prop_3_1_18_raw_closure_directed_sup_closed_of_image_algebraic_of_sup_agrees
    {D : Type u} [PartialOrder D] (c : RawClosureOperator D)
    (hSupAgrees :
      ∀ {A : Set (RawClosureOperator.ImageCarrier c)}
        {s : RawClosureOperator.ImageCarrier c},
        DirectedSet A → IsSup A s →
          IsSup (c.inclusion '' A) (c.inclusion s)) :
    IsAlgebraicDomain (RawClosureOperator.ImageCarrier c) →
      IsDirectedSupClosed (Set.range c.c) :=
  fun hImageAlg =>
    c.directedSupClosed_range_of_image_algebraic_of_sup_agrees hImageAlg hSupAgrees

/-- Proposition 3.1.18 raw conditional biconditional: the PDF-premise closure
operator interface proves the displayed iff once the remaining bridge is made
explicit, namely that directed suprema computed in the raw image carrier remain
ambient suprema after inclusion. -/
theorem prop_3_1_18_raw_closure_image_algebraic_iff_directed_sup_closed_of_sup_agrees
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D) (hD : IsAlgebraicDomain D)
    (c : RawClosureOperator D)
    (hSupAgrees :
      ∀ {A : Set (RawClosureOperator.ImageCarrier c)}
        {s : RawClosureOperator.ImageCarrier c},
        DirectedSet A → IsSup A s →
          IsSup (c.inclusion '' A) (c.inclusion s)) :
    IsAlgebraicDomain (RawClosureOperator.ImageCarrier c) ↔
      IsDirectedSupClosed (Set.range c.c) := by
  constructor
  · exact prop_3_1_18_raw_closure_directed_sup_closed_of_image_algebraic_of_sup_agrees
      c hSupAgrees
  · exact prop_3_1_18_raw_closure_image_algebraic_of_directed_sup_closed hDdcpo hD c

/-- Proposition 3.2.4(3) support: fixing a point of the right factor makes the
left factor a continuous retract of the product. -/
def prodLeftContinuousSectionRetractionPair
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] (e0 : E) :
    ContinuousSectionRetractionPair D (D × E) where
  s := fun d => (d, e0)
  r := fun p => p.1
  monotone_s := by
    intro x y hxy
    exact ⟨hxy, le_rfl⟩
  monotone_r := by
    intro x y hxy
    exact hxy.1
  retract := by
    intro x
    rfl
  continuous_s := prod_left_section_scottContinuous e0
  continuous_r := prod_fst_scottContinuous

/-- Proposition 3.2.4(3) support: fixing a point of the left factor makes the
right factor a continuous retract of the product. -/
def prodRightContinuousSectionRetractionPair
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] (d0 : D) :
    ContinuousSectionRetractionPair E (D × E) where
  s := fun e => (d0, e)
  r := fun p => p.2
  monotone_s := by
    intro x y hxy
    exact ⟨le_rfl, hxy⟩
  monotone_r := by
    intro x y hxy
    exact hxy.2
  retract := by
    intro x
    rfl
  continuous_s := prod_right_section_scottContinuous d0
  continuous_r := prod_snd_scottContinuous

/-- Proposition 3.2.4(3), reverse direction: a product-continuous domain makes
the left factor continuous once a point of the right factor is chosen. -/
theorem prod_left_continuous_domain_of_product
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (e0 : E) (hProd : IsContinuousDomain (D × E)) :
    IsContinuousDomain D :=
  theorem_3_1_4_retract_continuous_domain_basis
    (prodLeftContinuousSectionRetractionPair (D := D) (E := E) e0) hProd

/-- Proposition 3.2.4(3), reverse direction: a product-continuous domain makes
the right factor continuous once a point of the left factor is chosen. -/
theorem prod_right_continuous_domain_of_product
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (d0 : D) (hProd : IsContinuousDomain (D × E)) :
    IsContinuousDomain E :=
  theorem_3_1_4_retract_continuous_domain_basis
    (prodRightContinuousSectionRetractionPair (D := D) (E := E) d0) hProd

/-- Proposition 3.2.4(3): with chosen points in both factors, product continuity
is equivalent to continuity of each factor.  The explicit points account for the
current Lean `IsDcpo`/domain interface not carrying nonemptiness as a field. -/
theorem prop_3_2_4_product_continuous_domain_iff_of_points
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (d0 : D) (e0 : E) :
    IsContinuousDomain (D × E) ↔ IsContinuousDomain D ∧ IsContinuousDomain E := by
  constructor
  · intro hProd
    exact ⟨prod_left_continuous_domain_of_product e0 hProd,
      prod_right_continuous_domain_of_product d0 hProd⟩
  · intro h
    exact prod_continuous_domain h.1 h.2

/-- Existence of a least element, used to represent pointed dcpo objects without
requiring a global `OrderBot` instance in category-level interfaces. -/
def HasLeastElement (D : Type u) [Preorder D] : Prop :=
  ∃ b : D, Chapter2.IsLeast b

/-- Compatibility name for the shared antisymmetry predicate from Chapter 2. -/
abbrev IsAntisymmetricOrder (D : Type u) [Preorder D] : Prop :=
  Chapter2.IsAntisymmetricOrder D

/-- A map preserves least elements in the unbundled pointed-dcpo interfaces.
This avoids requiring an `OrderBot` instance while still expressing the
bottom-preservation condition of the strict category `DCPO⊥!`. -/
def PreservesLeastElement
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] (f : D → E) : Prop :=
  ∀ x : D, Chapter2.IsLeast x → Chapter2.IsLeast (f x)

/-- Strict Scott-continuous maps for pointed dcpos: Scott-continuity plus
bottom preservation. -/
def StrictScottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] (f : D → E) : Prop :=
  ScottContinuous f ∧ PreservesLeastElement f

/-- The strict continuous function-space carrier used for `DCPO⊥!`.
It bundles precisely the strict continuous maps mentioned in Section 3.2.4. -/
structure StrictContFun (D : Type u) (E : Type v) [Preorder D] [Preorder E] where
  toFun : D → E
  continuous : ScottContinuous toFun
  strict : PreservesLeastElement toFun

namespace StrictContFun

instance {D : Type u} {E : Type v} [Preorder D] [Preorder E] :
    CoeFun (StrictContFun D E) (fun _ => D → E) where
  coe f := f.toFun

/-- Pointwise order on strict continuous maps. -/
def Le {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (f g : StrictContFun D E) : Prop :=
  ∀ x : D, f x ≤ g x

instance {D : Type u} {E : Type v} [Preorder D] [Preorder E] :
    Preorder (StrictContFun D E) where
  le := Le
  le_refl f x := le_rfl
  le_trans f g h hfg hgh x := le_trans (hfg x) (hgh x)

/-- Extensionality for bundled strict continuous maps. -/
theorem ext_apply
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {f g : StrictContFun D E} (h : ∀ x : D, f x = g x) : f = g := by
  cases f with
  | mk f hf hs =>
      cases g with
      | mk g hg gs =>
          have hfun : f = g := funext h
          subst hfun
          congr

end StrictContFun

namespace ContFun

/-- Constant continuous functions, used to exhibit the least element of a
pointed continuous function space. -/
def const {D : Type u} {E : Type v} [Preorder D] [Preorder E] (e : E) : ContFun D E where
  toFun := fun _ => e
  continuous := const_scottContinuous e

/-- If the codomain has a least element, then the constant-bottom function is
least in the pointwise order. -/
theorem const_isLeast
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] {e : E}
    (he : Chapter2.IsLeast e) :
    Chapter2.IsLeast (ContFun.const (D := D) e) := by
  intro f x
  exact he (f x)

/-- A pointed codomain makes the continuous function space pointed by the
constant least function. -/
theorem hasLeastElement_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : HasLeastElement E) : HasLeastElement (ContFun D E) := by
  rcases hE with ⟨e, he⟩
  exact ⟨ContFun.const (D := D) e, ContFun.const_isLeast he⟩

/-- Antisymmetry of the codomain transfers to the pointwise order on continuous
functions. -/
theorem antisymmetric_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsAntisymmetricOrder E) : IsAntisymmetricOrder (ContFun D E) := by
  intro f g hfg hgf
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          have hfun : f = g := funext fun x => hE (f x) (g x) (hfg x) (hgf x)
          subst hfun
          congr

end ContFun

/-- Exact object predicates for the named categories used in Sections 3.2 and
3.3.  Every dcpo object carries antisymmetry; continuous and algebraic variants
also retain their defining basis property.  Strictness belongs to morphisms, so
it does not change the pointed object predicate. -/
def DomainCategoryObject (C : DomainCategoryName) (D : Type u) [Preorder D] : Prop :=
  match C with
  | DomainCategoryName.DCPO => IsDcpo D ∧ IsAntisymmetricOrder D
  | DomainCategoryName.DCPO_bot =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ HasLeastElement D
  | DomainCategoryName.DCPO_bot_strict =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ HasLeastElement D
  | DomainCategoryName.CONT =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsContinuousDomain D
  | DomainCategoryName.ALG =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsAlgebraicDomain D
  | DomainCategoryName.CONT_bot =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsContinuousDomain D ∧ HasLeastElement D
  | DomainCategoryName.ALG_bot =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsAlgebraicDomain D ∧ HasLeastElement D
  | DomainCategoryName.CONT_bot_strict =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsContinuousDomain D ∧ HasLeastElement D
  | DomainCategoryName.ALG_bot_strict =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsAlgebraicDomain D ∧ HasLeastElement D

/-- Lightweight order-isomorphism data for categorical comparison objects.
This keeps the Section 3.2 interfaces stronger than a bare carrier equivalence
without importing a full category-theory development. -/
structure OrderIsoData (A : Type u) (B : Type v) [Preorder A] [Preorder B] where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ x : A, invFun (toFun x) = x
  right_inv : ∀ y : B, toFun (invFun y) = y
  monotone_to : Monotone toFun
  monotone_inv : Monotone invFun

/-- Identity order-isomorphism data. -/
def OrderIsoData.refl (A : Type u) [Preorder A] : OrderIsoData A A where
  toFun := id
  invFun := id
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  monotone_to := by intro x y hxy; exact hxy
  monotone_inv := by intro x y hxy; exact hxy

/-- Lemma 3.2.5 full-subcategory interface.

The local category model uses an object predicate and inherited
Scott-continuous hom-sets.  Finite products are represented by a terminal
object and binary products with projections, pairing and uniqueness laws; an
arbitrary object closed under a type-valued operation is not enough.  The PDF
attributes the resulting comparison theorem to Smyth [Smy83a] and Jung
[Jun89]. -/
structure FullSubcategoryWithFiniteProducts (Ambient : DomainCategoryName) : Type (u + 1) where
  ambient_supported :
    Ambient = DomainCategoryName.DCPO ∨ Ambient = DomainCategoryName.DCPO_bot_strict
  object : ∀ D : Type u, [Preorder D] → Prop
  object_in_ambient :
    ∀ D : Type u, ∀ [Preorder D], object D → DomainCategoryObject Ambient D
  product :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      object D → object E → Type u
  product_preorder :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E, Preorder (product D E hD hE)
  product_object :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @object (product D E hD hE) (product_preorder D E hD hE)
  terminal : Type u
  terminal_preorder : Preorder terminal
  terminal_object : @object terminal terminal_preorder
  terminate :
    ∀ X : Type u, ∀ [Preorder X], ∀ _hX : object X,
      @ContFun X terminal inferInstance terminal_preorder
  terminate_unique :
    ∀ X : Type u, ∀ [Preorder X], ∀ hX : object X,
      ∀ f : @ContFun X terminal inferInstance terminal_preorder,
        f = terminate X hX
  fst :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @ContFun (product D E hD hE) D (product_preorder D E hD hE) inferInstance
  snd :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @ContFun (product D E hD hE) E (product_preorder D E hD hE) inferInstance
  lift :
    ∀ X D E : Type u, ∀ [Preorder X], ∀ [Preorder D], ∀ [Preorder E],
      ∀ _hX : object X, ∀ hD : object D, ∀ hE : object E,
        ContFun X D → ContFun X E →
          @ContFun X (product D E hD hE) inferInstance (product_preorder D E hD hE)
  lift_fst :
    ∀ X D E : Type u, ∀ [Preorder X], ∀ [Preorder D], ∀ [Preorder E],
      ∀ hX : object X, ∀ hD : object D, ∀ hE : object E,
        ∀ f : ContFun X D, ∀ g : ContFun X E,
          ContFun.comp (fst D E hD hE) (lift X D E hX hD hE f g) = f
  lift_snd :
    ∀ X D E : Type u, ∀ [Preorder X], ∀ [Preorder D], ∀ [Preorder E],
      ∀ hX : object X, ∀ hD : object D, ∀ hE : object E,
        ∀ f : ContFun X D, ∀ g : ContFun X E,
          ContFun.comp (snd D E hD hE) (lift X D E hX hD hE f g) = g
  lift_unique :
    ∀ X D E : Type u, ∀ [Preorder X], ∀ [Preorder D], ∀ [Preorder E],
      ∀ hX : object X, ∀ hD : object D, ∀ hE : object E,
        ∀ f : ContFun X D, ∀ g : ContFun X E,
          ∀ h : @ContFun X (product D E hD hE) inferInstance (product_preorder D E hD hE),
            ContFun.comp (fst D E hD hE) h = f →
              ContFun.comp (snd D E hD hE) h = g →
                h = lift X D E hX hD hE f g

/-- Lemma 3.2.5 conclusion for the object-predicate full-subcategory interface:
every chosen finite-product object is represented together with an
order-isomorphism to the explicit cartesian product. -/
def FullSubcategoryFiniteProductsAgreeWithCartesian
    (Ambient : DomainCategoryName) (Sub : FullSubcategoryWithFiniteProducts.{u} Ambient) : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    ∀ hD : Sub.object D, ∀ hE : Sub.object E,
      Nonempty (@OrderIsoData (Sub.product D E hD hE) (CartesianProduct D E)
        (Sub.product_preorder D E hD hE) inferInstance)

/-- Lemma 3.2.5, object-predicate full-subcategory form.  Documented external
theorem from the Smyth/Jung proof cited in the PDF: finite products in a full
subcategory of `DCPO` or `DCPO⊥!` agree with cartesian products. -/
axiom lemma_3_2_5_full_subcategory_products_cartesian_full
    (Ambient : DomainCategoryName)
    (Sub : FullSubcategoryWithFiniteProducts.{u} Ambient) :
    FullSubcategoryFiniteProductsAgreeWithCartesian.{u} Ambient Sub

/-- Lemma 3.2.5 interface. PDF text: "Let C be a full subcategory of DCPO or
DCPO⊥! which has finite products. Then these are isomorphic to the cartesian
product."

Current Lean spelling: this legacy wrapper specializes the object-predicate
full-subcategory interface above to a named ambient object class.  A
finite-product structure is represented by a chosen binary product object.  The
comparison with the explicit cartesian product is recorded below as the
documented Smyth/Jung external theorem, not as a preloaded field. -/
structure HasFiniteProducts (C : DomainCategoryName) : Type (u + 1) where
  data : FullSubcategoryWithFiniteProducts.{u} C
  object_eq : ∀ D : Type u, ∀ [Preorder D], data.object D ↔ DomainCategoryObject C D

/-- Lemma 3.2.5 conclusion in the current interface: every chosen finite-product
object is represented together with an order-isomorphism to the explicit
cartesian product. -/
def FiniteProductsAgreeWithCartesian
    (_C : DomainCategoryName) (hC : HasFiniteProducts.{u} _C) : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    ∀ hD : hC.data.object D, ∀ hE : hC.data.object E,
      Nonempty (@OrderIsoData (hC.data.product D E hD hE) (CartesianProduct D E)
        (hC.data.product_preorder D E hD hE) inferInstance)

/-- Lemma 3.2.5, legacy named-category interface form, derived from the
documented object-predicate external theorem above. -/
theorem lemma_3_2_5_full_subcategory_products_cartesian
    (C : DomainCategoryName) (hC : HasFiniteProducts.{u} C) :
    FiniteProductsAgreeWithCartesian.{u} C hC := by
  simpa [FiniteProductsAgreeWithCartesian,
    FullSubcategoryFiniteProductsAgreeWithCartesian] using
    (lemma_3_2_5_full_subcategory_products_cartesian_full C hC.data)

/-- Separate Scott-continuity of a binary map. -/
def SeparatelyScottContinuous
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (f : D × E → F) : Prop :=
  (∀ d : D, ScottContinuous (fun e : E => f (d, e))) ∧
    ∀ e : E, ScottContinuous (fun d : D => f (d, e))

/-- Lemma 3.2.6. PDF text: "A function f : D × E -> F is continuous if and
only if it is continuous in each variable separately."

Lean spelling: binary Scott-continuity for the product preorder is equivalent
to Scott-continuity of every coordinate section. -/
theorem lemma_3_2_6_continuous_iff_separately_continuous
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (f : D × E → F) :
    ScottContinuous f ↔ SeparatelyScottContinuous f := by
  constructor
  · intro hf
    constructor
    · intro d
      constructor
      · intro e₁ e₂ he
        exact hf.1 ⟨le_rfl, he⟩
      · intro A s hA hs
        let B : Set (D × E) := {p | p.1 = d ∧ p.2 ∈ A}
        have hBdir : DirectedSet B := by
          constructor
          · rcases hA.1 with ⟨a, ha⟩
            exact ⟨(d, a), rfl, ha⟩
          · intro p hp q hq
            rcases hA.2 hp.2 hq.2 with ⟨r, hr, hpr, hqr⟩
            exact ⟨(d, r), ⟨rfl, hr⟩, ⟨by simpa [hp.1], hpr⟩,
              ⟨by simpa [hq.1], hqr⟩⟩
        have hBsup : IsSup B (d, s) := by
          constructor
          · intro p hp
            exact ⟨by simpa [hp.1], hs.1 hp.2⟩
          · intro q hq
            constructor
            · rcases hA.1 with ⟨a, ha⟩
              exact (hq (a := (d, a)) ⟨rfl, ha⟩).1
            · exact hs.2 q.2 (by
                intro a ha
                exact (hq (a := (d, a)) ⟨rfl, ha⟩).2)
        have hfB : IsSup (f '' B) (f (d, s)) := hf.2 hBdir hBsup
        constructor
        · intro y hy
          rcases hy with ⟨a, ha, rfl⟩
          exact hfB.1 ⟨(d, a), ⟨rfl, ha⟩, rfl⟩
        · intro y hy
          exact hfB.2 y (by
            intro z hz
            rcases hz with ⟨p, hp, rfl⟩
            rcases p with ⟨pd, pe⟩
            rcases hp with ⟨hpd, hpA⟩
            have hpd' : pd = d := by simpa using hpd
            rw [hpd']
            exact hy ⟨pe, by simpa using hpA, rfl⟩)
    · intro e
      constructor
      · intro d₁ d₂ hd
        exact hf.1 ⟨hd, le_rfl⟩
      · intro A s hA hs
        let B : Set (D × E) := {p | p.1 ∈ A ∧ p.2 = e}
        have hBdir : DirectedSet B := by
          constructor
          · rcases hA.1 with ⟨a, ha⟩
            exact ⟨(a, e), ha, rfl⟩
          · intro p hp q hq
            rcases hA.2 hp.1 hq.1 with ⟨r, hr, hpr, hqr⟩
            exact ⟨(r, e), ⟨hr, rfl⟩, ⟨hpr, by simpa [hp.2]⟩,
              ⟨hqr, by simpa [hq.2]⟩⟩
        have hBsup : IsSup B (s, e) := by
          constructor
          · intro p hp
            exact ⟨hs.1 hp.1, by simpa [hp.2]⟩
          · intro q hq
            constructor
            · exact hs.2 q.1 (by
                intro a ha
                exact (hq (a := (a, e)) ⟨ha, rfl⟩).1)
            · rcases hA.1 with ⟨a, ha⟩
              exact (hq (a := (a, e)) ⟨ha, rfl⟩).2
        have hfB : IsSup (f '' B) (f (s, e)) := hf.2 hBdir hBsup
        constructor
        · intro y hy
          rcases hy with ⟨a, ha, rfl⟩
          exact hfB.1 ⟨(a, e), ⟨ha, rfl⟩, rfl⟩
        · intro y hy
          exact hfB.2 y (by
            intro z hz
            rcases hz with ⟨p, hp, rfl⟩
            rcases p with ⟨pd, pe⟩
            rcases hp with ⟨hpA, hpe⟩
            have hpe' : pe = e := by simpa using hpe
            rw [hpe']
            exact hy ⟨pd, by simpa using hpA, rfl⟩)
  · intro hsep
    have hmono : Monotone f := by
      intro p q hpq
      exact le_trans ((hsep.2 p.2).1 hpq.1) ((hsep.1 q.1).1 hpq.2)
    constructor
    · exact hmono
    · intro A s hA hs
      let AD : Set D := {d | ∃ e : E, (d, e) ∈ A}
      let AE : Set E := {e | ∃ d : D, (d, e) ∈ A}
      have hADdir : DirectedSet AD := by
        constructor
        · rcases hA.1 with ⟨p, hp⟩
          exact ⟨p.1, p.2, hp⟩
        · intro d hd d' hd'
          rcases hd with ⟨e, hde⟩
          rcases hd' with ⟨e', hd'e'⟩
          rcases hA.2 hde hd'e' with ⟨p, hp, hdp, hd'p⟩
          exact ⟨p.1, ⟨p.2, hp⟩, hdp.1, hd'p.1⟩
      have hAEdir : DirectedSet AE := by
        constructor
        · rcases hA.1 with ⟨p, hp⟩
          exact ⟨p.2, p.1, hp⟩
        · intro e he e' he'
          rcases he with ⟨d, hde⟩
          rcases he' with ⟨d', hd'e'⟩
          rcases hA.2 hde hd'e' with ⟨p, hp, hdp, hd'p⟩
          exact ⟨p.2, ⟨p.1, hp⟩, hdp.2, hd'p.2⟩
      have hAEsup : IsSup AE s.2 := by
        constructor
        · intro e he
          rcases he with ⟨d, hde⟩
          exact (hs.1 hde).2
        · intro e he
          have hUpper : IsUpperBound A (s.1, e) := by
            intro p hp
            exact ⟨(hs.1 hp).1, he ⟨p.1, hp⟩⟩
          exact (hs.2 (s.1, e) hUpper).2
      have hADsup : IsSup AD s.1 := by
        constructor
        · intro d hd
          rcases hd with ⟨e, hde⟩
          exact (hs.1 hde).1
        · intro d hd
          have hUpper : IsUpperBound A (d, s.2) := by
            intro p hp
            exact ⟨hd ⟨p.2, hp⟩, (hs.1 hp).2⟩
          exact (hs.2 (d, s.2) hUpper).1
      constructor
      · intro z hz
        rcases hz with ⟨p, hp, rfl⟩
        exact hmono (hs.1 hp)
      · intro y hy
        have hy_d_snd : ∀ d ∈ AD, f (d, s.2) ≤ y := by
          intro d hd
          have hSupE : IsSup ((fun e : E => f (d, e)) '' AE) (f (d, s.2)) :=
            (hsep.1 d).2 hAEdir hAEsup
          exact hSupE.2 y (by
            intro z hz
            rcases hz with ⟨e, he, rfl⟩
            rcases hd with ⟨ed, hdA⟩
            rcases he with ⟨d', hd'eA⟩
            rcases hA.2 hdA hd'eA with ⟨p, hp, hdp, hd'p⟩
            exact le_trans (hmono ⟨hdp.1, hd'p.2⟩) (hy ⟨p, hp, rfl⟩))
        have hSupD : IsSup ((fun d : D => f (d, s.2)) '' AD) (f (s.1, s.2)) :=
          (hsep.2 s.2).2 hADdir hADsup
        exact hSupD.2 y (by
          intro z hz
          rcases hz with ⟨d, hd, rfl⟩
          exact hy_d_snd d hd)

/-- Lemma 3.2.7 full-subcategory interface.

This is the object-predicate version of "a cartesian closed full subcategory of
`DCPO`".  Morphisms are inherited Scott-continuous maps, finite products carry
their actual universal properties, and `exponential_universal` records the
hom-order isomorphism characterizing exponentials.  The external comparison
theorem below follows the PDF's Smyth/Jung reference. -/
structure CartesianClosedFullSubcategoryOfDCPO : Type (u + 1) where
  object : ∀ D : Type u, [Preorder D] → Prop
  object_dcpo : ∀ D : Type u, ∀ [Preorder D], object D → IsDcpo D
  object_antisymmetric : ∀ D : Type u, ∀ [Preorder D], object D → IsAntisymmetricOrder D
  function_space_dcpo :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      object D → object E → IsDcpo (ContFun D E)
  function_space_antisymmetric :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      object D → object E → IsAntisymmetricOrder (ContFun D E)
  exponential :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      object D → object E → Type u
  exponential_preorder :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E, Preorder (exponential D E hD hE)
  exponential_object :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @object (exponential D E hD hE) (exponential_preorder D E hD hE)
  exponential_dcpo :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @IsDcpo (exponential D E hD hE) (exponential_preorder D E hD hE)
  exponential_antisymmetric :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @IsAntisymmetricOrder (exponential D E hD hE) (exponential_preorder D E hD hE)
  products : FullSubcategoryWithFiniteProducts.{u} DomainCategoryName.DCPO
  products_object_iff :
    ∀ D : Type u, ∀ [Preorder D], products.object D ↔ object D
  exponential_universal :
    ∀ X D E : Type u, ∀ [Preorder X], ∀ [Preorder D], ∀ [Preorder E],
      ∀ hX : object X, ∀ hD : object D, ∀ hE : object E,
        Nonempty
          (@OrderIsoData
            (@ContFun
              (products.product X D ((products_object_iff X).2 hX)
                ((products_object_iff D).2 hD)) E
              (products.product_preorder X D ((products_object_iff X).2 hX)
                ((products_object_iff D).2 hD)) inferInstance)
            (@ContFun X (exponential D E hD hE) inferInstance
              (exponential_preorder D E hD hE))
            inferInstance inferInstance)

/-- Lemma 3.2.7 conclusion for the object-predicate full-subcategory interface:
each exponential object is a partial-order dcpo and is order-isomorphic to the
Scott-continuous function-space carrier.  The comparison is supplied by the
documented external theorem below from the stated exponential universal
property. -/
def FullSubcategoryExponentialAgreesWithFunctionSpace
    (C : CartesianClosedFullSubcategoryOfDCPO.{u}) : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    ∀ hD : C.object D, ∀ hE : C.object E,
      Nonempty (@OrderIsoData (C.exponential D E hD hE) (ContFun D E)
        (C.exponential_preorder D E hD hE) inferInstance)

/-- Lemma 3.2.7, object-predicate full-subcategory form.  Documented external
theorem from the categorical comparison argument cited around Lemma 3.2.5: the
exponential in a cartesian closed full subcategory of `DCPO` agrees with the
Scott-continuous function-space carrier. -/
axiom lemma_3_2_7_exponential_is_function_space_full
    (C : CartesianClosedFullSubcategoryOfDCPO.{u}) :
    FullSubcategoryExponentialAgreesWithFunctionSpace.{u} C

/-- Named-category compatibility wrapper for the full cartesian-closed
subcategory interface.  Unlike the former carrier-only record, `data` includes
finite-product and exponential universal properties. -/
structure CartesianClosedFullSubcategory (C : DomainCategoryName) : Type (u + 1) where
  ambient_eq : C = DomainCategoryName.DCPO
  data : CartesianClosedFullSubcategoryOfDCPO.{u}
  object_iff :
    ∀ D : Type u, ∀ [Preorder D], data.object D ↔ DomainCategoryObject C D

/-- Lemma 3.2.7 conclusion in the current interface: every chosen exponential
object is represented as a partial-order dcpo together with an order-isomorphism
to the bundled Scott-continuous function-space carrier, which is also recorded
as a partial-order dcpo. -/
def ExponentialAgreesWithFunctionSpace
    (_C : DomainCategoryName) (hC : CartesianClosedFullSubcategory.{u} _C) : Prop :=
  FullSubcategoryExponentialAgreesWithFunctionSpace hC.data

/-- Lemma 3.2.7, legacy named-category interface form, derived from the
documented object-predicate external theorem above. -/
theorem lemma_3_2_7_exponential_is_function_space
    (C : DomainCategoryName) (hC : CartesianClosedFullSubcategory.{u} C) :
    ExponentialAgreesWithFunctionSpace.{u} C hC := by
  simpa [ExponentialAgreesWithFunctionSpace,
    FullSubcategoryExponentialAgreesWithFunctionSpace] using
    (lemma_3_2_7_exponential_is_function_space_full hC.data)

/-- Proposition 3.2.8. PDF text: "The coalesced sum of pointed dcpo's is a
pointed dcpo."

Current Lean spelling: the coalesced-sum carrier is a dcpo with least bottom.
The explicit bottom-separation hypotheses record the poset fact that no
non-bottom element can be below bottom in the current preorder-based interface. -/
theorem prop_3_2_8_coalesced_sum_pointed_dcpo
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hD : IsDcpo D) (hE : IsDcpo E)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    IsDcpo (CoalescedSum D E) ∧ Chapter2.IsLeast (⊥ : CoalescedSum D E) :=
  CoalescedSum.pointedDcpo (D := D) (E := E) hD hE hDbot hEbot

/-- The strict coproduct universal-property interface for the coalesced sum, at
the carrier level with strict bottom-preserving maps. -/
def IsStrictCoproduct
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E] :
    Prop :=
  Nonempty (CoalescedSum.StrictCoproductData.{u, v, w} (D := D) (E := E))

/-- The strict Scott-continuous coproduct interface for the coalesced sum.  This
is the `DCPO⊥!` part of Proposition 3.2.9 in the current unbundled interface:
strict injections are Scott-continuous, and strict Scott-continuous pairs have
a unique strict mediator whose underlying map is Scott-continuous. -/
def IsStrictContinuousCoproduct
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    Prop :=
  Nonempty
    (CoalescedSum.StrictContinuousCoproductData.{u, v, w} (D := D) (E := E)
      hDbot hEbot)

/-- The `CONT⊥!` object-class part of Proposition 3.2.9.  The local predicate
`IsContinuousDomain` records the basis property, so the dcpo parts of the object
class are stated explicitly. -/
def CoalescedSumContinuousObjectClosure
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (_hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (_hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    Prop :=
  IsDcpo D → IsDcpo E → IsContinuousDomain D → IsContinuousDomain E →
    IsDcpo (CoalescedSum D E) ∧ IsContinuousDomain (CoalescedSum D E)

/-- The `ALG⊥!` object-class part of Proposition 3.2.9, isolated as an explicit
closure clause.  The local predicate `IsAlgebraicDomain` records the compact
basis property, so the dcpo parts of the object class are stated explicitly. -/
def CoalescedSumAlgebraicObjectClosure
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (_hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (_hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    Prop :=
  IsDcpo D → IsDcpo E → IsAlgebraicDomain D → IsAlgebraicDomain E →
    IsDcpo (CoalescedSum D E) ∧ IsAlgebraicDomain (CoalescedSum D E)

/-- Proposition 3.2.9 support: the coalesced sum preserves the `CONT⊥!` object
class in the current preorder interface. -/
theorem coalescedSumContinuousObjectClosure
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    CoalescedSumContinuousObjectClosure D E hDbot hEbot := by
  intro hDdcpo hEdcpo hDcont hEcont
  exact
    ⟨CoalescedSum.isDcpo (D := D) (E := E) hDdcpo hEdcpo hDbot hEbot,
      CoalescedSum.continuousDomain (D := D) (E := E) hDbot hEbot hDcont hEcont⟩

/-- Proposition 3.2.9 support: the coalesced sum preserves the `ALG⊥!` object
class in the current preorder interface. -/
theorem coalescedSumAlgebraicObjectClosure
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    CoalescedSumAlgebraicObjectClosure D E hDbot hEbot := by
  intro hDdcpo hEdcpo hDalg hEalg
  exact
    ⟨CoalescedSum.isDcpo (D := D) (E := E) hDdcpo hEdcpo hDbot hEbot,
      CoalescedSum.algebraicDomain (D := D) (E := E) hDbot hEbot hDalg hEalg⟩

/-- Full Proposition 3.2.9 data in the current interface: the proved
`DCPO⊥!` strict continuous coproduct core, plus proved object-class closure
clauses for `CONT⊥!` and `ALG⊥!`. -/
structure CoalescedSumFullCoproductData
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) : Prop where
  dcpo_coproduct : IsStrictContinuousCoproduct.{u, v, w} D E hDbot hEbot
  continuous_object_closure : CoalescedSumContinuousObjectClosure D E hDbot hEbot
  algebraic_object_closure : CoalescedSumAlgebraicObjectClosure D E hDbot hEbot

/-- Proposition 3.2.9. PDF text: "The coalesced sum of pointed dcpo's is the
coproduct in DCPO⊥!, CONT⊥!, and ALG⊥!."

Current Lean spelling: this declaration records the `DCPO⊥!` strict continuous
coproduct core: strict Scott-continuous injections and the expected unique
strict Scott-continuous mediator for every pair of strict Scott-continuous maps.
The full data declaration below adds the `CONT⊥!` and `ALG⊥!` object-class
preservation clauses, with the same bottom-separation hypotheses used by the
coalesced-sum dcpo construction in the preorder interface. -/
noncomputable def prop_3_2_9_coalesced_sum_coproduct
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    IsStrictContinuousCoproduct.{u, v, w} D E hDbot hEbot :=
  ⟨CoalescedSum.strictContinuousCoproductData (D := D) (E := E) hDbot hEbot⟩

/-- Proposition 3.2.9, full-data packaging for the current interface. -/
noncomputable def prop_3_2_9_coalesced_sum_coproduct_full
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    CoalescedSumFullCoproductData D E hDbot hEbot :=
  { dcpo_coproduct := prop_3_2_9_coalesced_sum_coproduct D E hDbot hEbot
    continuous_object_closure := coalescedSumContinuousObjectClosure D E hDbot hEbot
    algebraic_object_closure := coalescedSumAlgebraicObjectClosure D E hDbot hEbot }

/-- Proposition 3.2.9, theorem-facing existence wrapper around the complete
coproduct and object-class preservation package. -/
theorem prop_3_2_9_coalesced_sum_coproduct_full_exists
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    Nonempty (CoalescedSumFullCoproductData D E hDbot hEbot) :=
  ⟨prop_3_2_9_coalesced_sum_coproduct_full D E hDbot hEbot⟩

/-- Proposition 3.2.9, full-data packaging from explicit object-class closure
proofs.  This compatibility constructor is retained for callers that already
package the object-class closure clauses separately. -/
noncomputable def prop_3_2_9_coalesced_sum_coproduct_full_of_object_closure
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (hCont : CoalescedSumContinuousObjectClosure D E hDbot hEbot)
    (hAlg : CoalescedSumAlgebraicObjectClosure D E hDbot hEbot) :
    CoalescedSumFullCoproductData D E hDbot hEbot :=
  { dcpo_coproduct := prop_3_2_9_coalesced_sum_coproduct D E hDbot hEbot
    continuous_object_closure := hCont
    algebraic_object_closure := hAlg }

/-- The commuting-tuple carrier used in the proof of Theorem 3.3.1.  Its points
are dependent tuples whose coordinates commute with every diagram morphism. -/
def DiagramLimitCarrier
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)) : Type (max u w) :=
  {x : ∀ i : O, Obj i // ∀ j : M, map j (x (shape.dom j)) = x (shape.cod j)}

instance instPreorderDiagramLimitCarrier
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)} :
    Preorder (DiagramLimitCarrier shape Obj map) where
  le x y := ∀ i : O, x.1 i ≤ y.1 i
  le_refl x i := le_rfl
  le_trans x y z hxy hyz i := le_trans (hxy i) (hyz i)

/-- Coordinate projection from the commuting-tuple carrier. -/
def DiagramLimitCarrier.proj
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (i : O) : DiagramLimitCarrier shape Obj map → Obj i :=
  fun x => x.1 i

/-- The coordinate image of a subset of the commuting-tuple carrier. -/
def DiagramLimitCarrier.coordSet
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (A : Set (DiagramLimitCarrier shape Obj map)) (i : O) : Set (Obj i) :=
  DiagramLimitCarrier.proj i '' A

theorem DiagramLimitCarrier.coordSet_directed
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    {A : Set (DiagramLimitCarrier shape Obj map)}
    (hA : DirectedSet A) (i : O) :
    DirectedSet (DiagramLimitCarrier.coordSet A i) :=
  DirectedSet.image (f := DiagramLimitCarrier.proj i) (by
    intro x y hxy
    exact hxy i) hA

/-- The coordinatewise supremum tuple for a directed subset of the
commuting-tuple carrier. -/
noncomputable def DiagramLimitCarrier.supTuple
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (A : Set (DiagramLimitCarrier shape Obj map)) (hA : DirectedSet A) :
    ∀ i : O, Obj i :=
  fun i => Classical.choose (hObj i (DiagramLimitCarrier.coordSet A i)
    (DiagramLimitCarrier.coordSet_directed hA i))

theorem DiagramLimitCarrier.supTuple_isSup_coord
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (A : Set (DiagramLimitCarrier shape Obj map)) (hA : DirectedSet A)
    (i : O) :
    IsSup (DiagramLimitCarrier.coordSet A i)
      (DiagramLimitCarrier.supTuple hObj A hA i) :=
  Classical.choose_spec (hObj i (DiagramLimitCarrier.coordSet A i)
    (DiagramLimitCarrier.coordSet_directed hA i))

/-- The coordinatewise supremum tuple still commutes with every diagram morphism.
This is where Scott-continuity of the diagram maps and antisymmetry of the
target dcpos are used. -/
theorem DiagramLimitCarrier.supTuple_commutes
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hmap : ∀ j : M, ScottContinuous (map j))
    (A : Set (DiagramLimitCarrier shape Obj map)) (hA : DirectedSet A)
    (j : M) :
    map j (DiagramLimitCarrier.supTuple hObj A hA (shape.dom j)) =
      DiagramLimitCarrier.supTuple hObj A hA (shape.cod j) := by
  let s := DiagramLimitCarrier.supTuple hObj A hA
  have hdomSup :
      IsSup (DiagramLimitCarrier.coordSet A (shape.dom j)) (s (shape.dom j)) :=
    DiagramLimitCarrier.supTuple_isSup_coord hObj A hA (shape.dom j)
  have hcodSup :
      IsSup (DiagramLimitCarrier.coordSet A (shape.cod j)) (s (shape.cod j)) :=
    DiagramLimitCarrier.supTuple_isSup_coord hObj A hA (shape.cod j)
  have hmapSup :
      IsSup (map j '' DiagramLimitCarrier.coordSet A (shape.dom j))
        (map j (s (shape.dom j))) :=
    (hmap j).2 (DiagramLimitCarrier.coordSet_directed hA (shape.dom j)) hdomSup
  have hcod_le_map : s (shape.cod j) ≤ map j (s (shape.dom j)) := by
    exact hcodSup.2 (map j (s (shape.dom j))) (by
      intro y hy
      rcases hy with ⟨x, hxA, rfl⟩
      calc
        x.1 (shape.cod j) = map j (x.1 (shape.dom j)) := (x.2 j).symm
        _ ≤ map j (s (shape.dom j)) :=
          (hmap j).1 (hdomSup.1 ⟨x, hxA, rfl⟩))
  have hmap_le_cod : map j (s (shape.dom j)) ≤ s (shape.cod j) := by
    exact hmapSup.2 (s (shape.cod j)) (by
      intro y hy
      rcases hy with ⟨d, hd, rfl⟩
      rcases hd with ⟨x, hxA, rfl⟩
      calc
        map j (x.1 (shape.dom j)) = x.1 (shape.cod j) := x.2 j
        _ ≤ s (shape.cod j) := hcodSup.1 ⟨x, hxA, rfl⟩)
  exact hantisymm (shape.cod j) _ _ hmap_le_cod hcod_le_map

/-- The coordinatewise supremum as an element of the commuting-tuple carrier. -/
noncomputable def DiagramLimitCarrier.directedSup
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hmap : ∀ j : M, ScottContinuous (map j))
    (A : Set (DiagramLimitCarrier shape Obj map)) (hA : DirectedSet A) :
    DiagramLimitCarrier shape Obj map where
  val := DiagramLimitCarrier.supTuple hObj A hA
  property := DiagramLimitCarrier.supTuple_commutes hObj hantisymm hmap A hA

theorem DiagramLimitCarrier.directedSup_isSup
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hmap : ∀ j : M, ScottContinuous (map j))
    (A : Set (DiagramLimitCarrier shape Obj map)) (hA : DirectedSet A) :
    IsSup A (DiagramLimitCarrier.directedSup hObj hantisymm hmap A hA) := by
  constructor
  · intro x hx i
    exact (DiagramLimitCarrier.supTuple_isSup_coord hObj A hA i).1 ⟨x, hx, rfl⟩
  · intro y hy i
    exact (DiagramLimitCarrier.supTuple_isSup_coord hObj A hA i).2 (y.1 i) (by
      intro z hz
      rcases hz with ⟨x, hxA, rfl⟩
      exact hy hxA i)

theorem DiagramLimitCarrier.isDcpo
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hmap : ∀ j : M, ScottContinuous (map j)) :
    IsDcpo (DiagramLimitCarrier shape Obj map) := by
  intro A hA
  exact ⟨DiagramLimitCarrier.directedSup hObj hantisymm hmap A hA,
    DiagramLimitCarrier.directedSup_isSup hObj hantisymm hmap A hA⟩

theorem DiagramLimitCarrier.antisymmetric
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i)) :
    IsAntisymmetricOrder (DiagramLimitCarrier shape Obj map) := by
  intro x y hxy hyx
  apply Subtype.ext
  funext i
  exact hantisymm i (x.1 i) (y.1 i) (hxy i) (hyx i)

theorem DiagramLimitCarrier.proj_scottContinuous
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hmap : ∀ j : M, ScottContinuous (map j))
    (i : O) : ScottContinuous (DiagramLimitCarrier.proj (shape := shape) (map := map) i) := by
  constructor
  · intro x y hxy
    exact hxy i
  · intro A s hA hs
    let t := DiagramLimitCarrier.directedSup hObj hantisymm hmap A hA
    have ht : IsSup A t :=
      DiagramLimitCarrier.directedSup_isSup hObj hantisymm hmap A hA
    have hst : s = t :=
      DiagramLimitCarrier.antisymmetric hantisymm s t
        (Chapter2.IsSup.le_of_isSup hs ht) (Chapter2.IsSup.le_of_isSup ht hs)
    have htCoord :
        IsSup (DiagramLimitCarrier.coordSet A i) (DiagramLimitCarrier.proj i t) :=
      DiagramLimitCarrier.supTuple_isSup_coord hObj A hA i
    simpa [DiagramLimitCarrier.coordSet, DiagramLimitCarrier.proj, hst] using htCoord

/-- The limiting cone carried by the commuting-tuple object. -/
def DiagramLimitCarrier.limitCone
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)} :
    Cone shape Obj map (DiagramLimitCarrier shape Obj map) where
  leg := DiagramLimitCarrier.proj
  commute j x := x.2 j

/-- The unique mediator from any cone into the commuting-tuple cone. -/
def DiagramLimitCarrier.lift
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    {E : Type z} [Preorder E] (c : Cone shape Obj map E) :
    E → DiagramLimitCarrier shape Obj map :=
  fun x => ⟨fun i => c.leg i x, fun j => c.commute j x⟩

theorem DiagramLimitCarrier.lift_scottContinuous
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    {E : Type z} [Preorder E] (c : Cone shape Obj map E)
    (hc : ∀ i : O, ScottContinuous (c.leg i)) :
    ScottContinuous (DiagramLimitCarrier.lift c) := by
  constructor
  · intro x y hxy i
    exact (hc i).1 hxy
  · intro A s hA hs
    constructor
    · intro y hy i
      rcases hy with ⟨a, ha, rfl⟩
      exact ((hc i).2 hA hs).1 ⟨a, ha, rfl⟩
    · intro y hy i
      exact ((hc i).2 hA hs).2 (y.1 i) (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hy ⟨a, ha, rfl⟩ i)

/-- The coordinatewise least tuple for a pointed diagram. -/
noncomputable def DiagramLimitCarrier.leastTuple
    {O : Type u} {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    (hpointed : ∀ i : O, HasLeastElement (Obj i)) : ∀ i : O, Obj i :=
  fun i => Classical.choose (hpointed i)

theorem DiagramLimitCarrier.leastTuple_isLeast
    {O : Type u} {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    (hpointed : ∀ i : O, HasLeastElement (Obj i)) (i : O) :
    Chapter2.IsLeast (DiagramLimitCarrier.leastTuple hpointed i) :=
  Classical.choose_spec (hpointed i)

theorem DiagramLimitCarrier.leastTuple_commutes
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hpointed : ∀ i : O, HasLeastElement (Obj i))
    (hmap : ∀ j : M, StrictScottContinuous (map j)) (j : M) :
    map j (DiagramLimitCarrier.leastTuple hpointed (shape.dom j)) =
      DiagramLimitCarrier.leastTuple hpointed (shape.cod j) := by
  have hmapLeast :
      Chapter2.IsLeast
        (map j (DiagramLimitCarrier.leastTuple hpointed (shape.dom j))) :=
    (hmap j).2
      (DiagramLimitCarrier.leastTuple hpointed (shape.dom j))
      (DiagramLimitCarrier.leastTuple_isLeast hpointed (shape.dom j))
  have hcodLeast :
      Chapter2.IsLeast
        (DiagramLimitCarrier.leastTuple hpointed (shape.cod j)) :=
    DiagramLimitCarrier.leastTuple_isLeast hpointed (shape.cod j)
  exact hantisymm (shape.cod j) _ _
    (hmapLeast (DiagramLimitCarrier.leastTuple hpointed (shape.cod j)))
    (hcodLeast (map j (DiagramLimitCarrier.leastTuple hpointed (shape.dom j))))

/-- The coordinatewise bottom tuple as an element of the limiting carrier. -/
noncomputable def DiagramLimitCarrier.least
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hpointed : ∀ i : O, HasLeastElement (Obj i))
    (hmap : ∀ j : M, StrictScottContinuous (map j)) :
    DiagramLimitCarrier shape Obj map where
  val := DiagramLimitCarrier.leastTuple hpointed
  property := DiagramLimitCarrier.leastTuple_commutes (shape := shape) (map := map)
    hantisymm hpointed hmap

theorem DiagramLimitCarrier.least_isLeast
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hpointed : ∀ i : O, HasLeastElement (Obj i))
    (hmap : ∀ j : M, StrictScottContinuous (map j)) :
    Chapter2.IsLeast (DiagramLimitCarrier.least hantisymm hpointed hmap) := by
  intro x i
  change DiagramLimitCarrier.leastTuple hpointed i ≤ x.1 i
  exact DiagramLimitCarrier.leastTuple_isLeast hpointed i (x.1 i)

theorem DiagramLimitCarrier.hasLeastElement
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hpointed : ∀ i : O, HasLeastElement (Obj i))
    (hmap : ∀ j : M, StrictScottContinuous (map j)) :
    HasLeastElement (DiagramLimitCarrier shape Obj map) :=
  ⟨DiagramLimitCarrier.least hantisymm hpointed hmap,
    DiagramLimitCarrier.least_isLeast hantisymm hpointed hmap⟩

theorem DiagramLimitCarrier.proj_strictScottContinuous
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hpointed : ∀ i : O, HasLeastElement (Obj i))
    (hmap : ∀ j : M, StrictScottContinuous (map j)) (i : O) :
    StrictScottContinuous
      (DiagramLimitCarrier.proj (shape := shape) (map := map) i) := by
  refine ⟨DiagramLimitCarrier.proj_scottContinuous hObj hantisymm
    (fun j => (hmap j).1) i, ?_⟩
  intro x hx
  have hbottom :
      Chapter2.IsLeast (DiagramLimitCarrier.least hantisymm hpointed hmap) :=
    DiagramLimitCarrier.least_isLeast hantisymm hpointed hmap
  have hx_eq :
      x = DiagramLimitCarrier.least hantisymm hpointed hmap :=
    DiagramLimitCarrier.antisymmetric hantisymm x
      (DiagramLimitCarrier.least hantisymm hpointed hmap)
      (hx (DiagramLimitCarrier.least hantisymm hpointed hmap))
      (hbottom x)
  intro y
  rw [hx_eq]
  change DiagramLimitCarrier.leastTuple hpointed i ≤ y
  exact DiagramLimitCarrier.leastTuple_isLeast hpointed i y

theorem DiagramLimitCarrier.lift_strictScottContinuous
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    {E : Type z} [Preorder E] (c : Cone shape Obj map E)
    (hc : ∀ i : O, StrictScottContinuous (c.leg i)) :
    StrictScottContinuous (DiagramLimitCarrier.lift c) := by
  refine ⟨DiagramLimitCarrier.lift_scottContinuous c (fun i => (hc i).1), ?_⟩
  intro x hx y i
  exact (hc i).2 x hx (y.1 i)

/-- A limiting cone in the current concrete-diagram interface for `DCPO`.  This
records the actual universal property: a dcpo carrier, continuous projection
legs, and a unique continuous mediating map from every other cone whose vertex
is also a partial-order dcpo. -/
structure LimitingConeData
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j))
    (L : Type l) [Preorder L] where
  isDcpo : IsDcpo L
  cone : Cone shape Obj map L
  leg_continuous : ∀ i : O, ScottContinuous (cone.leg i)
  lift :
    ∀ (E : Type z) [Preorder E], IsDcpo E → IsAntisymmetricOrder E →
      (c : Cone shape Obj map E) →
        (∀ i : O, ScottContinuous (c.leg i)) → E → L
  lift_continuous :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i)),
      ScottContinuous (lift E hE hEanti c hc)
  lift_fac :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i))
      (i : O) (x : E),
      cone.leg i (lift E hE hEanti c hc x) = c.leg i x
  lift_unique :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i))
      (g : E → L),
      ScottContinuous g →
      (∀ i : O, ∀ x : E, cone.leg i (g x) = c.leg i x) →
        ∀ x : E, g x = lift E hE hEanti c hc x

/-- A colimiting cocone in the current concrete-diagram interface for `DCPO`.
This is the dual universal property: a dcpo carrier, continuous injection legs,
and a unique continuous mediating map into every other cocone whose vertex is
also a partial-order dcpo. -/
structure ColimitingCoconeData
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j))
    (C : Type l) [Preorder C] where
  isDcpo : IsDcpo C
  cocone : Cocone shape Obj map C
  leg_continuous : ∀ i : O, ScottContinuous (cocone.leg i)
  desc :
    ∀ (E : Type z) [Preorder E], IsDcpo E → IsAntisymmetricOrder E →
      (c : Cocone shape Obj map E) →
        (∀ i : O, ScottContinuous (c.leg i)) → C → E
  desc_continuous :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i)),
      ScottContinuous (desc E hE hEanti c hc)
  desc_fac :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i))
      (i : O) (x : Obj i),
      desc E hE hEanti c hc (cocone.leg i x) = c.leg i x
  desc_unique :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i))
      (g : C → E),
      ScottContinuous g →
      (∀ i : O, ∀ x : Obj i, g (cocone.leg i x) = c.leg i x) →
        ∀ x : C, g x = desc E hE hEanti c hc x

/-- Strict-pointed limiting cone data for `DCPO⊥!`.  It mirrors
`LimitingConeData` but restricts diagram maps, cone legs, and mediating maps to
strict Scott-continuous maps. -/
structure StrictPointedLimitingConeData
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j))
    (L : Type l) [Preorder L] where
  isDcpo : IsDcpo L
  antisymmetric : IsAntisymmetricOrder L
  pointed : HasLeastElement L
  cone : Cone shape Obj map L
  leg_strict : ∀ i : O, StrictScottContinuous (cone.leg i)
  lift :
    ∀ (E : Type z) [Preorder E], IsDcpo E → IsAntisymmetricOrder E →
      HasLeastElement E →
        (c : Cone shape Obj map E) →
          (∀ i : O, StrictScottContinuous (c.leg i)) → E → L
  lift_strict :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i)),
      StrictScottContinuous (lift E hE hEanti hEpointed c hc)
  lift_fac :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i))
      (i : O) (x : E),
      cone.leg i (lift E hE hEanti hEpointed c hc x) = c.leg i x
  lift_unique :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i))
      (g : E → L),
      StrictScottContinuous g →
      (∀ i : O, ∀ x : E, cone.leg i (g x) = c.leg i x) →
        ∀ x : E, g x = lift E hE hEanti hEpointed c hc x

/-- Strict-pointed colimiting cocone data for `DCPO⊥!`.  It records the dual
universal property with strict Scott-continuous cocone legs and mediating maps. -/
structure StrictPointedColimitingCoconeData
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j))
    (C : Type l) [Preorder C] where
  isDcpo : IsDcpo C
  antisymmetric : IsAntisymmetricOrder C
  pointed : HasLeastElement C
  cocone : Cocone shape Obj map C
  leg_strict : ∀ i : O, StrictScottContinuous (cocone.leg i)
  desc :
    ∀ (E : Type z) [Preorder E], IsDcpo E → IsAntisymmetricOrder E →
      HasLeastElement E →
        (c : Cocone shape Obj map E) →
          (∀ i : O, StrictScottContinuous (c.leg i)) → C → E
  desc_strict :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i)),
      StrictScottContinuous (desc E hE hEanti hEpointed c hc)
  desc_fac :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i))
      (i : O) (x : Obj i),
      desc E hE hEanti hEpointed c hc (cocone.leg i x) = c.leg i x
  desc_unique :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i))
      (g : C → E),
      StrictScottContinuous g →
      (∀ i : O, ∀ x : Obj i, g (cocone.leg i x) = c.leg i x) →
        ∀ x : C, g x = desc E hE hEanti hEpointed c hc x

/-- Completeness of a named domain-category object class in the Chapter 3
concrete-diagram interface.  The generic named-category version records
Scott-continuity; the dedicated `DCPO⊥!` declarations below use strict maps. -/
def DomainCategoryHasAllLimits (C : DomainCategoryName) : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, DomainCategoryObject C (Obj i)) →
        (∀ j : M, ScottContinuous (map j)) →
          ∃ L : Type z, ∃ instL : Preorder L,
            @DomainCategoryObject C L instL ∧
              Nonempty (@LimitingConeData.{u, v, w, z, z} O M shape Obj _ map L instL)

/-- Cocompleteness of a named domain-category object class in the Chapter 3
concrete-diagram interface, with the same Scott-continuous morphism convention
as `DomainCategoryHasAllLimits`. -/
def DomainCategoryHasAllColimits (C : DomainCategoryName) : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, DomainCategoryObject C (Obj i)) →
        (∀ j : M, ScottContinuous (map j)) →
          ∃ Col : Type z, ∃ instCol : Preorder Col,
            @DomainCategoryObject C Col instCol ∧
              Nonempty (@ColimitingCoconeData.{u, v, w, z, z} O M shape Obj _ map Col instCol)

/-- Completeness of `DCPO` in the concrete-diagram interface used for Theorem
3.3.1.  Because the local development is preorder-based, the partial-order part
of "dcpo" is carried by the explicit `IsAntisymmetricOrder` hypothesis. -/
def DCPOHasAllLimits : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, IsDcpo (Obj i)) →
        (∀ i : O, IsAntisymmetricOrder (Obj i)) →
          (∀ j : M, ScottContinuous (map j)) →
            ∃ L : Type (max u w), ∃ instL : Preorder L,
              @IsDcpo L instL ∧ @IsAntisymmetricOrder L instL ∧
                Nonempty (@LimitingConeData.{u, v, w, z, max u w}
                  O M shape Obj _ map L instL)

/-- Cocompleteness of `DCPO` in the Chapter 3 concrete-diagram setting.  This
is still an external-literature theorem, but its statement now matches the
book's partial-order reading of `DCPO` by carrying explicit antisymmetry
hypotheses for objects and the colimit carrier.

The PDF attributes Theorem 3.3.2 to Markowsky [Mar77], Meseguer [Mes77], a
reduction to Herrlich--Strecker [HS73, Theorem 23.14] appearing in
Lehmann--Smyth [LS81], and the detailed analysis by Fiech [Fie92]. -/
def DCPOHasAllColimits : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, IsDcpo (Obj i)) →
        (∀ i : O, IsAntisymmetricOrder (Obj i)) →
          (∀ j : M, ScottContinuous (map j)) →
            ∃ Col : Type z, ∃ instCol : Preorder Col,
              @IsDcpo Col instCol ∧ @IsAntisymmetricOrder Col instCol ∧
                Nonempty (@ColimitingCoconeData.{u, v, w, z, z}
                  O M shape Obj _ map Col instCol)

/-- Completeness of `DCPO⊥!` in the current concrete-diagram interface:
objects are antisymmetric pointed dcpos and all diagram/cone/mediating maps are
strict Scott-continuous.  The carrier universe matches the concrete
commuting-tuple construction used by the proof below. -/
def StrictPointedDCPOHasAllLimits : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, IsDcpo (Obj i)) →
        (∀ i : O, IsAntisymmetricOrder (Obj i)) →
          (∀ i : O, HasLeastElement (Obj i)) →
            (∀ j : M, StrictScottContinuous (map j)) →
              ∃ L : Type (max u w), ∃ instL : Preorder L,
                @IsDcpo L instL ∧ @IsAntisymmetricOrder L instL ∧
                  @HasLeastElement L instL ∧
                    Nonempty (@StrictPointedLimitingConeData.{u, v, w, z, max u w}
                      O M shape Obj _ map L instL)

/-- Cocompleteness of `DCPO⊥!` in the current concrete-diagram interface, with
the same strict Scott-continuous morphism convention as
`StrictPointedDCPOHasAllLimits`.

Unlike the strict completeness component, no strict colimit construction is
formalized here yet; Theorem 3.3.4 therefore keeps this as local proof debt
rather than deriving it from the `DCPO` colimit theorem. -/
def StrictPointedDCPOHasAllColimits : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, IsDcpo (Obj i)) →
        (∀ i : O, IsAntisymmetricOrder (Obj i)) →
          (∀ i : O, HasLeastElement (Obj i)) →
            (∀ j : M, StrictScottContinuous (map j)) →
              ∃ Col : Type z, ∃ instCol : Preorder Col,
                @IsDcpo Col instCol ∧ @IsAntisymmetricOrder Col instCol ∧
                  @HasLeastElement Col instCol ∧
                    Nonempty (@StrictPointedColimitingCoconeData.{u, v, w, z, z}
                      O M shape Obj _ map Col instCol)

/-- Concrete function-space adjunction for `DCPO`: application and currying
identify continuous maps `C × D -> E` with continuous maps `C -> [D -> E]`.
The support theorem is proved after the bundled curry/uncurry definitions. -/
def DCPOFunctionSpaceAdjunction : Prop :=
  ∀ C D E : Type u, ∀ [Preorder C], ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo C → IsAntisymmetricOrder C →
      IsDcpo D → IsAntisymmetricOrder D →
        IsDcpo E → IsAntisymmetricOrder E →
          Nonempty (@OrderIsoData (ContFun (C × D) E) (ContFun C (ContFun D E))
            inferInstance inferInstance)

/-- Internal-hom comparison for `DCPO`: an exponential object is a partial-order
dcpo compared with the concrete continuous function-space carrier.  The
concrete comparison is proved below by choosing `ContFun D E` itself. -/
def DCPOInternalHomComparison : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo D → IsAntisymmetricOrder D →
      IsDcpo E → IsAntisymmetricOrder E →
        ∃ Exp : Type u, ∃ instExp : Preorder Exp,
          @IsDcpo Exp instExp ∧ @IsAntisymmetricOrder Exp instExp ∧
            Nonempty (@OrderIsoData Exp (ContFun D E) instExp inferInstance)

/-- Cartesian closedness of `DCPO`, split into the proved concrete
function-space adjunction and the internal-hom comparison with the ordinary
continuous function-space carrier. -/
def DCPOCartesianClosed : Prop :=
  DCPOFunctionSpaceAdjunction.{u} ∧ DCPOInternalHomComparison.{u}

/-- Object-class support for the strict function-space carrier used by
`DCPO⊥!`: strict continuous maps form a pointed partial-order dcpo. -/
def StrictPointedFunctionSpaceObjectSupport : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo D → IsAntisymmetricOrder D → HasLeastElement D →
      IsDcpo E → IsAntisymmetricOrder E → HasLeastElement E →
        @IsDcpo (StrictContFun D E) inferInstance ∧
          @IsAntisymmetricOrder (StrictContFun D E) inferInstance ∧
            @HasLeastElement (StrictContFun D E) inferInstance

/-- Strict-pointed internal-hom comparison for `DCPO⊥!`: an internal-hom object
is a pointed partial-order dcpo compared with the strict function-space
carrier.  The concrete comparison is proved below by choosing the strict
function-space carrier itself. -/
def StrictPointedInternalHomComparison : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo D → IsAntisymmetricOrder D → HasLeastElement D →
      IsDcpo E → IsAntisymmetricOrder E → HasLeastElement E →
        ∃ H : Type u, ∃ instH : Preorder H,
          @IsDcpo H instH ∧ @IsAntisymmetricOrder H instH ∧
            @HasLeastElement H instH ∧
              Nonempty (@OrderIsoData H (StrictContFun D E) instH inferInstance)

/-- Object/internal-hom component used in the monoidal-closed construction. -/
def StrictPointedDCPOMonoidalClosedCore : Prop :=
  StrictPointedFunctionSpaceObjectSupport.{u} ∧
    StrictPointedInternalHomComparison.{u}

/-- Concrete tensor-hom adjunction support for the strict pointed interface.  The
current carrier-level statement compares strict continuous maps out of the smash
product with strict continuous maps into the strict function-space carrier.  The
explicit `OrderBot` and bottom-separation hypotheses are the preorder-interface
side conditions used by the local smash-product construction. -/
def StrictPointedTensorHomAdjunction : Prop :=
  ∀ D E F : Type u, ∀ [Preorder D], ∀ [Preorder E], ∀ [Preorder F],
    ∀ [OrderBot D], ∀ [OrderBot E],
      IsDcpo D → IsAntisymmetricOrder D → HasLeastElement D →
        IsDcpo E → IsAntisymmetricOrder E → HasLeastElement E →
          IsDcpo F → IsAntisymmetricOrder F → HasLeastElement F →
            (∀ x : D, x ≤ ⊥ → x = ⊥) →
              (∀ y : E, y ≤ ⊥ → y = ⊥) →
                Nonempty
                  (@OrderIsoData (StrictContFun (SmashProduct D E) F)
                    (StrictContFun D (StrictContFun E F)) inferInstance inferInstance)

/-- Monoidal closedness of `DCPO⊥!` in the concrete local interface: the
strict function-space object/internal-hom data together with the smash-product
tensor-hom order isomorphism. -/
def StrictPointedDCPOMonoidalClosed : Prop :=
  StrictPointedDCPOMonoidalClosedCore.{u} ∧ StrictPointedTensorHomAdjunction.{u}

/-- Concrete function-space adjunction for `DCPO⊥` with non-strict morphisms.
The object hypotheses are pointed, but the hom-sets are ordinary
Scott-continuous maps. -/
def PointedDCPOFunctionSpaceAdjunction : Prop :=
  ∀ C D E : Type u, ∀ [Preorder C], ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo C → IsAntisymmetricOrder C → HasLeastElement C →
      IsDcpo D → IsAntisymmetricOrder D → HasLeastElement D →
        IsDcpo E → IsAntisymmetricOrder E → HasLeastElement E →
          Nonempty (@OrderIsoData (ContFun (C × D) E) (ContFun C (ContFun D E))
            inferInstance inferInstance)

/-- Pointed internal-hom comparison for `DCPO⊥`: an internal-hom object is
pointed and order-isomorphic to the ordinary continuous function-space carrier.
The concrete comparison is proved below by choosing `ContFun D E` itself. -/
def PointedDCPOInternalHomComparison : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo D → IsAntisymmetricOrder D → HasLeastElement D →
      IsDcpo E → IsAntisymmetricOrder E → HasLeastElement E →
        ∃ H : Type u, ∃ instH : Preorder H,
          @IsDcpo H instH ∧ @IsAntisymmetricOrder H instH ∧
            @HasLeastElement H instH ∧
              Nonempty (@OrderIsoData H (ContFun D E) instH inferInstance)

/-- Cartesian closedness of the pointed dcpo category, split into the proved
ordinary continuous function-space adjunction and the pointed internal-hom
comparison with the ordinary function-space carrier.  Morphisms are not
required to be strict here, matching `DCPO⊥`. -/
def PointedDCPOCartesianClosed : Prop :=
  PointedDCPOFunctionSpaceAdjunction.{u} ∧
    PointedDCPOInternalHomComparison.{u}

/-- The concrete target statement of Theorem 3.3.1 after expanding the book's
commuting-tuple construction.  The theorem below proves this predicate
directly. -/
def DCPOCompletenessStatement : Prop := DCPOHasAllLimits.{u, v, w, z}

/-- Statement form of Theorem 3.3.2.  The book cites external colimit
construction literature for this result: Markowsky [Mar77], Meseguer [Mes77],
Herrlich--Strecker [HS73, Theorem 23.14] via Lehmann--Smyth [LS81], and Fiech
[Fie92].  The current Lean declaration keeps the full universal property as an
explicit statement.  As in 3.3.1, the local preorder-based interface records
the partial-order side condition explicitly. -/
def DCPOCocompletenessStatement : Prop := DCPOHasAllColimits.{u, v, w, z}

/-- Target statement for the complete strict pointed dcpo category interface
used by Theorem 3.3.4. -/
def StrictPointedDCPOCompletenessStatement : Prop :=
  StrictPointedDCPOHasAllLimits.{u, v, w, z}

/-- Target statement for the cocomplete strict pointed dcpo category interface
used by Theorem 3.3.4. -/
def StrictPointedDCPOCocompletenessStatement : Prop :=
  StrictPointedDCPOHasAllColimits.{u, v, w, z}

/-- Theorem 3.3.1. PDF text: "DCPO has limits of arbitrary diagrams."

Current Lean spelling: for any concrete diagram of partial-order dcpos and
Scott-continuous maps, the commuting-tuple carrier is a partial-order dcpo and
carries the limiting-cone universal property against partial-order dcpo cone
vertices. -/
theorem theorem_3_3_1_dcpo_complete :
    DCPOCompletenessStatement.{u, v, w, z} := by
  intro O M shape Obj _instObj map hObj hantisymm hmap
  refine ⟨DiagramLimitCarrier shape Obj map, inferInstance, ?_, ?_, ?_⟩
  · exact DiagramLimitCarrier.isDcpo hObj hantisymm hmap
  · exact DiagramLimitCarrier.antisymmetric hantisymm
  · refine ⟨?_⟩
    refine
      { isDcpo := DiagramLimitCarrier.isDcpo hObj hantisymm hmap
        cone := DiagramLimitCarrier.limitCone
        leg_continuous := DiagramLimitCarrier.proj_scottContinuous hObj hantisymm hmap
        lift := ?_
        lift_continuous := ?_
        lift_fac := ?_
        lift_unique := ?_ }
    · intro E _instE _hE _hEanti c _hc
      exact DiagramLimitCarrier.lift c
    · intro E _instE _hE _hEanti c hc
      exact DiagramLimitCarrier.lift_scottContinuous c hc
    · intro E _instE _hE _hEanti c _hc i x
      rfl
    · intro E _instE _hE _hEanti c _hc g _hg hfac x
      apply Subtype.ext
      funext i
      exact hfac i x

/-- Theorem 3.3.4, complete component. PDF text component: "`DCPO⊥!` is
complete."

Current Lean spelling: for any concrete diagram of pointed partial-order dcpos
and strict Scott-continuous maps, the same commuting-tuple carrier as in
Theorem 3.3.1 has a coordinatewise least element, strict projection legs, and a
strict universal mediating map from every strict cone. -/
theorem theorem_3_3_4_strict_pointed_dcpo_complete :
    StrictPointedDCPOCompletenessStatement.{u, v, w, z} := by
  intro O M shape Obj _instObj map hObj hantisymm hpointed hmap
  refine ⟨DiagramLimitCarrier shape Obj map, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact DiagramLimitCarrier.isDcpo hObj hantisymm (fun j => (hmap j).1)
  · exact DiagramLimitCarrier.antisymmetric hantisymm
  · exact DiagramLimitCarrier.hasLeastElement hantisymm hpointed hmap
  · refine ⟨?_⟩
    refine
      { isDcpo := DiagramLimitCarrier.isDcpo hObj hantisymm (fun j => (hmap j).1)
        antisymmetric := DiagramLimitCarrier.antisymmetric hantisymm
        pointed := DiagramLimitCarrier.hasLeastElement hantisymm hpointed hmap
        cone := DiagramLimitCarrier.limitCone
        leg_strict := DiagramLimitCarrier.proj_strictScottContinuous hObj hantisymm hpointed hmap
        lift := ?_
        lift_strict := ?_
        lift_fac := ?_
        lift_unique := ?_ }
    · intro E _instE _hE _hEanti _hEpointed c _hc
      exact DiagramLimitCarrier.lift c
    · intro E _instE _hE _hEanti _hEpointed c hc
      exact DiagramLimitCarrier.lift_strictScottContinuous c hc
    · intro E _instE _hE _hEanti _hEpointed c _hc i x
      rfl
    · intro E _instE _hE _hEanti _hEpointed c _hc g _hg hfac x
      apply Subtype.ext
      funext i
      exact hfac i x

/-- Theorem 3.3.4, cocomplete component. PDF text component: "`DCPO⊥!` is
cocomplete."

The PDF states this strict pointed cocompleteness component without an
element-level proof in the surrounding text and without a separate external
source citation.  Following the project policy, this is registered as local
proof debt in `formalization_status.md`. -/
theorem theorem_3_3_4_strict_pointed_dcpo_cocomplete : StrictPointedDCPOCocompletenessStatement.{u, v, w, z} := by admit

/-- Theorem 3.3.2. PDF text: "DCPO has colimits of arbitrary diagrams."

Current Lean spelling: documented external theorem.  The PDF cites Markowsky
[Mar77], Meseguer [Mes77], Herrlich--Strecker [HS73, Theorem 23.14] via
Lehmann--Smyth [LS81], and Fiech [Fie92] for this colimit construction. -/
axiom theorem_3_3_2_dcpo_cocomplete :
    DCPOCocompletenessStatement.{u, v, w, z}

/-- Auxiliary packaging lemma for Theorem 3.3.3. PDF text: "DCPO is cartesian closed,
complete and cocomplete."

Current Lean spelling: package a `DCPO` cartesian-closed interface and the
documented external cocompleteness theorem together with the constructed
commuting-tuple completeness theorem above.  The concrete cartesian-closed
interface is proved later by choosing the ordinary continuous function-space
carrier itself. -/
theorem theorem_3_3_3_dcpo_cartesian_closed_complete_cocomplete_of_cartesianClosed :
    DCPOCartesianClosed.{u} →
      DCPOCartesianClosed.{u} ∧ DCPOHasAllLimits.{u, v, w, z} ∧
        DCPOHasAllColimits.{u, v, w, z} := by
  intro hClosed
  exact ⟨hClosed, theorem_3_3_1_dcpo_complete, theorem_3_3_2_dcpo_cocomplete⟩

/-- Theorem 3.3.4. PDF text: "DCPO⊥! is monoidal closed, complete and
cocomplete."

Current Lean spelling: package a strict-pointed monoidal-closed interface with
the strict-pointed complete/cocomplete interfaces.  The strict completeness
component is constructed above from the commuting-tuple carrier; the strict
cocompleteness component is the registered local proof debt above.  The
concrete monoidal-closed interface is proved later in the file from the strict
function-space carrier and internal-hom comparison; the smash-product
tensor-hom order isomorphism is packaged separately as
`StrictPointedTensorHomAdjunction`. -/
theorem theorem_3_3_4_strict_pointed_dcpo_monoidal_closed_complete_cocomplete_of_monoidalClosed :
    StrictPointedDCPOMonoidalClosed.{u} →
      StrictPointedDCPOCompletenessStatement.{u, v, w, z} →
        StrictPointedDCPOMonoidalClosed.{u} ∧
          StrictPointedDCPOHasAllLimits.{u, v, w, z} ∧
            StrictPointedDCPOHasAllColimits.{u, v, w, z} := by
  intro hClosed hComplete
  exact ⟨hClosed, hComplete, theorem_3_3_4_strict_pointed_dcpo_cocomplete⟩

/-- Auxiliary identity lemma for Theorem 3.3.5. PDF text: "DCPO⊥ is cartesian
closed."

Current Lean spelling: pointed `DCPO⊥` is cartesian closed when the pointed
internal-hom comparison data with the ordinary continuous function-space carrier
is supplied.  The concrete theorem below supplies that comparison by choosing
the ordinary function-space carrier itself; morphisms are intentionally not
strict. -/
theorem theorem_3_3_5_pointed_dcpo_cartesian_closed_of_cartesianClosed
    (h : PointedDCPOCartesianClosed.{u}) : PointedDCPOCartesianClosed.{u} :=
  h

/-- Legacy weak carrier/projection witness for Theorem 3.3.7.

PDF text excerpt for Theorem 3.3.7: "Let `⟨(D_n)_{n∈N},
(e_mn : D_n → D_m)_{n≤m∈N}⟩` be an expanding sequence in `DCPO`. Define an
object `D` by compatible tuples `x_n = p_nm(x_m)`; projections `p_m : D → D_m`;
and embeddings `e_m : D_m → D` by the stage-coordinate formula. Then the maps
`(e_m,p_m)` form embedding-projection pairs with `⋁_m e_m ∘ p_m = id_D`,
`⟨D,(p_n)⟩` is a limit of the projection diagram, and `⟨D,(e_n)⟩` is a colimit
of the embedding diagram."

Current Lean spelling of this legacy witness: it only records the explicit
bilimit carrier predicate and the existence of the coordinate projection maps;
the full limit-colimit content is represented by the later projection-cone and
embedding-cocone theorems. -/
structure ExpandingSequence.BilimitTheoremData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) : Prop where
  carrier_eq : ∀ x : Bilimit S, BilimitCarrier S x.1
  projection : ∀ n : Nat, Nonempty (Bilimit S → D n)

/-- Theorem 3.3.7 legacy partial carrier/projection data for the bilimit of an
expanding sequence.  Full limit-colimit universal properties are tracked and
proved separately below. -/
theorem theorem_3_3_7_expanding_sequence_bilimit_legacy
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.BilimitTheoremData S := by
  exact ⟨fun x => x.2, fun n => ⟨Bilimit.proj S n⟩⟩

instance bilimitPreorder
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) :
    Preorder (Bilimit S) where
  le x y := ∀ n : Nat, x.1 n ≤ y.1 n
  le_refl x n := le_rfl
  le_trans x y z hxy hyz n := le_trans (hxy n) (hyz n)

/-- A cocone over an expanding sequence, with maps `f_n : D_n -> E` commuting
with the embeddings `e_{n,m}`. -/
structure ExpandingSequence.Cocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (E : Type u) [Preorder E] where
  f : ∀ n : Nat, D n → E
  continuous : ∀ n : Nat, ScottContinuous (f n)
  commute : ∀ {n m : Nat} (h : n ≤ m) (x : D n), f m (S.e h x) = f n x

/-- A cone over the projection side of an expanding sequence, with maps
`p_n : E -> D_n` commuting with the projections `p_{n,m}`. -/
structure ExpandingSequence.ProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (E : Type u) [Preorder E] where
  p : ∀ n : Nat, E → D n
  continuous : ∀ n : Nat, ScottContinuous (p n)
  commute : ∀ {n m : Nat} (h : n ≤ m) (x : E), S.p h (p m x) = p n x

/-- A map between cocone carriers mediates the two cocones. -/
def ExpandingSequence.CoconeMediates
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E F : Type u} [Preorder E] [Preorder F]
    (C : ExpandingSequence.Cocone S E) (C' : ExpandingSequence.Cocone S F)
    (u : E → F) : Prop :=
  ScottContinuous u ∧ ∀ n : Nat, ∀ x : D n, u (C.f n x) = C'.f n x

/-- A cocone is colimiting in `DCPO` when every cocone with dcpo carrier has a
unique continuous mediating map from its carrier. -/
def ExpandingSequence.IsColimitingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (_hE : IsDcpo E)
    (_hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    (C : ExpandingSequence.Cocone S E) : Prop :=
  ∀ F : Type u, ∀ [Preorder F], IsDcpo F →
    (∀ x y : F, x ≤ y → y ≤ x → x = y) → ∀ C' : ExpandingSequence.Cocone S F,
    ∃ u : E → F, ExpandingSequence.CoconeMediates S C C' u ∧
      ∀ v : E → F, ExpandingSequence.CoconeMediates S C C' v → ∀ y : E, v y = u y

/-- A map between projection-cone carriers mediates the two projection cones. -/
def ExpandingSequence.ProjectionConeMediates
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E F : Type u} [Preorder E] [Preorder F]
    (C : ExpandingSequence.ProjectionCone S E)
    (C' : ExpandingSequence.ProjectionCone S F) (u : E → F) : Prop :=
  ScottContinuous u ∧ ∀ n : Nat, ∀ x : E, C'.p n (u x) = C.p n x

/-- A map represented as the embedding half of an e-p-pair. -/
def EmbeddingMorphism {E F : Type u} [Preorder E] [Preorder F] (u : E → F) : Prop :=
  Nonempty {ep : EPPair E F // ∀ x : E, ep.e x = u x}

/-- A map represented as the projection half of an e-p-pair. -/
def ProjectionMorphism {E F : Type u} [Preorder E] [Preorder F] (u : E → F) : Prop :=
  Nonempty {ep : EPPair F E // ∀ x : E, ep.p x = u x}

/-- A projection cone is limiting in `DCPO` when every projection cone with dcpo
carrier has a unique continuous mediating map into its carrier. -/
def ExpandingSequence.IsLimitingProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (_hE : IsDcpo E)
    (_hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    (C : ExpandingSequence.ProjectionCone S E) : Prop :=
  ∀ F : Type u, ∀ [Preorder F], IsDcpo F →
    (∀ x y : F, x ≤ y → y ≤ x → x = y) → ∀ C' : ExpandingSequence.ProjectionCone S F,
    ∃ u : F → E, ExpandingSequence.ProjectionConeMediates S C' C u ∧
      ∀ v : F → E, ExpandingSequence.ProjectionConeMediates S C' C v → ∀ y : F, v y = u y

/-- The e-p-pair decomposition of the cocone maps in Lemma 3.3.8.

PDF text excerpt: a cocone `⟨E,(f_n)_{n∈N}⟩` is colimiting iff "there are
Scott-continuous functions `g_n : E → D_n` such that each `(f_n,g_n)` is an
e-p-pair and, secondly, `⋁_{n∈N} f_n ∘ g_n = id_E` holds."

Current Lean spelling: the projections are represented by the projection halves
of `EPPair (D n) E`, and the supremum identity is recorded pointwise as an
`IsSup` statement for `{f_n(g_n(y)) | n ∈ Nat}`. -/
structure ExpandingSequence.CoconeEPDecomposition
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E) where
  ep : ∀ n : Nat, EPPair (D n) E
  ep_e : ∀ n : Nat, ∀ x : D n, (ep n).e x = C.f n x
  sup_identity :
    ∀ y : E, IsSup ({z : E | ∃ n : Nat, z = (ep n).e ((ep n).p y)} : Set E) y

/-- The statement form of Lemma 3.3.8.

PDF text excerpt: "Let `⟨E,(f_n)_{n∈N}⟩` be a cocone for the expanding sequence
`⟨(D_n)_{n∈N},(e_mn : D_n → D_m)_{n≤m∈N}⟩`. It is colimiting if and only if,
firstly, there are Scott-continuous functions `g_n : E → D_n` such that each
`(f_n,g_n)` is an e-p-pair and, secondly, `⋁_{n∈N} f_n ∘ g_n = id_E` holds."

Current Lean spelling: the iff is stated for preorder carriers under explicit
stage dcpo/antisymmetry hypotheses and explicit dcpo/antisymmetry hypotheses on
the cocone carrier. -/
def ExpandingSequence.ColimitingCoconeCriterionFull
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) :
  Prop :=
  (∀ n : Nat, IsDcpo (D n)) →
  (∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) →
  ∀ E : Type u, ∀ [Preorder E], ∀ hE : IsDcpo E,
    ∀ hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y, ∀ C : ExpandingSequence.Cocone S E,
    ExpandingSequence.IsColimitingCocone S hE hEanti C ↔
      Nonempty (ExpandingSequence.CoconeEPDecomposition S C)

/-- A cocone whose legs are embeddings, represented by e-p-pairs whose embedding
components are the cocone maps. -/
structure ExpandingSequence.CoconeEmbeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E) where
  ep : ∀ n : Nat, EPPair (D n) E
  ep_e : ∀ n : Nat, ∀ x : D n, (ep n).e x = C.f n x

namespace ExpandingSequence.CoconeEmbeddingData

variable {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
variable {S : ExpandingSequence D}
variable {E : Type u} [Preorder E]
variable {C : ExpandingSequence.Cocone S E}
variable (hC : ExpandingSequence.CoconeEmbeddingData S C)

/-- Projection coordinates from an embedding cocone commute up to the first
inequality needed for the bilimit carrier equation. -/
theorem projection_commute_le_left {n m : Nat} (h : n ≤ m) (y : E) :
    S.p h ((hC.ep m).p y) ≤ (hC.ep n).p y := by
  apply ((hC.ep n).toAdjunction.adj (S.p h ((hC.ep m).p y)) y).2
  calc
    (hC.ep n).e (S.p h ((hC.ep m).p y))
        = C.f n (S.p h ((hC.ep m).p y)) := hC.ep_e n _
    _ = C.f m (S.e h (S.p h ((hC.ep m).p y))) := (C.commute h _).symm
    _ ≤ C.f m ((hC.ep m).p y) := (C.continuous m).1 (S.below h ((hC.ep m).p y))
    _ = (hC.ep m).e ((hC.ep m).p y) := (hC.ep_e m _).symm
    _ ≤ y := (hC.ep m).below y

/-- Projection coordinates from an embedding cocone commute up to the second
inequality needed for the bilimit carrier equation. -/
theorem projection_commute_le_right {n m : Nat} (h : n ≤ m) (y : E) :
    (hC.ep n).p y ≤ S.p h ((hC.ep m).p y) := by
  have hleToM : S.e h ((hC.ep n).p y) ≤ (hC.ep m).p y := by
    apply ((hC.ep m).toAdjunction.adj (S.e h ((hC.ep n).p y)) y).2
    calc
      (hC.ep m).e (S.e h ((hC.ep n).p y))
          = C.f m (S.e h ((hC.ep n).p y)) := hC.ep_e m _
      _ = C.f n ((hC.ep n).p y) := C.commute h _
      _ = (hC.ep n).e ((hC.ep n).p y) := (hC.ep_e n _).symm
      _ ≤ y := (hC.ep n).below y
  have hmono := (S.continuous_p h).1 hleToM
  simpa [S.retract h ((hC.ep n).p y)] using hmono

/-- With explicit antisymmetry for the stage orders, the projection coordinates
of an embedding cocone form a compatible bilimit tuple. -/
theorem projection_commute_of_antisymm
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {n m : Nat} (h : n ≤ m) (y : E) :
    (hC.ep n).p y = S.p h ((hC.ep m).p y) :=
  hantisymm n _ _
    (hC.projection_commute_le_right h y)
    (hC.projection_commute_le_left h y)

/-- The projection part of the e-p-pair in Proposition 3.3.9, constructed as a
map into the explicit bilimit carrier under explicit antisymmetry of the stage
orders. -/
def toBilimitOfAntisymm
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    E → Bilimit S :=
  fun y => ⟨fun n => (hC.ep n).p y, by
    intro n m h
    exact hC.projection_commute_of_antisymm hantisymm h y⟩

/-- The projection map `E -> Bilimit S` built from an embedding cocone is
monotone, because each coordinate projection in the e-p-pairs is monotone. -/
theorem toBilimitOfAntisymm_monotone
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    Monotone (hC.toBilimitOfAntisymm hantisymm) := by
  intro x y hxy n
  exact ((hC.ep n).continuous_p).1 hxy

/-- The projection map `E -> Bilimit S` built from an embedding cocone is
Scott-continuous.  Suprema in the explicit bilimit order are checked
coordinatewise. -/
theorem toBilimitOfAntisymm_scottContinuous
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ScottContinuous (hC.toBilimitOfAntisymm hantisymm) := by
  constructor
  · exact hC.toBilimitOfAntisymm_monotone hantisymm
  · intro A y hA hy
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact hC.toBilimitOfAntisymm_monotone hantisymm (hy.1 ha)
    · intro b hb n
      have hcoordSup : IsSup ((hC.ep n).p '' A) ((hC.ep n).p y) :=
        ((hC.ep n).continuous_p).2 hA hy
      exact hcoordSup.2 (b.1 n) (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hb ⟨a, ha, rfl⟩ n)

end ExpandingSequence.CoconeEmbeddingData

namespace ExpandingSequence.CoconeEPDecomposition

variable {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
variable {S : ExpandingSequence D}
variable {E : Type u} [Preorder E]
variable {C : ExpandingSequence.Cocone S E}

/-- The e-p-pair decomposition in Lemma 3.3.8 forgets to the embedding-cocone
data used in Proposition 3.3.9. -/
def toEmbeddingData (h : ExpandingSequence.CoconeEPDecomposition S C) :
    ExpandingSequence.CoconeEmbeddingData S C where
  ep := h.ep
  ep_e := h.ep_e

/-- The source-side family `{f_n(g_n(y))}` from Lemma 3.3.8. -/
def SourceImage (h : ExpandingSequence.CoconeEPDecomposition S C) (y : E) : Set E :=
  {z | ∃ n : Nat, z = (h.ep n).e ((h.ep n).p y)}

/-- The source-side family `{f_n(g_n(y))}` is directed. -/
theorem sourceImage_directed
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (y : E) : DirectedSet (h.SourceImage y) := by
  constructor
  · exact ⟨(h.ep 0).e ((h.ep 0).p y), ⟨0, rfl⟩⟩
  · intro a ha b hb
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    let k : Nat := max n m
    refine ⟨(h.ep k).e ((h.ep k).p y), ⟨k, rfl⟩, ?_, ?_⟩
    · have hnk : n ≤ k := Nat.le_max_left n m
      have hcoord : (h.ep n).p y = S.p hnk ((h.ep k).p y) := by
        simpa [toEmbeddingData] using
          (h.toEmbeddingData.projection_commute_of_antisymm hantisymm hnk y)
      calc
        (h.ep n).e ((h.ep n).p y)
            = C.f n ((h.ep n).p y) := h.ep_e n _
        _ = C.f n (S.p hnk ((h.ep k).p y)) := by rw [hcoord]
        _ = C.f k (S.e hnk (S.p hnk ((h.ep k).p y))) :=
              (C.commute hnk (S.p hnk ((h.ep k).p y))).symm
        _ ≤ C.f k ((h.ep k).p y) :=
              (C.continuous k).1 (S.below hnk ((h.ep k).p y))
        _ = (h.ep k).e ((h.ep k).p y) := (h.ep_e k _).symm
    · have hmk : m ≤ k := Nat.le_max_right n m
      have hcoord : (h.ep m).p y = S.p hmk ((h.ep k).p y) := by
        simpa [toEmbeddingData] using
          (h.toEmbeddingData.projection_commute_of_antisymm hantisymm hmk y)
      calc
        (h.ep m).e ((h.ep m).p y)
            = C.f m ((h.ep m).p y) := h.ep_e m _
        _ = C.f m (S.p hmk ((h.ep k).p y)) := by rw [hcoord]
        _ = C.f k (S.e hmk (S.p hmk ((h.ep k).p y))) :=
              (C.commute hmk (S.p hmk ((h.ep k).p y))).symm
        _ ≤ C.f k ((h.ep k).p y) :=
              (C.continuous k).1 (S.below hmk ((h.ep k).p y))
        _ = (h.ep k).e ((h.ep k).p y) := (h.ep_e k _).symm

/-- The target-side family `{f'_n(g_n(y))}` used to define the mediating map
from a decomposed cocone to another cocone. -/
def TargetImage (h : ExpandingSequence.CoconeEPDecomposition S C)
    {F : Type u} [Preorder F] (C' : ExpandingSequence.Cocone S F) (y : E) : Set F :=
  {z | ∃ n : Nat, z = C'.f n ((h.ep n).p y)}

/-- The target-side family `{f'_n(g_n(y))}` is directed. -/
theorem targetImage_directed
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (C' : ExpandingSequence.Cocone S F) (y : E) :
    DirectedSet (h.TargetImage C' y) := by
  constructor
  · exact ⟨C'.f 0 ((h.ep 0).p y), ⟨0, rfl⟩⟩
  · intro a ha b hb
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    let k : Nat := max n m
    refine ⟨C'.f k ((h.ep k).p y), ⟨k, rfl⟩, ?_, ?_⟩
    · have hnk : n ≤ k := Nat.le_max_left n m
      have hcoord : (h.ep n).p y = S.p hnk ((h.ep k).p y) := by
        simpa [toEmbeddingData] using
          (h.toEmbeddingData.projection_commute_of_antisymm hantisymm hnk y)
      calc
        C'.f n ((h.ep n).p y)
            = C'.f n (S.p hnk ((h.ep k).p y)) := by rw [hcoord]
        _ = C'.f k (S.e hnk (S.p hnk ((h.ep k).p y))) :=
              (C'.commute hnk (S.p hnk ((h.ep k).p y))).symm
        _ ≤ C'.f k ((h.ep k).p y) :=
              (C'.continuous k).1 (S.below hnk ((h.ep k).p y))
    · have hmk : m ≤ k := Nat.le_max_right n m
      have hcoord : (h.ep m).p y = S.p hmk ((h.ep k).p y) := by
        simpa [toEmbeddingData] using
          (h.toEmbeddingData.projection_commute_of_antisymm hantisymm hmk y)
      calc
        C'.f m ((h.ep m).p y)
            = C'.f m (S.p hmk ((h.ep k).p y)) := by rw [hcoord]
        _ = C'.f k (S.e hmk (S.p hmk ((h.ep k).p y))) :=
              (C'.commute hmk (S.p hmk ((h.ep k).p y))).symm
        _ ≤ C'.f k ((h.ep k).p y) :=
              (C'.continuous k).1 (S.below hmk ((h.ep k).p y))

/-- The canonical mediating map supplied by a Lemma 3.3.8 e-p-pair
decomposition, defined as `y ↦ ⋁_n f'_n(g_n(y))`. -/
noncomputable def mediatingSup
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (C' : ExpandingSequence.Cocone S F) : E → F :=
  fun y => Classical.choose (hF _ (h.targetImage_directed hantisymm C' y))

/-- The canonical mediating map is the supremum of its target-side image family. -/
theorem mediatingSup_isSup
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (C' : ExpandingSequence.Cocone S F) (y : E) :
    IsSup (h.TargetImage C' y) (h.mediatingSup hantisymm hF C' y) :=
  Classical.choose_spec (hF _ (h.targetImage_directed hantisymm C' y))

/-- The canonical mediating map is monotone. -/
theorem mediatingSup_monotone
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (C' : ExpandingSequence.Cocone S F) :
    Monotone (h.mediatingSup hantisymm hF C') := by
  intro x y hxy
  exact (h.mediatingSup_isSup hantisymm hF C' x).2
    (h.mediatingSup hantisymm hF C' y) (by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      calc
        C'.f n ((h.ep n).p x)
            ≤ C'.f n ((h.ep n).p y) := (C'.continuous n).1 ((h.ep n).continuous_p.1 hxy)
        _ ≤ h.mediatingSup hantisymm hF C' y :=
            (h.mediatingSup_isSup hantisymm hF C' y).1 ⟨n, rfl⟩)

/-- The canonical mediating map preserves directed suprema. -/
theorem mediatingSup_scottContinuous
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (C' : ExpandingSequence.Cocone S F) :
    ScottContinuous (h.mediatingSup hantisymm hF C') := by
  constructor
  · exact h.mediatingSup_monotone hantisymm hF C'
  · intro A y hA hy
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact h.mediatingSup_monotone hantisymm hF C' (hy.1 ha)
    · intro b hb
      exact (h.mediatingSup_isSup hantisymm hF C' y).2 b (by
        intro z hz
        rcases hz with ⟨n, rfl⟩
        have hprojSup : IsSup ((h.ep n).p '' A) ((h.ep n).p y) :=
          ((h.ep n).continuous_p).2 hA hy
        have hstageSup :
            IsSup (C'.f n '' ((h.ep n).p '' A)) (C'.f n ((h.ep n).p y)) :=
          (C'.continuous n).2
            (DirectedSet.image ((h.ep n).continuous_p).1 hA) hprojSup
        exact hstageSup.2 b (by
          intro w hw
          rcases hw with ⟨ga, hga, rfl⟩
          rcases hga with ⟨a, ha, rfl⟩
          calc
            C'.f n ((h.ep n).p a)
                ≤ h.mediatingSup hantisymm hF C' a :=
                    (h.mediatingSup_isSup hantisymm hF C' a).1 ⟨n, rfl⟩
            _ ≤ b := hb ⟨a, ha, rfl⟩))

/-- At a cocone stage point `f_n(x)`, the target-side image family has supremum
`f'_n(x)`. -/
theorem targetImage_stage_isSup
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (C' : ExpandingSequence.Cocone S F)
    (n : Nat) (x : D n) :
    IsSup (h.TargetImage C' (C.f n x)) (C'.f n x) := by
  have hpn : (h.ep n).p (C.f n x) = x := by
    calc
      (h.ep n).p (C.f n x)
          = (h.ep n).p ((h.ep n).e x) := by rw [(h.ep_e n x).symm]
      _ = x := (h.ep n).retract x
  constructor
  · intro z hz
    rcases hz with ⟨m, rfl⟩
    rcases Nat.le_total n m with hnm | hmn
    · have hpm : (h.ep m).p (C.f n x) = S.e hnm x := by
        calc
          (h.ep m).p (C.f n x)
              = (h.ep m).p (C.f m (S.e hnm x)) := by rw [(C.commute hnm x).symm]
          _ = (h.ep m).p ((h.ep m).e (S.e hnm x)) := by
              rw [(h.ep_e m (S.e hnm x)).symm]
          _ = S.e hnm x := (h.ep m).retract (S.e hnm x)
      calc
        C'.f m ((h.ep m).p (C.f n x))
            = C'.f m (S.e hnm x) := by rw [hpm]
        _ = C'.f n x := C'.commute hnm x
        _ ≤ C'.f n x := le_rfl
    · have hcoord : (h.ep m).p (C.f n x) = S.p hmn ((h.ep n).p (C.f n x)) := by
        simpa [toEmbeddingData] using
          (h.toEmbeddingData.projection_commute_of_antisymm hantisymm hmn (C.f n x))
      calc
        C'.f m ((h.ep m).p (C.f n x))
            = C'.f m (S.p hmn x) := by rw [hcoord, hpn]
        _ = C'.f n (S.e hmn (S.p hmn x)) :=
            (C'.commute hmn (S.p hmn x)).symm
        _ ≤ C'.f n x := (C'.continuous n).1 (S.below hmn x)
  · intro b hb
    exact hb ⟨n, by rw [hpn]⟩

/-- The canonical supremum map commutes with the source and target cocone legs. -/
theorem mediatingSup_commute
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (hFanti : ∀ x y : F, x ≤ y → y ≤ x → x = y)
    (C' : ExpandingSequence.Cocone S F) :
    ∀ n : Nat, ∀ x : D n,
      h.mediatingSup hantisymm hF C' (C.f n x) = C'.f n x := by
  intro n x
  have hchosen := h.mediatingSup_isSup hantisymm hF C' (C.f n x)
  have hstage := h.targetImage_stage_isSup hantisymm C' n x
  exact hFanti _ _
    (hchosen.2 (C'.f n x) hstage.1)
    (hstage.2 (h.mediatingSup hantisymm hF C' (C.f n x)) hchosen.1)

/-- The canonical supremum map is a cocone-mediating morphism. -/
theorem mediatingSup_mediates
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (hFanti : ∀ x y : F, x ≤ y → y ≤ x → x = y)
    (C' : ExpandingSequence.Cocone S F) :
    ExpandingSequence.CoconeMediates S C C' (h.mediatingSup hantisymm hF C') := by
  exact ⟨h.mediatingSup_scottContinuous hantisymm hF C',
    h.mediatingSup_commute hantisymm hF hFanti C'⟩

/-- Any cocone-mediating map out of a decomposed cocone agrees with the canonical
supremum map. -/
theorem mediatingSup_unique
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (hFanti : ∀ x y : F, x ≤ y → y ≤ x → x = y)
    (C' : ExpandingSequence.Cocone S F)
    (v : E → F) (hv : ExpandingSequence.CoconeMediates S C C' v) :
    ∀ y : E, v y = h.mediatingSup hantisymm hF C' y := by
  intro y
  have hsourceSup : IsSup (h.SourceImage y) y := by
    simpa [SourceImage] using h.sup_identity y
  have hvSourceSup : IsSup (v '' h.SourceImage y) (v y) :=
    hv.1.2 (h.sourceImage_directed hantisymm y) hsourceSup
  have hvTargetSup : IsSup (h.TargetImage C' y) (v y) := by
    constructor
    · intro z hz
      rcases hz with ⟨n, rfl⟩
      have hsrcMem : (h.ep n).e ((h.ep n).p y) ∈ h.SourceImage y := ⟨n, rfl⟩
      have hsrcLe : (h.ep n).e ((h.ep n).p y) ≤ y := hsourceSup.1 hsrcMem
      calc
        C'.f n ((h.ep n).p y)
            = v (C.f n ((h.ep n).p y)) := (hv.2 n ((h.ep n).p y)).symm
        _ = v ((h.ep n).e ((h.ep n).p y)) := by
            rw [(h.ep_e n ((h.ep n).p y)).symm]
        _ ≤ v y := hv.1.1 hsrcLe
    · intro b hb
      exact hvSourceSup.2 b (by
        intro w hw
        rcases hw with ⟨z, hz, rfl⟩
        rcases hz with ⟨n, rfl⟩
        calc
          v ((h.ep n).e ((h.ep n).p y))
              = v (C.f n ((h.ep n).p y)) := by
                  rw [h.ep_e n ((h.ep n).p y)]
          _ = C'.f n ((h.ep n).p y) := hv.2 n ((h.ep n).p y)
          _ ≤ b := hb ⟨n, rfl⟩)
  have hchosen := h.mediatingSup_isSup hantisymm hF C' y
  exact hFanti _ _
    (hvTargetSup.2 (h.mediatingSup hantisymm hF C' y) hchosen.1)
    (hchosen.2 (v y) hvTargetSup.1)

end ExpandingSequence.CoconeEPDecomposition

/-- Lemma 3.3.8 sufficiency direction: an e-p-pair decomposition with
`⋁_n f_n(g_n(y)) = y` makes the cocone colimiting. -/
theorem ExpandingSequence.isColimitingCocone_of_epDecomposition
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    {C : ExpandingSequence.Cocone S E}
    (h : ExpandingSequence.CoconeEPDecomposition S C) :
    ExpandingSequence.IsColimitingCocone S hE hEanti C := by
  intro F _ hF hFanti C'
  refine ⟨h.mediatingSup hantisymm hF C', ?_, ?_⟩
  · exact h.mediatingSup_mediates hantisymm hF hFanti C'
  · intro v hv y
    exact h.mediatingSup_unique hantisymm hF hFanti C' v hv y

/-- The image family `{f_n(p_n x) | n ∈ Nat}` whose directed supremum is the
mediating map from the bilimit to a cocone carrier in Theorem 3.3.7 and
Proposition 3.3.9. -/
def ExpandingSequence.BilimitToCoconeImage
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E)
    (x : Bilimit S) : Set E :=
  {z | ∃ n : Nat, z = C.f n (Bilimit.proj S n x)}

/-- The family `{f_n(p_n x)}` is directed.  This is the directedness calculation
used in the proof of Theorem 3.3.7 to define the mediating map
`⋁_n f_n(p_n x)`. -/
theorem ExpandingSequence.bilimitToCoconeImage_directed
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E)
    (x : Bilimit S) : DirectedSet (ExpandingSequence.BilimitToCoconeImage S C x) := by
  constructor
  · exact ⟨C.f 0 (Bilimit.proj S 0 x), ⟨0, rfl⟩⟩
  · intro a ha b hb
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    let k : Nat := max n m
    refine ⟨C.f k (Bilimit.proj S k x), ⟨k, rfl⟩, ?_, ?_⟩
    · have hnk : n ≤ k := Nat.le_max_left n m
      calc
        C.f n (Bilimit.proj S n x)
            = C.f n (S.p hnk (Bilimit.proj S k x)) := by
                congr
                simpa [Bilimit.proj, k] using x.2 hnk
        _ = C.f k (S.e hnk (S.p hnk (Bilimit.proj S k x))) :=
                (C.commute hnk (S.p hnk (Bilimit.proj S k x))).symm
        _ ≤ C.f k (Bilimit.proj S k x) :=
                (C.continuous k).1 (S.below hnk (Bilimit.proj S k x))
    · have hmk : m ≤ k := Nat.le_max_right n m
      calc
        C.f m (Bilimit.proj S m x)
            = C.f m (S.p hmk (Bilimit.proj S k x)) := by
                congr
                simpa [Bilimit.proj, k] using x.2 hmk
        _ = C.f k (S.e hmk (S.p hmk (Bilimit.proj S k x))) :=
                (C.commute hmk (S.p hmk (Bilimit.proj S k x))).symm
        _ ≤ C.f k (Bilimit.proj S k x) :=
                (C.continuous k).1 (S.below hmk (Bilimit.proj S k x))

/-- The canonical mediating map `Bilimit S -> E`, defined pointwise as the
supremum `⋁_n f_n(p_n x)` when the cocone carrier is a dcpo. -/
noncomputable def ExpandingSequence.bilimitToCoconeSup
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (C : ExpandingSequence.Cocone S E) : Bilimit S → E :=
  fun x => Classical.choose (hE _ (ExpandingSequence.bilimitToCoconeImage_directed S C x))

/-- The canonical mediating map is indeed the supremum of the family
`{f_n(p_n x)}`. -/
theorem ExpandingSequence.bilimitToCoconeSup_isSup
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (C : ExpandingSequence.Cocone S E) (x : Bilimit S) :
    IsSup (ExpandingSequence.BilimitToCoconeImage S C x)
      (ExpandingSequence.bilimitToCoconeSup S hE C x) :=
  Classical.choose_spec (hE _
    (ExpandingSequence.bilimitToCoconeImage_directed S C x))

/-- Each stage component `f_n(p_n x)` lies below the canonical supremum
`⋁_n f_n(p_n x)`. -/
theorem ExpandingSequence.bilimitToCocone_le_sup
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (C : ExpandingSequence.Cocone S E) (x : Bilimit S) (n : Nat) :
    C.f n (Bilimit.proj S n x) ≤ ExpandingSequence.bilimitToCoconeSup S hE C x :=
  (ExpandingSequence.bilimitToCoconeSup_isSup S hE C x).1 ⟨n, rfl⟩

/-- The canonical supremum map is monotone in the explicit bilimit order. -/
theorem ExpandingSequence.bilimitToCoconeSup_monotone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (C : ExpandingSequence.Cocone S E) :
    Monotone (ExpandingSequence.bilimitToCoconeSup S hE C) := by
  intro x y hxy
  exact (ExpandingSequence.bilimitToCoconeSup_isSup S hE C x).2
    (ExpandingSequence.bilimitToCoconeSup S hE C y) (by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      calc
        C.f n (Bilimit.proj S n x)
            ≤ C.f n (Bilimit.proj S n y) := (C.continuous n).1 (hxy n)
        _ ≤ ExpandingSequence.bilimitToCoconeSup S hE C y :=
            ExpandingSequence.bilimitToCocone_le_sup S hE C y n)

/-- For an embedding cocone, the canonical supremum map satisfies the
`e ∘ p ≤ id` half of the e-p-pair laws. -/
theorem ExpandingSequence.bilimitToCoconeSup_below_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (y : E) :
    ExpandingSequence.bilimitToCoconeSup S hE C
        (hC.toBilimitOfAntisymm hantisymm y) ≤ y := by
  have hsup := ExpandingSequence.bilimitToCoconeSup_isSup S hE C
    (hC.toBilimitOfAntisymm hantisymm y)
  exact hsup.2 y (by
    intro z hz
    rcases hz with ⟨n, rfl⟩
    have hbelow : C.f n ((hC.ep n).p y) ≤ y := by
      calc
        C.f n ((hC.ep n).p y)
            = (hC.ep n).e ((hC.ep n).p y) := (hC.ep_e n _).symm
        _ ≤ y := (hC.ep n).below y
    simpa [Bilimit.proj, ExpandingSequence.CoconeEmbeddingData.toBilimitOfAntisymm]
      using hbelow)

/-- One half of the retract equation in Proposition 3.3.9: every bilimit point is
below the projection of its canonical image in the cocone carrier.  The reverse
inequality is the remaining nontrivial part of the retract proof. -/
theorem ExpandingSequence.le_toBilimitOf_bilimitToCoconeSup_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (x : Bilimit S) :
    x ≤ hC.toBilimitOfAntisymm hantisymm
      (ExpandingSequence.bilimitToCoconeSup S hE C x) := by
  intro n
  apply ((hC.ep n).toAdjunction.adj (Bilimit.proj S n x)
    (ExpandingSequence.bilimitToCoconeSup S hE C x)).2
  calc
    (hC.ep n).e (Bilimit.proj S n x)
        = C.f n (Bilimit.proj S n x) := hC.ep_e n _
    _ ≤ ExpandingSequence.bilimitToCoconeSup S hE C x :=
        ExpandingSequence.bilimitToCocone_le_sup S hE C x n

/-- Each stage image `f_m(x_m)` of a bilimit point projects below the `n`-th
coordinate of that point through the e-p-pair projection attached to the
embedding cocone. -/
theorem ExpandingSequence.coconeProjection_stage_le_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E]
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (x : Bilimit S) (n m : Nat) :
    (hC.ep n).p (C.f m (Bilimit.proj S m x)) ≤ Bilimit.proj S n x := by
  rcases Nat.le_total n m with hnm | hmn
  · have hcoord :=
      hC.projection_commute_of_antisymm hantisymm hnm
        (C.f m (Bilimit.proj S m x))
    calc
      (hC.ep n).p (C.f m (Bilimit.proj S m x))
          = S.p hnm ((hC.ep m).p (C.f m (Bilimit.proj S m x))) := hcoord
      _ = S.p hnm ((hC.ep m).p ((hC.ep m).e (Bilimit.proj S m x))) := by
          rw [(hC.ep_e m (Bilimit.proj S m x)).symm]
      _ = S.p hnm (Bilimit.proj S m x) := by
          rw [(hC.ep m).retract]
      _ = Bilimit.proj S n x := by
          simpa [Bilimit.proj] using (x.2 hnm).symm
      _ ≤ Bilimit.proj S n x := le_rfl
  · have hcomm :
        C.f m (Bilimit.proj S m x) =
          C.f n (S.e hmn (Bilimit.proj S m x)) :=
      (C.commute hmn (Bilimit.proj S m x)).symm
    calc
      (hC.ep n).p (C.f m (Bilimit.proj S m x))
          = (hC.ep n).p (C.f n (S.e hmn (Bilimit.proj S m x))) := by
              rw [hcomm]
      _ = (hC.ep n).p ((hC.ep n).e (S.e hmn (Bilimit.proj S m x))) := by
              rw [(hC.ep_e n (S.e hmn (Bilimit.proj S m x))).symm]
      _ = S.e hmn (Bilimit.proj S m x) := by
              rw [(hC.ep n).retract]
      _ = S.e hmn (S.p hmn (Bilimit.proj S n x)) := by
              congr
              simpa [Bilimit.proj] using x.2 hmn
      _ ≤ Bilimit.proj S n x := S.below hmn (Bilimit.proj S n x)

/-- The reverse half of the retract equation for Proposition 3.3.9: projecting
the canonical supremum map back into the bilimit lies below the original
bilimit point. -/
theorem ExpandingSequence.toBilimitOf_bilimitToCoconeSup_le_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (x : Bilimit S) :
    hC.toBilimitOfAntisymm hantisymm
      (ExpandingSequence.bilimitToCoconeSup S hE C x) ≤ x := by
  intro n
  have hprojSup :
      IsSup ((hC.ep n).p '' ExpandingSequence.BilimitToCoconeImage S C x)
        ((hC.ep n).p (ExpandingSequence.bilimitToCoconeSup S hE C x)) :=
    ((hC.ep n).continuous_p).2
      (ExpandingSequence.bilimitToCoconeImage_directed S C x)
      (ExpandingSequence.bilimitToCoconeSup_isSup S hE C x)
  exact hprojSup.2 (Bilimit.proj S n x) (by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy with ⟨m, rfl⟩
    exact ExpandingSequence.coconeProjection_stage_le_of_embeddingData
      S hC hantisymm x n m)

/-- The canonical supremum map in Proposition 3.3.9 is Scott-continuous for an
embedding cocone.  The key upper-bound argument sends an upper bound `b` of the
images of a directed family to the bilimit point `p(b)`, then uses the supremum
property in the bilimit order and the e-p-pair adjunctions stagewise. -/
theorem ExpandingSequence.bilimitToCoconeSup_scottContinuous_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ScottContinuous (ExpandingSequence.bilimitToCoconeSup S hE C) := by
  constructor
  · exact ExpandingSequence.bilimitToCoconeSup_monotone S hE C
  · intro A x hA hx
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact (ExpandingSequence.bilimitToCoconeSup_monotone S hE C) (hx.1 ha)
    · intro b hb
      have hbproj : IsUpperBound A (hC.toBilimitOfAntisymm hantisymm b) := by
        intro a ha n
        apply ((hC.ep n).toAdjunction.adj (Bilimit.proj S n a) b).2
        calc
          (hC.ep n).e (Bilimit.proj S n a)
              = C.f n (Bilimit.proj S n a) := hC.ep_e n _
          _ ≤ ExpandingSequence.bilimitToCoconeSup S hE C a :=
              ExpandingSequence.bilimitToCocone_le_sup S hE C a n
          _ ≤ b := hb ⟨a, ha, rfl⟩
      have hxproj : x ≤ hC.toBilimitOfAntisymm hantisymm b :=
        hx.2 (hC.toBilimitOfAntisymm hantisymm b) hbproj
      exact (ExpandingSequence.bilimitToCoconeSup_isSup S hE C x).2 b (by
        intro z hz
        rcases hz with ⟨n, rfl⟩
        have hnle : Bilimit.proj S n x ≤ (hC.ep n).p b := by
          simpa [Bilimit.proj, ExpandingSequence.CoconeEmbeddingData.toBilimitOfAntisymm]
            using hxproj n
        calc
          C.f n (Bilimit.proj S n x)
              = (hC.ep n).e (Bilimit.proj S n x) := (hC.ep_e n _).symm
          _ ≤ b := ((hC.ep n).toAdjunction.adj (Bilimit.proj S n x) b).1 hnle)

/-- Construction data for the embedding map `Bilimit S -> E` in Proposition
3.3.9.  The field `isSup_image` records the book's formula
`x ↦ ⋁_n f_n(p_n x)`, while the remaining fields are exactly the e-p-pair laws
with the projection map already constructed from the embedding cocone. -/
structure ExpandingSequence.BilimitToCoconeEmbeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E)
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) where
  toFun : Bilimit S → E
  continuous_toFun : ScottContinuous toFun
  isSup_image : (∀ x : Bilimit S,
    IsSup (ExpandingSequence.BilimitToCoconeImage S C x) (toFun x))
  retract_toBilimit : ∀ x : Bilimit S, hC.toBilimitOfAntisymm hantisymm (toFun x) = x
  below_toFun : ∀ y : E, toFun (hC.toBilimitOfAntisymm hantisymm y) ≤ y

/-- Proposition 3.3.9 support: a direct version of the previous packaging lemma
where the only supplied canonical-map obligation is Scott continuity. -/
noncomputable def ExpandingSequence.bilimitToCoconeEmbeddingData_of_continuousSup
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (hcont : ScottContinuous (ExpandingSequence.bilimitToCoconeSup S hE C)) :
    ExpandingSequence.BilimitToCoconeEmbeddingData S C hC hantisymm := by
  refine
    { toFun := ExpandingSequence.bilimitToCoconeSup S hE C
      continuous_toFun := hcont
      isSup_image := ExpandingSequence.bilimitToCoconeSup_isSup S hE C
      retract_toBilimit := ?_
      below_toFun :=
        ExpandingSequence.bilimitToCoconeSup_below_of_embeddingData S hE hC
          hantisymm }
  intro x
  apply Subtype.ext
  funext n
  exact hantisymm n _ _
    ((ExpandingSequence.toBilimitOf_bilimitToCoconeSup_le_of_embeddingData
      S hE hC hantisymm x) n)
    (ExpandingSequence.le_toBilimitOf_bilimitToCoconeSup_of_embeddingData
      S hE hC hantisymm x n)

/-- Proposition 3.3.9 support: the canonical supremum map supplies the full
embedding data for any embedding cocone over a dcpo carrier, under explicit
stage-order antisymmetry. -/
noncomputable def ExpandingSequence.bilimitToCoconeEmbeddingData_canonical
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.BilimitToCoconeEmbeddingData S C hC hantisymm :=
  ExpandingSequence.bilimitToCoconeEmbeddingData_of_continuousSup
    S hE hC hantisymm
    (ExpandingSequence.bilimitToCoconeSup_scottContinuous_of_embeddingData
      S hE hC hantisymm)

/-- The bilimit is a sub-domain of `E`, represented by an embedding-projection
pair from the bilimit into `E`. -/
def ExpandingSequence.BilimitSubdomainOf
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (E : Type u) [Preorder E] : Prop :=
  Nonempty (EPPair (Bilimit S) E)

/-- Proposition 3.3.9 support: once the canonical supremum map from the bilimit
to the cocone carrier is available with the book's two e-p-pair laws, it packages
with `toBilimitOfAntisymm` to make the bilimit a sub-domain of the cocone
carrier. -/
theorem ExpandingSequence.bilimitSubdomainOf_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E)
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (hmap : ExpandingSequence.BilimitToCoconeEmbeddingData S C hC hantisymm) :
    ExpandingSequence.BilimitSubdomainOf S E := by
  exact ⟨{
    e := hmap.toFun
    p := hC.toBilimitOfAntisymm hantisymm
    continuous_e := hmap.continuous_toFun
    continuous_p := hC.toBilimitOfAntisymm_scottContinuous hantisymm
    retract := hmap.retract_toBilimit
    below := hmap.below_toFun
  }⟩

/-- Proposition 3.3.9 support: the canonical supremum construction makes the
bilimit a sub-domain of the cocone carrier whenever the carrier is a dcpo and
the stage preorders are explicitly antisymmetric. -/
theorem ExpandingSequence.bilimitSubdomainOf_of_embeddingData_canonical
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (C : ExpandingSequence.Cocone S E)
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.BilimitSubdomainOf S E := by
  exact ExpandingSequence.bilimitSubdomainOf_of_embeddingData S C hC hantisymm
    (ExpandingSequence.bilimitToCoconeEmbeddingData_canonical S hE hC hantisymm)

/-- The explicit bilimit preorder is antisymmetric whenever all stage preorders
are antisymmetric.  This is the poset component needed by the restricted-DCPO
form of Corollary 3.3.10. -/
theorem ExpandingSequence.bilimit_antisymm_of_stage_antisymm
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ∀ x y : Bilimit S, x ≤ y → y ≤ x → x = y := by
  intro x y hxy hyx
  apply Subtype.ext
  funext n
  exact hantisymm n _ _ (hxy n) (hyx n)

/-- The explicit bilimit carrier is a dcpo whenever all stage carriers are dcpos
and their preorders are antisymmetric.  Directed suprema are computed
coordinatewise, and compatibility follows by applying the continuous projections
`p_{n,m}` to the coordinate suprema. -/
theorem ExpandingSequence.bilimit_dcpo_of_stage_dcpo
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    IsDcpo (Bilimit S) := by
  intro A hA
  let coordSet : ∀ n : Nat, Set (D n) :=
    fun n => (fun x : Bilimit S => Bilimit.proj S n x) '' A
  have hcoordDir : ∀ n : Nat, DirectedSet (coordSet n) := by
    intro n
    exact DirectedSet.image
      (fun (x y : Bilimit S) (hxy : x ≤ y) => by
        change x.1 n ≤ y.1 n
        change (∀ n : Nat, x.1 n ≤ y.1 n) at hxy
        exact hxy n) hA
  let coordSup : ∀ n : Nat, D n :=
    fun n => Classical.choose (hDdcpo n (coordSet n) (hcoordDir n))
  have hcoordSup : ∀ n : Nat, IsSup (coordSet n) (coordSup n) := by
    intro n
    exact Classical.choose_spec (hDdcpo n (coordSet n) (hcoordDir n))
  have hcarrier : BilimitCarrier S coordSup := by
    intro n m hnm
    apply hantisymm n
    · exact (hcoordSup n).2 (S.p hnm (coordSup m)) (by
        intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        calc
          Bilimit.proj S n a = S.p hnm (Bilimit.proj S m a) := by
              simpa [Bilimit.proj] using a.2 hnm
          _ ≤ S.p hnm (coordSup m) :=
              (S.continuous_p hnm).1 ((hcoordSup m).1 ⟨a, ha, rfl⟩))
    · have hprojSup :
          IsSup ((S.p hnm) '' coordSet m) (S.p hnm (coordSup m)) :=
        (S.continuous_p hnm).2 (hcoordDir m) (hcoordSup m)
      exact hprojSup.2 (coordSup n) (by
        intro y hy
        rcases hy with ⟨ym, hym, rfl⟩
        rcases hym with ⟨a, ha, rfl⟩
        calc
          S.p hnm (Bilimit.proj S m a) = Bilimit.proj S n a := by
              simpa [Bilimit.proj] using (a.2 hnm).symm
          _ ≤ coordSup n := (hcoordSup n).1 ⟨a, ha, rfl⟩)
  refine ⟨⟨coordSup, hcarrier⟩, ?_⟩
  constructor
  · intro a ha n
    exact (hcoordSup n).1 ⟨a, ha, rfl⟩
  · intro b hb n
    exact (hcoordSup n).2 (Bilimit.proj S n b) (by
      intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact hb ha n)

/-- Under stage dcpo/poset hypotheses, the canonical projections
`Bilimit S -> D_n` are Scott-continuous.  The proof compares an arbitrary
directed supremum in the bilimit with the coordinatewise supremum used in
`bilimit_dcpo_of_stage_dcpo`. -/
theorem ExpandingSequence.bilimitProj_scottContinuous_of_stage_dcpo
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n : Nat) : ScottContinuous (Bilimit.proj S n) := by
  constructor
  · intro x y hxy
    change x.1 n ≤ y.1 n
    change (∀ n : Nat, x.1 n ≤ y.1 n) at hxy
    exact hxy n
  · intro A x hA hx
    let coordSet : ∀ n : Nat, Set (D n) :=
      fun n => (fun x : Bilimit S => Bilimit.proj S n x) '' A
    have hcoordDir : ∀ n : Nat, DirectedSet (coordSet n) := by
      intro n
      exact DirectedSet.image
        (fun (x y : Bilimit S) (hxy : x ≤ y) => by
          change x.1 n ≤ y.1 n
          change (∀ n : Nat, x.1 n ≤ y.1 n) at hxy
          exact hxy n) hA
    let coordSup : ∀ n : Nat, D n :=
      fun n => Classical.choose (hDdcpo n (coordSet n) (hcoordDir n))
    have hcoordSup : ∀ n : Nat, IsSup (coordSet n) (coordSup n) := by
      intro n
      exact Classical.choose_spec (hDdcpo n (coordSet n) (hcoordDir n))
    have hcarrier : BilimitCarrier S coordSup := by
      intro i j hij
      apply hantisymm i
      · exact (hcoordSup i).2 (S.p hij (coordSup j)) (by
          intro y hy
          rcases hy with ⟨a, ha, rfl⟩
          calc
            Bilimit.proj S i a = S.p hij (Bilimit.proj S j a) := by
                simpa [Bilimit.proj] using a.2 hij
            _ ≤ S.p hij (coordSup j) :=
                (S.continuous_p hij).1 ((hcoordSup j).1 ⟨a, ha, rfl⟩))
      · have hprojSup :
            IsSup ((S.p hij) '' coordSet j) (S.p hij (coordSup j)) :=
          (S.continuous_p hij).2 (hcoordDir j) (hcoordSup j)
        exact hprojSup.2 (coordSup i) (by
          intro y hy
          rcases hy with ⟨yj, hyj, rfl⟩
          rcases hyj with ⟨a, ha, rfl⟩
          calc
            S.p hij (Bilimit.proj S j a) = Bilimit.proj S i a := by
                simpa [Bilimit.proj] using (a.2 hij).symm
            _ ≤ coordSup i := (hcoordSup i).1 ⟨a, ha, rfl⟩)
    let y : Bilimit S := ⟨coordSup, hcarrier⟩
    have hy : IsSup A y := by
      constructor
      · intro a ha i
        exact (hcoordSup i).1 ⟨a, ha, rfl⟩
      · intro b hb i
        exact (hcoordSup i).2 (Bilimit.proj S i b) (by
          intro z hz
          rcases hz with ⟨a, ha, rfl⟩
          exact hb ha i)
    have hxy : x = y := by
      exact ExpandingSequence.bilimit_antisymm_of_stage_antisymm S hantisymm
        x y (hx.2 y hy.1) (hy.2 x hx.1)
    have hn : Bilimit.proj S n x = coordSup n := by
      rw [hxy]
      rfl
    rw [hn]
    simpa [coordSet, Bilimit.proj] using hcoordSup n

/-- The canonical projection cone of the explicit bilimit, available once the
stage dcpo/poset hypotheses make the coordinate projections Scott-continuous. -/
noncomputable def ExpandingSequence.bilimitProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.ProjectionCone S (Bilimit S) where
  p := Bilimit.proj S
  continuous := ExpandingSequence.bilimitProj_scottContinuous_of_stage_dcpo S hDdcpo hantisymm
  commute := by
    intro n m h x
    simpa [Bilimit.proj] using (x.2 h).symm

/-- The mediating map from a projection cone to the explicit bilimit is the
tuple of its projection components, as stated in Theorem 3.3.7. -/
def ExpandingSequence.projectionConeToBilimit
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.ProjectionCone S E) :
    E → Bilimit S :=
  fun x => ⟨fun n => C.p n x, by
    intro n m h
    exact (C.commute h x).symm⟩

/-- The projection-cone mediating map into the explicit bilimit is
Scott-continuous because each coordinate projection is Scott-continuous and the
bilimit order is coordinatewise. -/
theorem ExpandingSequence.projectionConeToBilimit_scottContinuous
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.ProjectionCone S E) :
    ScottContinuous (ExpandingSequence.projectionConeToBilimit S C) := by
  constructor
  · intro x y hxy n
    exact (C.continuous n).1 hxy
  · intro A x hA hx
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      intro n
      exact ((C.continuous n).2 hA hx).1 ⟨a, ha, rfl⟩
    · intro b hb n
      exact ((C.continuous n).2 hA hx).2 (Bilimit.proj S n b) (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hb ⟨a, ha, rfl⟩ n)

/-- The canonical projection cone satisfies the ordinary DCPO limiting universal
property from Theorem 3.3.7.  This is the projection-side component needed before
the stronger restricted projection-category statement of Corollary 3.3.10 can be
closed. -/
theorem ExpandingSequence.isLimitingProjectionCone_bilimitProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.IsLimitingProjectionCone S
      (ExpandingSequence.bilimit_dcpo_of_stage_dcpo S hDdcpo hantisymm)
      (ExpandingSequence.bilimit_antisymm_of_stage_antisymm S hantisymm)
      (ExpandingSequence.bilimitProjectionCone S hDdcpo hantisymm) := by
  intro F _ _hF _hFanti C'
  refine ⟨ExpandingSequence.projectionConeToBilimit S C', ?_, ?_⟩
  · constructor
    · exact ExpandingSequence.projectionConeToBilimit_scottContinuous S C'
    · intro n x
      rfl
  · intro v hv x
    apply Subtype.ext
    funext n
    exact hv.2 n x

/-- Projection maps in an expanding sequence compose as `p_nm ∘ p_mk = p_nk`.
The definition records only the corresponding embedding composition; this lemma
derives the projection law from the e-p-pair adjunctions and explicit
antisymmetry of the stage orders, matching the note after Definition 3.3.6. -/
theorem ExpandingSequence.projection_comp_of_antisymm
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {n m k : Nat} (hnm : n ≤ m) (hmk : m ≤ k) (hnk : n ≤ k) (z : D k) :
    S.p hnm (S.p hmk z) = S.p hnk z := by
  apply hantisymm n
  · apply ((S.epPair hnk).toAdjunction.adj (S.p hnm (S.p hmk z)) z).2
    calc
      S.e hnk (S.p hnm (S.p hmk z))
          = S.e hmk (S.e hnm (S.p hnm (S.p hmk z))) :=
              S.comp_e hnm hmk hnk _
      _ ≤ S.e hmk (S.p hmk z) :=
          (S.continuous_e hmk).1 (S.below hnm (S.p hmk z))
      _ ≤ z := S.below hmk z
  · apply ((S.epPair hnm).toAdjunction.adj (S.p hnk z) (S.p hmk z)).2
    apply ((S.epPair hmk).toAdjunction.adj (S.e hnm (S.p hnk z)) z).2
    calc
      S.e hmk (S.e hnm (S.p hnk z))
          = S.e hnk (S.p hnk z) := (S.comp_e hnm hmk hnk _).symm
      _ ≤ z := S.below hnk z

/-- Coordinate formula for the stage embedding `D_n -> Bilimit S`.  At
coordinate `i`, the PDF allows any common upper bound of `{i,n}`; here we use
`max i n` and take `p_{i,max i n} (e_{n,max i n} x)`. -/
def ExpandingSequence.stageProjectionMap
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (n i : Nat) : D n → D i :=
  fun x => S.p (Nat.le_max_left i n) (S.e (Nat.le_max_right i n) x)

/-- The coordinate maps used for a fixed stage form a projection cone over the
dual projection diagram. -/
theorem ExpandingSequence.stageProjectionMap_commute
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {i j : Nat} (hij : i ≤ j) (n : Nat) (x : D n) :
    S.p hij (S.stageProjectionMap n j x) = S.stageProjectionMap n i x := by
  let k₁ : Nat := max i n
  let k₂ : Nat := max j n
  have hik₁ : i ≤ k₁ := Nat.le_max_left i n
  have hnk₁ : n ≤ k₁ := Nat.le_max_right i n
  have hjk₂ : j ≤ k₂ := Nat.le_max_left j n
  have hnk₂ : n ≤ k₂ := Nat.le_max_right j n
  have hik₂ : i ≤ k₂ := le_trans hij hjk₂
  have hk₁k₂ : k₁ ≤ k₂ := (Nat.max_le).2 ⟨hik₂, hnk₂⟩
  have hpk :
      S.p hk₁k₂ (S.e hnk₂ x) = S.e hnk₁ x := by
    calc
      S.p hk₁k₂ (S.e hnk₂ x)
          = S.p hk₁k₂ (S.e hk₁k₂ (S.e hnk₁ x)) := by
              rw [(S.comp_e hnk₁ hk₁k₂ hnk₂ x)]
      _ = S.e hnk₁ x := S.retract hk₁k₂ (S.e hnk₁ x)
  calc
    S.p hij (S.stageProjectionMap n j x)
        = S.p hij (S.p hjk₂ (S.e hnk₂ x)) := rfl
    _ = S.p hik₂ (S.e hnk₂ x) :=
        S.projection_comp_of_antisymm hantisymm hij hjk₂ hik₂ (S.e hnk₂ x)
    _ = S.p hik₁ (S.p hk₁k₂ (S.e hnk₂ x)) :=
        (S.projection_comp_of_antisymm hantisymm hik₁ hk₁k₂ hik₂
          (S.e hnk₂ x)).symm
    _ = S.stageProjectionMap n i x := by
        rw [hpk]
        rfl

/-- The projection cone with carrier `D_n` whose components are the coordinate
maps of the stage embedding into the bilimit. -/
noncomputable def ExpandingSequence.stageProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n : Nat) : ExpandingSequence.ProjectionCone S (D n) where
  p := S.stageProjectionMap n
  continuous := fun i => by
    unfold ExpandingSequence.stageProjectionMap
    exact ScottContinuous.comp (S.continuous_p (Nat.le_max_left i n))
      (S.continuous_e (Nat.le_max_right i n))
  commute := by
    intro i j hij x
    exact S.stageProjectionMap_commute hantisymm hij n x

/-- The stage embedding `D_n -> Bilimit S`, implemented as the mediating map
from the stage projection cone. -/
noncomputable def ExpandingSequence.stageEmbedding
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n : Nat) : D n → Bilimit S :=
  ExpandingSequence.projectionConeToBilimit S (S.stageProjectionCone hantisymm n)

/-- Coordinate equation for the stage embedding, using the `max` common upper
bound formula from `stageProjectionMap`. -/
theorem ExpandingSequence.stageEmbedding_proj
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n i : Nat) (x : D n) :
    Bilimit.proj S i (S.stageEmbedding hantisymm n x) = S.stageProjectionMap n i x := by
  rfl

/-- The stage embedding is Scott-continuous because it is the mediating map from
a projection cone whose coordinate maps are Scott-continuous. -/
theorem ExpandingSequence.stageEmbedding_scottContinuous
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n : Nat) : ScottContinuous (S.stageEmbedding hantisymm n) := by
  exact ExpandingSequence.projectionConeToBilimit_scottContinuous S
    (S.stageProjectionCone hantisymm n)

/-- The stage embedding and the canonical projection form the e-p-pair
`(e_n,p_n)` from Theorem 3.3.7. -/
noncomputable def ExpandingSequence.stageEPPair
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n : Nat) : EPPair (D n) (Bilimit S) where
  e := S.stageEmbedding hantisymm n
  p := Bilimit.proj S n
  continuous_e := S.stageEmbedding_scottContinuous hantisymm n
  continuous_p := S.bilimitProj_scottContinuous_of_stage_dcpo hDdcpo hantisymm n
  retract := by
    intro x
    have hproof :
        Nat.le_max_right n n = Nat.le_max_left n n := Subsingleton.elim _ _
    change S.stageProjectionMap n n x = x
    unfold ExpandingSequence.stageProjectionMap
    rw [hproof]
    exact S.retract (Nat.le_max_left n n) x
  below := by
    intro y i
    let k : Nat := max i n
    have hik : i ≤ k := Nat.le_max_left i n
    have hnk : n ≤ k := Nat.le_max_right i n
    calc
      Bilimit.proj S i (S.stageEmbedding hantisymm n (Bilimit.proj S n y))
          = S.stageProjectionMap n i (Bilimit.proj S n y) := rfl
      _ = S.p hik (S.e hnk (S.p hnk (Bilimit.proj S k y))) := by
          unfold ExpandingSequence.stageProjectionMap
          rw [show Bilimit.proj S n y = S.p hnk (Bilimit.proj S k y) by
            simpa [Bilimit.proj] using y.2 hnk]
      _ ≤ S.p hik (Bilimit.proj S k y) :=
          (S.continuous_p hik).1 (S.below hnk (Bilimit.proj S k y))
      _ = Bilimit.proj S i y := by
          simpa [Bilimit.proj] using (y.2 hik).symm

/-- The stage-embedding coordinate formula is compatible with the connecting
embeddings: the `m`-stage embedding after `e_{n,m}` has the same coordinates as
the `n`-stage embedding. -/
theorem ExpandingSequence.stageProjectionMap_of_embedding
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {n m : Nat} (hnm : n ≤ m) (i : Nat) (x : D n) :
    S.stageProjectionMap m i (S.e hnm x) = S.stageProjectionMap n i x := by
  let k₁ : Nat := max i n
  let k₂ : Nat := max i m
  have hik₁ : i ≤ k₁ := Nat.le_max_left i n
  have hnk₁ : n ≤ k₁ := Nat.le_max_right i n
  have hik₂ : i ≤ k₂ := Nat.le_max_left i m
  have hmk₂ : m ≤ k₂ := Nat.le_max_right i m
  have hnk₂ : n ≤ k₂ := le_trans hnm hmk₂
  have hk₁k₂ : k₁ ≤ k₂ := (Nat.max_le).2 ⟨hik₂, hnk₂⟩
  have hpk : S.p hk₁k₂ (S.e hnk₂ x) = S.e hnk₁ x := by
    calc
      S.p hk₁k₂ (S.e hnk₂ x)
          = S.p hk₁k₂ (S.e hk₁k₂ (S.e hnk₁ x)) := by
              rw [S.comp_e hnk₁ hk₁k₂ hnk₂ x]
      _ = S.e hnk₁ x := S.retract hk₁k₂ (S.e hnk₁ x)
  calc
    S.stageProjectionMap m i (S.e hnm x)
        = S.p hik₂ (S.e hmk₂ (S.e hnm x)) := rfl
    _ = S.p hik₂ (S.e hnk₂ x) := by
        rw [(S.comp_e hnm hmk₂ hnk₂ x).symm]
    _ = S.p hik₁ (S.p hk₁k₂ (S.e hnk₂ x)) :=
        (S.projection_comp_of_antisymm hantisymm hik₁ hk₁k₂ hik₂
          (S.e hnk₂ x)).symm
    _ = S.stageProjectionMap n i x := by
        rw [hpk]
        rfl

/-- The stage embeddings commute with the expanding-sequence embeddings, giving
the canonical embedding cocone over the explicit bilimit. -/
theorem ExpandingSequence.stageEmbedding_commute
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {n m : Nat} (hnm : n ≤ m) (x : D n) :
    S.stageEmbedding hantisymm m (S.e hnm x) = S.stageEmbedding hantisymm n x := by
  apply Subtype.ext
  funext i
  exact S.stageProjectionMap_of_embedding hantisymm hnm i x

/-- The canonical embedding cocone of the explicit bilimit, with legs the stage
embeddings from Theorem 3.3.7. -/
noncomputable def ExpandingSequence.bilimitEmbeddingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.Cocone S (Bilimit S) where
  f := S.stageEmbedding hantisymm
  continuous := S.stageEmbedding_scottContinuous hantisymm
  commute := by
    intro n m h x
    exact S.stageEmbedding_commute hantisymm h x

/-- The canonical embedding cocone has embedding data: its legs are the
embedding halves of the e-p-pairs `(e_n,p_n)` from Theorem 3.3.7. -/
noncomputable def ExpandingSequence.bilimitEmbeddingCoconeEmbeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.CoconeEmbeddingData S (S.bilimitEmbeddingCocone hantisymm) where
  ep := S.stageEPPair hDdcpo hantisymm
  ep_e := by
    intro n x
    rfl

/-- The canonical embedding cocone satisfies the e-p-pair decomposition
criterion from Lemma 3.3.8.  The supremum identity is the coordinatewise form of
`⋁_n e_n ∘ p_n = id_D` from Theorem 3.3.7. -/
noncomputable def ExpandingSequence.bilimitEmbeddingCoconeEPDecomposition
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.CoconeEPDecomposition S (S.bilimitEmbeddingCocone hantisymm) where
  ep := S.stageEPPair hDdcpo hantisymm
  ep_e := by
    intro n x
    rfl
  sup_identity := by
    intro y
    constructor
    · intro z hz
      rcases hz with ⟨n, rfl⟩
      exact (S.stageEPPair hDdcpo hantisymm n).below y
    · intro b hb i
      have hUpper :
          S.stageEmbedding hantisymm i (Bilimit.proj S i y) ≤ b := by
        exact hb ⟨i, rfl⟩
      calc
        Bilimit.proj S i y
            = Bilimit.proj S i (S.stageEmbedding hantisymm i (Bilimit.proj S i y)) :=
                ((S.stageEPPair hDdcpo hantisymm i).retract
                  (Bilimit.proj S i y)).symm
        _ ≤ Bilimit.proj S i b := hUpper i

/-- The canonical supremum map from the bilimit to an embedding cocone agrees
with the cocone leg on each stage embedding. -/
theorem ExpandingSequence.bilimitToCoconeSup_stageEmbedding
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    (C : ExpandingSequence.Cocone S E) (n : Nat) (x : D n) :
    ExpandingSequence.bilimitToCoconeSup S hE C (S.stageEmbedding hantisymm n x) =
      C.f n x := by
  let hB := S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm
  have hchosen :=
    ExpandingSequence.bilimitToCoconeSup_isSup S hE C (S.stageEmbedding hantisymm n x)
  have hstage :
      IsSup (ExpandingSequence.BilimitToCoconeImage S C
        (S.stageEmbedding hantisymm n x)) (C.f n x) := by
    simpa [ExpandingSequence.BilimitToCoconeImage,
      ExpandingSequence.CoconeEPDecomposition.TargetImage,
      ExpandingSequence.bilimitEmbeddingCocone,
      ExpandingSequence.bilimitEmbeddingCoconeEPDecomposition,
      ExpandingSequence.stageEPPair] using
      (hB.targetImage_stage_isSup hantisymm C n x)
  exact hEanti _ _
    (hchosen.2 (C.f n x) hstage.1)
    (hstage.2 (ExpandingSequence.bilimitToCoconeSup S hE C
      (S.stageEmbedding hantisymm n x)) hchosen.1)

/-- The canonical supremum map from the bilimit to an embedding cocone is a
cocone-mediating map. -/
theorem ExpandingSequence.bilimitToCoconeSup_mediates_bilimitEmbeddingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C) :
    ExpandingSequence.CoconeMediates S (S.bilimitEmbeddingCocone hantisymm) C
      (ExpandingSequence.bilimitToCoconeSup S hE C) := by
  constructor
  · exact ExpandingSequence.bilimitToCoconeSup_scottContinuous_of_embeddingData
      S hE hC hantisymm
  · intro n x
    exact S.bilimitToCoconeSup_stageEmbedding hDdcpo hantisymm hE hEanti C n x

/-- Theorem 3.3.7 full data package.

PDF text excerpt: "Let `⟨(D_n)_{n∈N}, (e_mn : D_n → D_m)_{n≤m∈N}⟩` be an
expanding sequence in `DCPO`. Define an object `D` by compatible tuples
`x_n = p_nm(x_m)`, projections `p_m : D → D_m`, and embeddings
`e_m : D_m → D` by the coordinate formula using a common upper bound. Then:
(1) the maps `(e_m,p_m)` form embedding projection pairs and
`⋁_m e_m ∘ p_m = id_D`; (2) `⟨D,(p_n)⟩` is a limit of the projection diagram;
(3) `⟨D,(e_n)⟩` is a colimit of the embedding diagram."

Current Lean spelling: the theorem is packaged in the preorder interface under
explicit stage `IsDcpo` and antisymmetry hypotheses.  The fields below record
the dcpo/poset structure of the bilimit carrier, the projection-limit universal
property, the canonical e-p-pair decomposition, and the embedding-colimit
universal property. -/
structure ExpandingSequence.BilimitTheoremFullData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (_hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) where
  bilimit_dcpo : IsDcpo (Bilimit S)
  bilimit_antisymm : ∀ x y : Bilimit S, x ≤ y → y ≤ x → x = y
  projectionCone : ExpandingSequence.ProjectionCone S (Bilimit S)
  projectionCone_proj : ∀ n : Nat, ∀ x : Bilimit S, projectionCone.p n x = Bilimit.proj S n x
  limiting_projection :
    ExpandingSequence.IsLimitingProjectionCone S bilimit_dcpo bilimit_antisymm projectionCone
  embeddingCocone : ExpandingSequence.Cocone S (Bilimit S)
  embeddingCocone_f :
    ∀ n : Nat, ∀ x : D n, embeddingCocone.f n x = S.stageEmbedding hantisymm n x
  ep_decomposition : ExpandingSequence.CoconeEPDecomposition S embeddingCocone
  colimiting_embedding :
    ExpandingSequence.IsColimitingCocone S bilimit_dcpo bilimit_antisymm embeddingCocone

/-- Theorem 3.3.7, full preorder-interface form.

Current Lean spelling: construct the full package described above for an
expanding sequence once each stage is a dcpo and its preorder is explicitly
antisymmetric. -/
noncomputable def theorem_3_3_7_expanding_sequence_bilimit
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.BilimitTheoremFullData S hDdcpo hantisymm where
  bilimit_dcpo := S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm
  bilimit_antisymm := S.bilimit_antisymm_of_stage_antisymm hantisymm
  projectionCone := S.bilimitProjectionCone hDdcpo hantisymm
  projectionCone_proj := by
    intro n x
    rfl
  limiting_projection :=
    S.isLimitingProjectionCone_bilimitProjectionCone hDdcpo hantisymm
  embeddingCocone := S.bilimitEmbeddingCocone hantisymm
  embeddingCocone_f := by
    intro n x
    rfl
  ep_decomposition :=
    S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm
  colimiting_embedding :=
    S.isColimitingCocone_of_epDecomposition hantisymm
      (S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm)
      (S.bilimit_antisymm_of_stage_antisymm hantisymm)
      (S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm)

/-- Theorem 3.3.7, theorem-facing existence wrapper for the full bilimit
limit-colimit package. -/
theorem theorem_3_3_7_expanding_sequence_bilimit_exists
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    Nonempty (ExpandingSequence.BilimitTheoremFullData S hDdcpo hantisymm) :=
  ⟨theorem_3_3_7_expanding_sequence_bilimit S hDdcpo hantisymm⟩

/-- The statement form of Proposition 3.3.9.

PDF text: "Let `⟨E,(f_n)_{n∈N}⟩` be a cocone over the expanding sequence
`⟨(D_n)_{n∈N}, (e_mn : D_n → D_m)_{n≤m∈N}⟩` where the `f_n` are embeddings.
Then the bilimit of the sequence is a sub-domain of `E`."

Current Lean spelling: in the preorder interface, stage dcpo and stage
antisymmetry hypotheses are explicit, the target cocone carrier is required to
be a dcpo, and the embedding assumption on the cocone legs is supplied as
`CoconeEmbeddingData`.  The conclusion is an actual e-p-pair
`EPPair (Bilimit S) E`. -/
def ExpandingSequence.BilimitSubdomainOfCoconeFull
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) :
    Prop :=
  (∀ n : Nat, IsDcpo (D n)) →
  (∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) →
  ∀ E : Type u, ∀ [Preorder E], IsDcpo E → ∀ C : ExpandingSequence.Cocone S E,
    Nonempty (ExpandingSequence.CoconeEmbeddingData S C) →
      ExpandingSequence.BilimitSubdomainOf S E

/-- A projection cone whose legs are projections in e-p-pairs. -/
structure ExpandingSequence.ProjectionConeProjectionData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.ProjectionCone S E) where
  ep : ∀ n : Nat, EPPair (D n) E
  ep_p : ∀ n : Nat, ∀ x : E, (ep n).p x = C.p n x

namespace ExpandingSequence.ProjectionConeProjectionData

variable {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
variable {S : ExpandingSequence D}
variable {E : Type u} [Preorder E]
variable {C : ExpandingSequence.ProjectionCone S E}
variable (hC : ExpandingSequence.ProjectionConeProjectionData S C)

/-- A projection cone whose legs are projection halves determines an embedding
cocone by taking the corresponding embedding halves. -/
def toCocone
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.Cocone S E where
  f := fun n => (hC.ep n).e
  continuous := fun n => (hC.ep n).continuous_e
  commute := by
    intro n m h x
    apply hEanti
    · apply ((hC.ep m).toAdjunction.adj (S.e h x) ((hC.ep n).e x)).1
      have hproj :
          S.p h ((hC.ep m).p ((hC.ep n).e x)) = x := by
        calc
          S.p h ((hC.ep m).p ((hC.ep n).e x))
              = S.p h (C.p m ((hC.ep n).e x)) := by rw [hC.ep_p m]
          _ = C.p n ((hC.ep n).e x) := C.commute h _
          _ = (hC.ep n).p ((hC.ep n).e x) := by rw [hC.ep_p n]
          _ = x := (hC.ep n).retract x
      calc
        S.e h x = S.e h (S.p h ((hC.ep m).p ((hC.ep n).e x))) := by rw [hproj]
        _ ≤ (hC.ep m).p ((hC.ep n).e x) :=
          S.below h ((hC.ep m).p ((hC.ep n).e x))
    · apply ((hC.ep n).toAdjunction.adj x ((hC.ep m).e (S.e h x))).1
      have hproj :
          (hC.ep n).p ((hC.ep m).e (S.e h x)) = x := by
        calc
          (hC.ep n).p ((hC.ep m).e (S.e h x))
              = C.p n ((hC.ep m).e (S.e h x)) := hC.ep_p n _
          _ = S.p h (C.p m ((hC.ep m).e (S.e h x))) := (C.commute h _).symm
          _ = S.p h ((hC.ep m).p ((hC.ep m).e (S.e h x))) := by
              rw [hC.ep_p m]
          _ = S.p h (S.e h x) := by rw [(hC.ep m).retract]
          _ = x := S.retract h x
      rw [hproj]

/-- The embedding cocone induced by projection legs carries the same e-p-pairs. -/
def toCoconeEmbeddingData
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.CoconeEmbeddingData S (hC.toCocone hEanti) where
  ep := hC.ep
  ep_e := by
    intro n x
    rfl

end ExpandingSequence.ProjectionConeProjectionData

/-- A projection cone whose legs are projection halves has the canonical
mediating map into the bilimit as a projection morphism. -/
theorem ExpandingSequence.projectionConeToBilimit_projectionMorphism
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    {C : ExpandingSequence.ProjectionCone S E}
    (hC : ExpandingSequence.ProjectionConeProjectionData S C) :
    ProjectionMorphism (ExpandingSequence.projectionConeToBilimit S C) := by
  let Cemb : ExpandingSequence.Cocone S E := hC.toCocone hEanti
  let hCemb : ExpandingSequence.CoconeEmbeddingData S Cemb :=
    hC.toCoconeEmbeddingData hEanti
  let hmap := ExpandingSequence.bilimitToCoconeEmbeddingData_canonical
    S hE hCemb hantisymm
  let ep : EPPair (Bilimit S) E :=
    { e := hmap.toFun
      p := hCemb.toBilimitOfAntisymm hantisymm
      continuous_e := hmap.continuous_toFun
      continuous_p := hCemb.toBilimitOfAntisymm_scottContinuous hantisymm
      retract := hmap.retract_toBilimit
      below := hmap.below_toFun }
  refine ⟨⟨ep, ?_⟩⟩
  intro y
  apply Subtype.ext
  funext n
  exact hC.ep_p n y

/-- Projection-leg restricted version of the limiting-cone interface used for
Corollary 3.3.10.

PDF text: "The bilimit of an expanding sequence is also the colimit (limit) in
the restricted category of dcpo's with embeddings (projections) as morphisms."
This interface records the parenthesized limit/projection half.

Current Lean spelling: the cone legs are required to be projection halves of
e-p-pairs, and the universal property is quantified only over cones with the
same projection-leg data.  The mediating map is returned both as an ordinary
continuous cone morphism and as the projection half of an e-p-pair. -/
def ExpandingSequence.IsRestrictedLimitingProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (_hE : IsDcpo E)
    (_hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    (C : ExpandingSequence.ProjectionCone S E) : Prop :=
  Nonempty (ExpandingSequence.ProjectionConeProjectionData S C) ∧
    ∀ F : Type u, ∀ [Preorder F], IsDcpo F →
      (∀ x y : F, x ≤ y → y ≤ x → x = y) → ∀ C' : ExpandingSequence.ProjectionCone S F,
      Nonempty (ExpandingSequence.ProjectionConeProjectionData S C') →
        ∃ u : F → E, ExpandingSequence.ProjectionConeMediates S C' C u ∧
          ProjectionMorphism u ∧
          ∀ v : F → E, ExpandingSequence.ProjectionConeMediates S C' C v →
            ∀ y : F, v y = u y

/-- The canonical projection cone has projection morphisms in the restricted
projection category: each leg is the projection half of the e-p-pair
`(e_n,p_n)`. -/
noncomputable def ExpandingSequence.bilimitProjectionConeProjectionData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.ProjectionConeProjectionData S
      (S.bilimitProjectionCone hDdcpo hantisymm) where
  ep := S.stageEPPair hDdcpo hantisymm
  ep_p := by
    intro n x
    rfl

/-- The canonical projection cone satisfies the current projection-leg
restricted interface.  This upgrades the ordinary projection-limit result by
adding e-p-pair data for the canonical projections and packaging the mediating
map from any projection-leg cone as a projection morphism. -/
theorem ExpandingSequence.isRestrictedLimitingProjectionCone_bilimitProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.IsRestrictedLimitingProjectionCone S
      (S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm)
      (S.bilimit_antisymm_of_stage_antisymm hantisymm)
      (S.bilimitProjectionCone hDdcpo hantisymm) := by
  constructor
  · exact ⟨S.bilimitProjectionConeProjectionData hDdcpo hantisymm⟩
  · intro F _ hF hFanti C' hC'
    rcases hC' with ⟨hC'⟩
    refine ⟨ExpandingSequence.projectionConeToBilimit S C', ?_, ?_, ?_⟩
    · constructor
      · exact ExpandingSequence.projectionConeToBilimit_scottContinuous S C'
      · intro n x
        rfl
    · exact S.projectionConeToBilimit_projectionMorphism hantisymm hF hFanti hC'
    · intro v hv x
      apply Subtype.ext
      funext n
      exact hv.2 n x

/-- Embedding-leg restricted version of the colimiting-cocone interface used for
Corollary 3.3.10.

PDF text: "The bilimit of an expanding sequence is also the colimit (limit) in
the restricted category of dcpo's with embeddings (projections) as morphisms."
This interface records the colimit/embedding half.

Current Lean spelling: the cocone legs are required to be embedding halves of
e-p-pairs, and the universal property is quantified only over cocones with the
same embedding-leg data.  The mediating map is returned both as an ordinary
continuous cocone morphism and as the embedding half of an e-p-pair. -/
def ExpandingSequence.IsRestrictedColimitingEmbeddingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (_hE : IsDcpo E)
    (_hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    (C : ExpandingSequence.Cocone S E) : Prop :=
  Nonempty (ExpandingSequence.CoconeEmbeddingData S C) ∧
    ∀ F : Type u, ∀ [Preorder F], IsDcpo F →
      (∀ x y : F, x ≤ y → y ≤ x → x = y) → ∀ C' : ExpandingSequence.Cocone S F,
      Nonempty (ExpandingSequence.CoconeEmbeddingData S C') →
        ∃ u : E → F, ExpandingSequence.CoconeMediates S C C' u ∧
          EmbeddingMorphism u ∧
          ∀ v : E → F, ExpandingSequence.CoconeMediates S C C' v →
            ∀ y : E, v y = u y

/-- The canonical embedding cocone satisfies the current embedding-leg
restricted interface.  The proof uses the full Lemma 3.3.8 sufficiency
direction, because the canonical cocone has the e-p-pair decomposition
`⋁_n e_n ∘ p_n = id`; the mediating map is packaged as the canonical
bilimit-to-cocone embedding from Proposition 3.3.9. -/
theorem ExpandingSequence.isRestrictedColimitingEmbeddingCocone_bilimitEmbeddingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.IsRestrictedColimitingEmbeddingCocone S
      (S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm)
      (S.bilimit_antisymm_of_stage_antisymm hantisymm)
      (S.bilimitEmbeddingCocone hantisymm) := by
  constructor
  · exact ⟨S.bilimitEmbeddingCoconeEmbeddingData hDdcpo hantisymm⟩
  · intro F _ hF hFanti C' hC'
    rcases hC' with ⟨hC'⟩
    let hmap := ExpandingSequence.bilimitToCoconeEmbeddingData_canonical
      S hF hC' hantisymm
    refine ⟨hmap.toFun, ?_, ?_, ?_⟩
    · change ExpandingSequence.CoconeMediates S (S.bilimitEmbeddingCocone hantisymm) C'
        (ExpandingSequence.bilimitToCoconeSup S hF C')
      exact S.bilimitToCoconeSup_mediates_bilimitEmbeddingCocone
        hDdcpo hantisymm hF hFanti hC'
    · let ep : EPPair (Bilimit S) F :=
        { e := hmap.toFun
          p := hC'.toBilimitOfAntisymm hantisymm
          continuous_e := hmap.continuous_toFun
          continuous_p := hC'.toBilimitOfAntisymm_scottContinuous hantisymm
          retract := hmap.retract_toBilimit
          below := hmap.below_toFun }
      refine ⟨⟨ep, ?_⟩⟩
      intro x
      rfl
    · have hcolim :
        ExpandingSequence.IsColimitingCocone S
          (S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm)
          (S.bilimit_antisymm_of_stage_antisymm hantisymm)
          (S.bilimitEmbeddingCocone hantisymm) :=
        S.isColimitingCocone_of_epDecomposition hantisymm
          (S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm)
          (S.bilimit_antisymm_of_stage_antisymm hantisymm)
          (S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm)
      rcases hcolim F hF hFanti C' with ⟨u₀, hu₀, huniq⟩
      intro v hv y
      have hvu₀ := huniq v hv y
      have hmapu₀ : hmap.toFun y = u₀ y := by
        apply huniq hmap.toFun
        change ExpandingSequence.CoconeMediates S (S.bilimitEmbeddingCocone hantisymm) C'
          (ExpandingSequence.bilimitToCoconeSup S hF C')
        exact S.bilimitToCoconeSup_mediates_bilimitEmbeddingCocone
          hDdcpo hantisymm hF hFanti hC'
      exact hvu₀.trans hmapu₀.symm

/-- Current statement package for Corollary 3.3.10.

The package proves that the bilimit carrier has projection/embedding cone legs
of the restricted form and satisfies the corresponding universal properties
over cones/cocones whose legs are also restricted, with mediating maps packaged
as projection/embedding morphisms.  The uniqueness clause is stated for all
ordinary continuous cone/cocone mediating maps, hence is stronger than uniqueness
only among restricted morphisms. -/
structure ExpandingSequence.RestrictedBilimitColimitData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) where
  bilimit_dcpo : IsDcpo (Bilimit S)
  bilimit_antisymm : ∀ x y : Bilimit S, x ≤ y → y ≤ x → x = y
  projectionCone : ExpandingSequence.ProjectionCone S (Bilimit S)
  projectionCone_proj : ∀ n : Nat, ∀ x : Bilimit S, projectionCone.p n x = Bilimit.proj S n x
  limiting_projection :
    ExpandingSequence.IsRestrictedLimitingProjectionCone S bilimit_dcpo bilimit_antisymm projectionCone
  embeddingCocone : ExpandingSequence.Cocone S (Bilimit S)
  colimiting_embedding :
    ExpandingSequence.IsRestrictedColimitingEmbeddingCocone S bilimit_dcpo bilimit_antisymm embeddingCocone

/-- Corollary 3.3.10 current statement predicate: projection and embedding
legs are restricted, and the mediating morphisms are packaged as the matching
projection/embedding halves of e-p-pairs. -/
def ExpandingSequence.RestrictedBilimitColimitCoincidence
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) :
    Prop :=
  (∀ n : Nat, IsDcpo (D n)) →
    (∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) →
      Nonempty (ExpandingSequence.RestrictedBilimitColimitData S)

/-- Lemma 3.3.8 necessity direction: a colimiting cocone is isomorphic to the
explicit bilimit cocone, so the projections are obtained as `g_n = p_n ∘ u`,
where `u : E -> Bilimit S` is the unique mediating map into the canonical
embedding cocone. -/
theorem ExpandingSequence.coconeEPDecomposition_of_isColimitingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    {C : ExpandingSequence.Cocone S E}
    (hcolimiting : ExpandingSequence.IsColimitingCocone S hE hEanti C) :
    Nonempty (ExpandingSequence.CoconeEPDecomposition S C) := by
  let hBdcpo : IsDcpo (Bilimit S) := S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm
  let hBanti : ∀ x y : Bilimit S, x ≤ y → y ≤ x → x = y :=
    S.bilimit_antisymm_of_stage_antisymm hantisymm
  let CB : ExpandingSequence.Cocone S (Bilimit S) := S.bilimitEmbeddingCocone hantisymm
  have hBcolimiting : ExpandingSequence.IsColimitingCocone S hBdcpo hBanti CB :=
    S.isColimitingCocone_of_epDecomposition hantisymm hBdcpo hBanti
      (S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm)
  rcases hcolimiting (Bilimit S) hBdcpo hBanti CB with ⟨u, hu, _huuniq⟩
  rcases hBcolimiting E hE hEanti C with ⟨v, hv, _hvuniq⟩
  rcases hcolimiting E hE hEanti C with ⟨w, _hw, hwuniq⟩
  have hid : ExpandingSequence.CoconeMediates S C C (fun y : E => y) := by
    constructor
    · exact scottContinuous_id
    · intro n x
      rfl
  have hvuMed : ExpandingSequence.CoconeMediates S C C (fun y : E => v (u y)) := by
    constructor
    · exact ScottContinuous.comp hv.1 hu.1
    · intro n x
      calc
        v (u (C.f n x)) = v (CB.f n x) := by rw [hu.2 n x]
        _ = C.f n x := hv.2 n x
  have hvu : ∀ y : E, v (u y) = y := by
    intro y
    have hcomp : v (u y) = w y := hwuniq (fun y : E => v (u y)) hvuMed y
    have hidw : y = w y := hwuniq (fun y : E => y) hid y
    exact hcomp.trans hidw.symm
  let epFun : ∀ n : Nat, EPPair (D n) E := fun n =>
    { e := C.f n
      p := fun y : E => Bilimit.proj S n (u y)
      continuous_e := C.continuous n
      continuous_p :=
        ScottContinuous.comp
          (S.bilimitProj_scottContinuous_of_stage_dcpo hDdcpo hantisymm n) hu.1
      retract := by
        intro x
        calc
          Bilimit.proj S n (u (C.f n x))
              = Bilimit.proj S n (CB.f n x) := by rw [hu.2 n x]
          _ = x := by
              change Bilimit.proj S n (S.stageEmbedding hantisymm n x) = x
              exact (S.stageEPPair hDdcpo hantisymm n).retract x
      below := by
        intro y
        calc
          C.f n (Bilimit.proj S n (u y))
              = v (CB.f n (Bilimit.proj S n (u y))) := (hv.2 n _).symm
          _ ≤ v (u y) := by
              exact hv.1.1 ((S.stageEPPair hDdcpo hantisymm n).below (u y))
          _ = y := hvu y }
  refine ⟨{
    ep := epFun
    ep_e := by
      intro n x
      rfl
    sup_identity := ?_
  }⟩
  intro y
  constructor
  · intro z hz
    rcases hz with ⟨n, rfl⟩
    exact (epFun n).below y
  · intro b hb
    have hcanon :=
      (S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm).sup_identity (u y)
    have hub : IsUpperBound
        ({z : Bilimit S |
          ∃ n : Nat,
            z = (S.stageEPPair hDdcpo hantisymm n).e
              ((S.stageEPPair hDdcpo hantisymm n).p (u y))} : Set (Bilimit S))
        (u b) := by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      have hsource : C.f n (Bilimit.proj S n (u y)) ≤ b :=
        hb ⟨n, rfl⟩
      have hstage :
          (S.stageEPPair hDdcpo hantisymm n).e
              ((S.stageEPPair hDdcpo hantisymm n).p (u y)) =
            u (C.f n (Bilimit.proj S n (u y))) := by
        simpa [ExpandingSequence.stageEPPair, CB, ExpandingSequence.bilimitEmbeddingCocone]
          using (hu.2 n (Bilimit.proj S n (u y))).symm
      rw [hstage]
      exact hu.1.1 hsource
    have huyub : u y ≤ u b := hcanon.2 (u b) (by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      exact hub ⟨n, rfl⟩)
    calc
      y = v (u y) := (hvu y).symm
      _ ≤ v (u b) := hv.1.1 huyub
      _ = b := hvu b

/-- Legacy weak map-out predicate for an expanding sequence: a family of
continuous maps out of the stages, together with reverse continuous maps, gives a
map out of the explicit bilimit carrier.  It does not encode the cocone
commuting equations; the full cocone criterion is
`ColimitingCoconeCriterionFull`. -/
def ExpandingSequence.ColimitingCoconeCriterion
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) : Prop :=
  ∀ E : Type u, ∀ [Preorder E],
    (∃ f : ∀ n : Nat, D n → E, ∃ g : ∀ n : Nat, E → D n,
      ∀ n : Nat, ScottContinuous (f n) ∧ ScottContinuous (g n)) →
      Nonempty (Bilimit S → E)

/-- Lemma 3.3.8, legacy weak predicate: a family of stage maps induces a map out
of the bilimit carrier by using the zeroth projection.  This is weaker than the
full colimiting-cocone criterion in the book and does not encode the cocone
commuting equations. -/
theorem lemma_3_3_8_expanding_sequence_colimiting_cocone_criterion_legacy
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.ColimitingCoconeCriterion S := by
  intro E _ h
  rcases h with ⟨f, _g, _hfg⟩
  exact ⟨fun x => f 0 (Bilimit.proj S 0 x)⟩

/-- Lemma 3.3.8, full statement.

PDF text excerpt: "It is colimiting if and only if" the cocone maps come with
Scott-continuous e-p-pair projections `g_n : E → D_n` and satisfy
`⋁_{n∈N} f_n ∘ g_n = id_E`.

Current Lean spelling: prove both directions of the PDF criterion in the
preorder setting of `ColimitingCoconeCriterionFull`. -/
theorem lemma_3_3_8_expanding_sequence_colimiting_cocone_criterion
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.ColimitingCoconeCriterionFull S := by
  intro hDdcpo hantisymm E _ hE hEanti C
  constructor
  · intro hcolimiting
    exact ExpandingSequence.coconeEPDecomposition_of_isColimitingCocone
      S hDdcpo hantisymm hE hEanti hcolimiting
  · intro hdecomp
    rcases hdecomp with ⟨h⟩
    exact ExpandingSequence.isColimitingCocone_of_epDecomposition
      S hantisymm hE hEanti h

/-- Legacy weak map-to-carrier predicate for Proposition 3.3.9: a family of
continuous stage maps supplies a map from the bilimit carrier to the target.
This does not assert an embedding, projection, or cocone commuting law. -/
def ExpandingSequence.BilimitSubdomainOfCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) : Prop :=
  ∀ E : Type u, ∀ [Preorder E],
    (∃ f : ∀ n : Nat, D n → E, ∀ n : Nat, ScottContinuous (f n)) →
      Nonempty (Bilimit S → E)

/-- Proposition 3.3.9, legacy weak predicate: a family of stage maps supplies a
zeroth-projection map from the bilimit carrier.  PDF text: "where the `f_n` are
embeddings. Then the bilimit of the sequence is a sub-domain of `E`."  This
legacy predicate is weaker than the full subdomain embedding statement in the
book. -/
theorem prop_3_3_9_bilimit_subdomain_of_cocone_legacy
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.BilimitSubdomainOfCocone S := by
  intro E _ h
  rcases h with ⟨f, _hf⟩
  exact ⟨fun x => f 0 (Bilimit.proj S 0 x)⟩

/-- Proposition 3.3.9, full preorder-interface statement.

PDF text: "Let `⟨E,(f_n)_{n∈N}⟩` be a cocone over the expanding sequence
`⟨(D_n)_{n∈N}, (e_mn : D_n → D_m)_{n≤m∈N}⟩` where the `f_n` are embeddings.
Then the bilimit of the sequence is a sub-domain of `E`."

Current Lean spelling: for any dcpo cocone carrier whose legs are supplied as
embeddings, the bilimit embeds as a sub-domain of the cocone carrier via the
canonical supremum map. -/
theorem prop_3_3_9_bilimit_subdomain_of_cocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.BilimitSubdomainOfCoconeFull S := by
  intro _hDdcpo hantisymm E _ hE C hCNonempty
  rcases hCNonempty with ⟨hC⟩
  exact ExpandingSequence.bilimitSubdomainOf_of_embeddingData_canonical
    S hE C hC hantisymm

/-- Legacy weak limit-colimit coincidence predicate: packages only the current
carrier/projection data and the weak map-out predicate. -/
def ExpandingSequence.BilimitColimitCoincidence
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) : Prop :=
  ExpandingSequence.BilimitTheoremData S ∧ ExpandingSequence.ColimitingCoconeCriterion S

/-- Corollary 3.3.10, lightweight interface: packages the current bilimit carrier
data and weak colimiting-cocone criterion. -/
theorem cor_3_3_10_bilimit_colimit_embedding_projection_legacy
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.BilimitColimitCoincidence S := by
  exact ⟨theorem_3_3_7_expanding_sequence_bilimit_legacy S,
    lemma_3_3_8_expanding_sequence_colimiting_cocone_criterion_legacy S⟩

/-- Corollary 3.3.10, current preorder-interface statement.

PDF text: "The bilimit of an expanding sequence is also the colimit (limit) in
the restricted category of dcpo's with embeddings (projections) as morphisms."

Current Lean spelling: the canonical bilimit cones have the required
embedding/projection legs and satisfy universal properties against cones with
the same kind of restricted legs.  The universal mediating maps are now
packaged as embedding/projection morphisms, with uniqueness stated against all
ordinary continuous mediating maps. -/
theorem cor_3_3_10_bilimit_colimit_embedding_projection
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) :
    ExpandingSequence.RestrictedBilimitColimitCoincidence S := by
  intro hDdcpo hantisymm
  exact ⟨{
    bilimit_dcpo := S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm
    bilimit_antisymm := S.bilimit_antisymm_of_stage_antisymm hantisymm
    projectionCone := S.bilimitProjectionCone hDdcpo hantisymm
    projectionCone_proj := by
      intro n x
      rfl
    limiting_projection :=
      S.isRestrictedLimitingProjectionCone_bilimitProjectionCone hDdcpo hantisymm
    embeddingCocone := S.bilimitEmbeddingCocone hantisymm
    colimiting_embedding :=
      S.isRestrictedColimitingEmbeddingCocone_bilimitEmbeddingCocone hDdcpo hantisymm
  }⟩

/-- The stage-image union `⋃ n, e_n(B_n)` appearing in Theorem 3.3.11, with the
maps into the bilimit supplied explicitly by the theorem data. -/
def ExpandingSequence.BilimitBasisUnion
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (stageEmbed : ∀ n : Nat, D n → Bilimit S) (B : ∀ n : Nat, Set (D n)) :
    Set (Bilimit S) :=
  {x | ∃ n : Nat, ∃ b : D n, b ∈ B n ∧ x = stageEmbed n b}

/-- The compact-stage union `⋃ n, e_n(K(D_n))` from the algebraic part of
Theorem 3.3.11. -/
def ExpandingSequence.BilimitCompactUnion
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (stageEmbed : ∀ n : Nat, D n → Bilimit S) : Set (Bilimit S) :=
  ExpandingSequence.BilimitBasisUnion S stageEmbed
    (fun n : Nat => (Chapter2.CompactSet : Set (D n)))

/-- The canonical stage embedding sends stage approximants to bilimit
approximants.  This is the formal version of the proof step in Theorem 3.3.11
where the maps `e_n` are used as lower adjoints. -/
theorem ExpandingSequence.stageEmbedding_wayBelow_bilimit
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {n : Nat} {b : D n} {x : Bilimit S}
    (hb : b ≪ Bilimit.proj S n x) :
    S.stageEmbedding hantisymm n b ≪ x := by
  exact Chapter2.prop_2_2_2_2 le_rfl
    ((S.stageEPPair hDdcpo hantisymm n).wayBelow_iff.2 hb)
    ((S.stageEPPair hDdcpo hantisymm n).below x)

/-- The basis-union clause in Theorem 3.3.11: if each stage has a basis `B n`,
then the union of the images of those bases under the canonical bilimit stage
embeddings is a basis for the bilimit. -/
theorem ExpandingSequence.bilimitBasisUnion_isBasisRaw
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (B : ∀ n : Nat, Set (D n)) (hB : ∀ n : Nat, Chapter2.IsBasisRaw (B n)) :
    Chapter2.IsBasisRaw
      (ExpandingSequence.BilimitBasisUnion S (S.stageEmbedding hantisymm) B) := by
  intro x
  let A : Set (Bilimit S) :=
    {z | ∃ n : Nat, ∃ b : D n,
      b ∈ Chapter2.Approximants (B n) (Bilimit.proj S n x) ∧
        z = S.stageEmbedding hantisymm n b}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨n, b, hb, rfl⟩
    constructor
    · exact ⟨n, b, hb.1, rfl⟩
    · exact S.stageEmbedding_wayBelow_bilimit hDdcpo hantisymm hb.2
  · constructor
    · rcases hB 0 (Bilimit.proj S 0 x) with ⟨A0, hA0sub, hA0dir, _hA0sup⟩
      rcases hA0dir.1 with ⟨b0, hb0⟩
      exact ⟨S.stageEmbedding hantisymm 0 b0, 0, b0, hA0sub hb0, rfl⟩
    · intro z hz w hw
      rcases hz with ⟨n, b, hb, rfl⟩
      rcases hw with ⟨m, c, hc, rfl⟩
      let k : Nat := max n m
      have hnk : n ≤ k := Nat.le_max_left n m
      have hmk : m ≤ k := Nat.le_max_right n m
      have hbLiftWay :
          S.e hnk b ≪ Bilimit.proj S k x := by
        have hbEmb :
            S.e hnk b ≪ S.e hnk (Bilimit.proj S n x) :=
          ((S.epPair hnk).wayBelow_iff).2 hb.2
        have hxnk : Bilimit.proj S n x = S.p hnk (Bilimit.proj S k x) := by
          simpa [Bilimit.proj] using x.2 hnk
        have hbTarget :
            S.e hnk (Bilimit.proj S n x) ≤ Bilimit.proj S k x := by
          rw [hxnk]
          exact S.below hnk (Bilimit.proj S k x)
        exact Chapter2.prop_2_2_2_2 le_rfl hbEmb hbTarget
      have hcLiftWay :
          S.e hmk c ≪ Bilimit.proj S k x := by
        have hcEmb :
            S.e hmk c ≪ S.e hmk (Bilimit.proj S m x) :=
          ((S.epPair hmk).wayBelow_iff).2 hc.2
        have hxmk : Bilimit.proj S m x = S.p hmk (Bilimit.proj S k x) := by
          simpa [Bilimit.proj] using x.2 hmk
        have hcTarget :
            S.e hmk (Bilimit.proj S m x) ≤ Bilimit.proj S k x := by
          rw [hxmk]
          exact S.below hmk (Bilimit.proj S k x)
        exact Chapter2.prop_2_2_2_2 le_rfl hcEmb hcTarget
      have hKbasis : Chapter2.IsBasis (B k) := Chapter2.prop_2_2_4_1 (hB k)
      have hKdir :
          DirectedSet (Chapter2.Approximants (B k) (Bilimit.proj S k x)) :=
        (hKbasis (Bilimit.proj S k x)).1
      have hKsup :
          IsSup (Chapter2.Approximants (B k) (Bilimit.proj S k x))
            (Bilimit.proj S k x) :=
        (hKbasis (Bilimit.proj S k x)).2
      rcases hbLiftWay hKdir hKsup le_rfl with ⟨b', hb'Mem, hbLe⟩
      rcases hcLiftWay hKdir hKsup le_rfl with ⟨c', hc'Mem, hcLe⟩
      rcases hKdir.2 hb'Mem hc'Mem with ⟨d, hdMem, hb'd, hc'd⟩
      refine ⟨S.stageEmbedding hantisymm k d, ?_, ?_, ?_⟩
      · exact ⟨k, d, hdMem, rfl⟩
      · calc
          S.stageEmbedding hantisymm n b
              = S.stageEmbedding hantisymm k (S.e hnk b) := by
                  exact (S.stageEmbedding_commute hantisymm hnk b).symm
          _ ≤ S.stageEmbedding hantisymm k d :=
              (S.stageEmbedding_scottContinuous hantisymm k).1 (le_trans hbLe hb'd)
      · calc
          S.stageEmbedding hantisymm m c
              = S.stageEmbedding hantisymm k (S.e hmk c) := by
                  exact (S.stageEmbedding_commute hantisymm hmk c).symm
          _ ≤ S.stageEmbedding hantisymm k d :=
              (S.stageEmbedding_scottContinuous hantisymm k).1 (le_trans hcLe hc'd)
  · constructor
    · intro z hz
      rcases hz with ⟨n, b, hb, rfl⟩
      have hbLe : b ≤ Bilimit.proj S n x := Chapter2.prop_2_2_2_1 hb.2
      calc
        S.stageEmbedding hantisymm n b
            ≤ S.stageEmbedding hantisymm n (Bilimit.proj S n x) :=
              (S.stageEmbedding_scottContinuous hantisymm n).1 hbLe
        _ ≤ x := (S.stageEPPair hDdcpo hantisymm n).below x
    · intro y hy i
      have hIbasis : Chapter2.IsBasis (B i) := Chapter2.prop_2_2_4_1 (hB i)
      exact ((hIbasis (Bilimit.proj S i x)).2).2 (Bilimit.proj S i y) (by
        intro b hb
        have hUpper :
            S.stageEmbedding hantisymm i b ≤ y :=
          hy ⟨i, b, hb, rfl⟩
        calc
          b = Bilimit.proj S i (S.stageEmbedding hantisymm i b) := by
                exact ((S.stageEPPair hDdcpo hantisymm i).retract b).symm
          _ ≤ Bilimit.proj S i y :=
                (S.bilimitProj_scottContinuous_of_stage_dcpo hDdcpo hantisymm i).1 hUpper)

/-- Countability of the stage-image union used in the omega clauses of Theorem
3.3.11. -/
theorem ExpandingSequence.bilimitBasisUnion_countable
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (B : ∀ n : Nat, Set (D n)) (hBcount : ∀ n : Nat, (B n).Countable) :
    (ExpandingSequence.BilimitBasisUnion S (S.stageEmbedding hantisymm) B).Countable := by
  refine Set.Countable.mono ?_
    (Set.countable_iUnion
      (fun n : Nat => Set.Countable.image (hBcount n) (S.stageEmbedding hantisymm n)))
  intro x hx
  rcases hx with ⟨n, b, hb, rfl⟩
  exact Set.mem_iUnion.2 ⟨n, b, hb, rfl⟩

/-- The compact-basis equality in Theorem 3.3.11: for an algebraic expanding
sequence, compact elements of the bilimit are exactly the images of compact
elements from finite stages. -/
theorem ExpandingSequence.bilimitCompactSet_eq
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (hAlg : ∀ n : Nat, IsAlgebraicDomain (D n)) :
    (Chapter2.CompactSet : Set (Bilimit S)) =
      ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm) := by
  ext x
  constructor
  · intro hxCompact
    have hBasisRaw :
        Chapter2.IsBasisRaw
          (ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm)) :=
      S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm
        (fun n : Nat => (Chapter2.CompactSet : Set (D n)))
        (fun n => Chapter2.basis_to_raw (hAlg n))
    rcases hBasisRaw x with ⟨A, hAsub, hAdir, hAsup⟩
    have hxWay : x ≪ x := by
      simpa [Chapter2.CompactSet, Chapter2.Compact] using hxCompact
    rcases hxWay hAdir hAsup le_rfl with ⟨a, ha, hxa⟩
    have haApprox := hAsub ha
    have hax : a ≤ x := Chapter2.prop_2_2_2_1 haApprox.2
    have hEq : x = a :=
      S.bilimit_antisymm_of_stage_antisymm hantisymm x a hxa hax
    simpa [hEq] using haApprox.1
  · intro hxUnion
    rcases hxUnion with ⟨n, c, hcCompact, rfl⟩
    have hcWay : c ≪ c := by
      simpa [Chapter2.CompactSet, Chapter2.Compact] using hcCompact
    have hProj :
        Bilimit.proj S n (S.stageEmbedding hantisymm n c) = c :=
      (S.stageEPPair hDdcpo hantisymm n).retract c
    have hcProjWay : c ≪ Bilimit.proj S n (S.stageEmbedding hantisymm n c) := by
      simpa [hProj] using hcWay
    exact S.stageEmbedding_wayBelow_bilimit hDdcpo hantisymm hcProjWay

/-- Bilimit preservation, continuous-domain component of Theorem 3.3.11.

Current Lean spelling: Chapter 3's `IsContinuousDomain` uses the strong basis
predicate `IsBasis`; the full theorem supplies the explicit stage dcpo and
antisymmetry hypotheses needed by the preorder interface. -/
def ExpandingSequence.BilimitPreservation
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) : Prop :=
  (∀ n : Nat, IsContinuousDomain (D n)) → IsContinuousDomain (Bilimit S)

/-- Theorem 3.3.11 full data package.

PDF text: "Let `⟨(D_n)_{n∈N}, (e_mn : D_n → D_m)_{n≤m∈N}⟩` be an expanding
sequence and `⟨D,(e_n)_{n∈N}⟩` its bilimit. (1) If all `D_n` are
`(ω-)continuous` then so is `D`. If we are given bases `B_n`, `n ∈ N`, for each
`D_n` then a basis for `D` is given by `⋃_{n∈N} e_n(B_n)`. (2) If all `D_n`
are `(ω-)algebraic` then so is `D` and `K(D) = ⋃_{n∈N} e_n(K(D_n))`."

Current Lean spelling: stage dcpo and stage antisymmetry hypotheses are explicit.
The continuous/algebraic fields use Chapter 3's strong basis predicates, while
the omega fields and the explicit basis-union clauses use the Chapter 2 raw
basis/countability predicates. -/
structure ExpandingSequence.BilimitPreservationData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) where
  stageEmbed : ∀ n : Nat, D n → Bilimit S
  stageEmbed_continuous : ∀ n : Nat, ScottContinuous (stageEmbed n)
  stageEmbed_retract : ∀ n : Nat, ∀ x : D n, Bilimit.proj S n (stageEmbed n x) = x
  stageEmbed_below : ∀ n : Nat, ∀ y : Bilimit S, stageEmbed n (Bilimit.proj S n y) ≤ y
  stageEmbed_commute :
    ∀ {n m : Nat}, ∀ h : n ≤ m, ∀ x : D n, stageEmbed m (S.e h x) = stageEmbed n x
  continuous : (∀ n : Nat, IsContinuousDomain (D n)) → IsContinuousDomain (Bilimit S)
  omega_continuous :
    (∀ n : Nat, Chapter2.IsOmegaContinuousDomain (D n)) →
      Chapter2.IsOmegaContinuousDomain (Bilimit S)
  basis_union :
    ∀ B : ∀ n : Nat, Set (D n), (∀ n : Nat, Chapter2.IsBasisRaw (B n)) →
      Chapter2.IsBasisRaw (ExpandingSequence.BilimitBasisUnion S stageEmbed B)
  algebraic : (∀ n : Nat, IsAlgebraicDomain (D n)) → IsAlgebraicDomain (Bilimit S)
  omega_algebraic :
    (∀ n : Nat, Chapter2.IsOmegaAlgebraicDomain (D n)) →
      Chapter2.IsOmegaAlgebraicDomain (Bilimit S)
  compact_eq :
    (∀ n : Nat, IsAlgebraicDomain (D n)) →
      (Chapter2.CompactSet : Set (Bilimit S)) =
        ExpandingSequence.BilimitCompactUnion S stageEmbed

/-- Theorem 3.3.11, full preservation package for bilimits of expanding
sequences.  PDF text: if all stages are `(ω-)continuous`, then so is the
bilimit and supplied bases combine as `⋃_{n∈N} e_n(B_n)`; if all stages are
`(ω-)algebraic`, then so is the bilimit and
`K(D) = ⋃_{n∈N} e_n(K(D_n))`.

The proof formalizes the PDF's elementwise argument using the directed family
`⋃ n, e_n(B_{p_n x})`, countable unions of stage-image bases, and the compact
stage equality.  As elsewhere in this section, the current preorder interface
takes stage dcpo and stage antisymmetry as explicit hypotheses. -/
noncomputable def theorem_3_3_11_expanding_sequence_bilimit_preservation_full
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.BilimitPreservationData S hDdcpo hantisymm := by
  refine
    { stageEmbed := S.stageEmbedding hantisymm
      stageEmbed_continuous := S.stageEmbedding_scottContinuous hantisymm
      stageEmbed_retract := ?_
      stageEmbed_below := ?_
      stageEmbed_commute := ?_
      continuous := ?_
      omega_continuous := ?_
      basis_union := ?_
      algebraic := ?_
      omega_algebraic := ?_
      compact_eq := S.bilimitCompactSet_eq hDdcpo hantisymm }
  · intro n x
    have hproof :
        Nat.le_max_right n n = Nat.le_max_left n n := Subsingleton.elim _ _
    change S.stageProjectionMap n n x = x
    unfold ExpandingSequence.stageProjectionMap
    rw [hproof]
    exact S.retract (Nat.le_max_left n n) x
  · intro n y i
    let k : Nat := max i n
    have hik : i ≤ k := Nat.le_max_left i n
    have hnk : n ≤ k := Nat.le_max_right i n
    calc
      Bilimit.proj S i (S.stageEmbedding hantisymm n (Bilimit.proj S n y))
          = S.stageProjectionMap n i (Bilimit.proj S n y) := rfl
      _ = S.p hik (S.e hnk (S.p hnk (Bilimit.proj S k y))) := by
          unfold ExpandingSequence.stageProjectionMap
          rw [show Bilimit.proj S n y = S.p hnk (Bilimit.proj S k y) by
            simpa [Bilimit.proj] using y.2 hnk]
      _ ≤ S.p hik (Bilimit.proj S k y) :=
          (S.continuous_p hik).1 (S.below hnk (Bilimit.proj S k y))
      _ = Bilimit.proj S i y := by
          simpa [Bilimit.proj] using (y.2 hik).symm
  · intro n m h x
    exact S.stageEmbedding_commute hantisymm h x
  · intro hCont
    choose B hB using hCont
    exact ⟨ExpandingSequence.BilimitBasisUnion S (S.stageEmbedding hantisymm) B,
      Chapter2.prop_2_2_4_1
        (S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm B
          (fun n => Chapter2.basis_to_raw (hB n)))⟩
  · intro hOmega
    choose B hBcount hBraw using hOmega
    exact ⟨ExpandingSequence.BilimitBasisUnion S (S.stageEmbedding hantisymm) B,
      S.bilimitBasisUnion_countable hantisymm B hBcount,
      S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm B hBraw⟩
  · intro B hB
    exact S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm B hB
  · intro hAlg
    have hBasisRaw :
        Chapter2.IsBasisRaw
          (ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm)) :=
      S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm
        (fun n : Nat => (Chapter2.CompactSet : Set (D n)))
        (fun n => Chapter2.basis_to_raw (hAlg n))
    have hCompactEq :
        (Chapter2.CompactSet : Set (Bilimit S)) =
          ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm) := by
      exact S.bilimitCompactSet_eq hDdcpo hantisymm hAlg
    change Chapter2.IsBasis (Chapter2.CompactSet : Set (Bilimit S))
    rw [hCompactEq]
    exact Chapter2.prop_2_2_4_1 hBasisRaw
  · intro hOmegaAlg
    have hAlg : ∀ n : Nat, IsAlgebraicDomain (D n) :=
      fun n => Chapter2.prop_2_2_4_1 (hOmegaAlg n).2
    have hCompactEq :
        (Chapter2.CompactSet : Set (Bilimit S)) =
          ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm) :=
      S.bilimitCompactSet_eq hDdcpo hantisymm hAlg
    have hCountUnion :
        (ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm)).Countable :=
      S.bilimitBasisUnion_countable hantisymm
        (fun n : Nat => (Chapter2.CompactSet : Set (D n)))
        (fun n => (hOmegaAlg n).1)
    have hBasisUnion :
        Chapter2.IsBasisRaw
          (ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm)) :=
      S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm
        (fun n : Nat => (Chapter2.CompactSet : Set (D n)))
        (fun n => (hOmegaAlg n).2)
    constructor
    · rw [hCompactEq]
      exact hCountUnion
    · rw [hCompactEq]
      exact hBasisUnion

/-- Theorem 3.3.11, theorem-facing existence wrapper for the complete
continuity, algebraicity, basis-union, and compact-union package. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_preservation_full_exists
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    Nonempty (ExpandingSequence.BilimitPreservationData S hDdcpo hantisymm) :=
  ⟨theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm⟩

/-- Theorem 3.3.11(1), continuous branch: if every stage has a Chapter 3 strong
basis, then the bilimit has a Chapter 3 strong basis. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_preservation
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.BilimitPreservation S := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).continuous

/-- Theorem 3.3.11(1), omega-continuous branch: if every stage has a countable
Chapter 2 raw basis, then the bilimit has one. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_omega_continuous
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    (∀ n : Nat, Chapter2.IsOmegaContinuousDomain (D n)) →
      Chapter2.IsOmegaContinuousDomain (Bilimit S) := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).omega_continuous

/-- Theorem 3.3.11(1), basis clause: given Chapter 2 raw bases `B_n` for the
stages, the union of their images under the bilimit stage embeddings is a raw
basis for the bilimit. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_basis_union
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (B : ∀ n : Nat, Set (D n))
    (hB : ∀ n : Nat, Chapter2.IsBasisRaw (B n)) :
    Chapter2.IsBasisRaw (ExpandingSequence.BilimitBasisUnion S
      (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).stageEmbed B) := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).basis_union B hB

/-- Theorem 3.3.11(2), algebraic branch: if the compact elements form a Chapter
3 strong basis at every stage, then they form a strong basis for the bilimit. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_algebraic
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    (∀ n : Nat, IsAlgebraicDomain (D n)) → IsAlgebraicDomain (Bilimit S) := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).algebraic

/-- Theorem 3.3.11(2), omega-algebraic branch: if each stage has a countable
Chapter 2 raw compact basis, then the bilimit has one. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_omega_algebraic
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    (∀ n : Nat, Chapter2.IsOmegaAlgebraicDomain (D n)) →
      Chapter2.IsOmegaAlgebraicDomain (Bilimit S) := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).omega_algebraic

/-- Theorem 3.3.11(2), compact-basis clause: in the algebraic case, the compact
elements of the bilimit are exactly the union of the images of the compact
elements of the stages. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_compact_eq
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (hAlg : ∀ n : Nat, IsAlgebraicDomain (D n)) :
    (Chapter2.CompactSet : Set (Bilimit S)) =
      ExpandingSequence.BilimitCompactUnion S
        (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).stageEmbed := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).compact_eq hAlg

namespace StrictContFun

/-- Evaluation of a directed family of strict maps is directed pointwise. -/
theorem eval_directed
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {A : Set (StrictContFun D E)} (hA : DirectedSet A) (d : D) :
    DirectedSet ((fun f : StrictContFun D E => f d) '' A) :=
  DirectedSet.image (f := fun f : StrictContFun D E => f d)
    (by intro f g hfg; exact hfg d) hA

/-- Pointwise supremum of a directed family of strict continuous maps. -/
noncomputable def directedSupFun
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    D → E :=
  fun d => Classical.choose (hE ((fun f : StrictContFun D E => f d) '' A)
    (StrictContFun.eval_directed hA d))

/-- The pointwise value of `directedSupFun` is the supremum of the pointwise
evaluation set. -/
theorem directedSupFun_isSup_eval
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A)
    (d : D) :
    IsSup ((fun f : StrictContFun D E => f d) '' A)
      (StrictContFun.directedSupFun hE A hA d) :=
  Classical.choose_spec (hE ((fun f : StrictContFun D E => f d) '' A)
    (StrictContFun.eval_directed hA d))

/-- The pointwise directed supremum of strict continuous maps is monotone. -/
theorem directedSupFun_monotone
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    Monotone (StrictContFun.directedSupFun hE A hA) := by
  intro d e hde
  exact (StrictContFun.directedSupFun_isSup_eval hE A hA d).2
    (StrictContFun.directedSupFun hE A hA e) (by
      intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact le_trans (f.continuous.1 hde)
        ((StrictContFun.directedSupFun_isSup_eval hE A hA e).1 ⟨f, hfA, rfl⟩))

/-- The pointwise directed supremum of strict continuous maps is
Scott-continuous. -/
theorem directedSupFun_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    ScottContinuous (StrictContFun.directedSupFun hE A hA) := by
  constructor
  · exact StrictContFun.directedSupFun_monotone hE A hA
  · intro B s hB hs
    constructor
    · intro y hy
      rcases hy with ⟨b, hb, rfl⟩
      exact StrictContFun.directedSupFun_monotone hE A hA (hs.1 hb)
    · intro y hy
      exact (StrictContFun.directedSupFun_isSup_eval hE A hA s).2 y (by
        intro z hz
        rcases hz with ⟨f, hfA, rfl⟩
        exact (f.continuous.2 hB hs).2 y (by
          intro fb hfb
          rcases hfb with ⟨b, hb, rfl⟩
          exact le_trans
            ((StrictContFun.directedSupFun_isSup_eval hE A hA b).1 ⟨f, hfA, rfl⟩)
            (hy ⟨b, hb, rfl⟩)))

/-- The pointwise directed supremum of strict maps is still strict. -/
theorem directedSupFun_preservesLeast
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    PreservesLeastElement (StrictContFun.directedSupFun hE A hA) := by
  intro d hd y
  exact (StrictContFun.directedSupFun_isSup_eval hE A hA d).2 y (by
    intro z hz
    rcases hz with ⟨f, _hfA, rfl⟩
    exact f.strict d hd y)

/-- Directed supremum in the strict continuous function space. -/
noncomputable def directedSup
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    StrictContFun D E where
  toFun := StrictContFun.directedSupFun hE A hA
  continuous := StrictContFun.directedSupFun_scottContinuous hE A hA
  strict := StrictContFun.directedSupFun_preservesLeast hE A hA

/-- The constructed pointwise strict function is the supremum of the directed
family. -/
theorem directedSup_isSup
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    IsSup A (StrictContFun.directedSup hE A hA) := by
  constructor
  · intro f hfA x
    change f x ≤ StrictContFun.directedSupFun hE A hA x
    exact (StrictContFun.directedSupFun_isSup_eval hE A hA x).1 ⟨f, hfA, rfl⟩
  · intro g hg x
    change StrictContFun.directedSupFun hE A hA x ≤ g x
    exact (StrictContFun.directedSupFun_isSup_eval hE A hA x).2 (g x) (by
      intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact hg hfA x)

/-- If the codomain is a dcpo, then strict continuous maps into it form a dcpo
under the pointwise order. -/
theorem isDcpo_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) : IsDcpo (StrictContFun D E) := by
  intro A hA
  exact ⟨StrictContFun.directedSup hE A hA, StrictContFun.directedSup_isSup hE A hA⟩

/-- Evaluation at a point is Scott-continuous for strict continuous maps under
the pointwise function-space dcpo. -/
theorem eval_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (d : D) : ScottContinuous (fun f : StrictContFun D E => f d) := by
  constructor
  · intro f g hfg
    exact hfg d
  · intro A s hA hs
    constructor
    · intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact hs.1 hfA d
    · intro y hy
      have hPointSup : IsSup A (StrictContFun.directedSup hE A hA) :=
        StrictContFun.directedSup_isSup hE A hA
      exact le_trans ((hs.2 (StrictContFun.directedSup hE A hA) hPointSup.1) d)
        ((StrictContFun.directedSupFun_isSup_eval hE A hA d).2 y hy)

/-- The application map `[D -> E]! × D -> E` is Scott-continuous. -/
theorem apply_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) :
    ScottContinuous (fun p : StrictContFun D E × D => p.1 p.2) := by
  exact (lemma_3_2_6_continuous_iff_separately_continuous
    (fun p : StrictContFun D E × D => p.1 p.2)).2
    ⟨fun f => f.continuous, fun d => StrictContFun.eval_scottContinuous hE d⟩

/-- Support for Theorem 3.3.4: a least codomain element gives the constant
least strict continuous function. -/
def const {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (e : E) (he : Chapter2.IsLeast e) : StrictContFun D E where
  toFun := fun _ => e
  continuous := const_scottContinuous e
  strict := fun _ _ => he

/-- The constant least strict function is least in the pointwise order. -/
theorem const_isLeast
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] {e : E}
    (he : Chapter2.IsLeast e) :
    Chapter2.IsLeast (StrictContFun.const (D := D) (E := E) e he) := by
  intro f x
  exact he (f x)

/-- A pointed codomain makes the strict continuous function space pointed. -/
theorem hasLeastElement_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : HasLeastElement E) : HasLeastElement (StrictContFun D E) := by
  rcases hE with ⟨e, he⟩
  exact ⟨StrictContFun.const (D := D) (E := E) e he, StrictContFun.const_isLeast he⟩

/-- Antisymmetry of the codomain transfers to strict continuous functions. -/
theorem antisymmetric_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsAntisymmetricOrder E) : IsAntisymmetricOrder (StrictContFun D E) := by
  intro f g hfg hgf
  cases f with
  | mk f hf hs =>
      cases g with
      | mk g hg gs =>
          have hfun : f = g := funext fun x => hE (f x) (g x) (hfg x) (hgf x)
          subst hfun
          congr

end StrictContFun

namespace StrictContFun

/-- The strict continuous function-space carrier is a pointed partial-order
dcpo whenever the codomain is. -/
theorem strictPointedFunctionSpaceObjectSupport :
    StrictPointedFunctionSpaceObjectSupport.{u} := by
  intro D E _ _ _hDdcpo _hDanti _hDpointed hEdcpo hEanti hEpointed
  exact ⟨StrictContFun.isDcpo_of_codomain hEdcpo,
    StrictContFun.antisymmetric_of_codomain hEanti,
    StrictContFun.hasLeastElement_of_codomain hEpointed⟩

/-- The concrete strict continuous function space supplies the strict-pointed
internal-hom comparison. -/
theorem strictPointedInternalHomComparison :
    StrictPointedInternalHomComparison.{u} := by
  intro D E _ _ _hDdcpo _hDanti _hDpointed hEdcpo hEanti hEpointed
  refine ⟨StrictContFun D E, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact StrictContFun.isDcpo_of_codomain hEdcpo
  · exact StrictContFun.antisymmetric_of_codomain hEanti
  · exact StrictContFun.hasLeastElement_of_codomain hEpointed
  · exact ⟨OrderIsoData.refl (StrictContFun D E)⟩

/-- Build the current strict-pointed monoidal-closed interface once the strict
internal-hom comparison is supplied.  The smash tensor-hom adjunction is
registered separately by `StrictPointedTensorHomAdjunction`. -/
theorem strictPointedDCPOMonoidalClosedCore_of_internalHomComparison
    (h : StrictPointedInternalHomComparison.{u}) :
    StrictPointedDCPOMonoidalClosedCore.{u} :=
  ⟨StrictContFun.strictPointedFunctionSpaceObjectSupport, h⟩

/-- The object/internal-hom component supplied by the concrete strict function
space.  The tensor-hom component is constructed below. -/
theorem strictPointedDCPOMonoidalClosedCore :
    StrictPointedDCPOMonoidalClosedCore.{u} :=
  StrictContFun.strictPointedDCPOMonoidalClosedCore_of_internalHomComparison
    StrictContFun.strictPointedInternalHomComparison

/-- One direction of the smash tensor/function-space adjunction: a strict
continuous map out of the smash product curries to a strict continuous map into
the strict function space.  This is support for Theorem 3.3.4's tensor-hom
adjunction; the inverse uncurrying direction and order-isomorphism package are
not claimed here. -/
noncomputable def smashCurryBundled
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (f : StrictContFun (SmashProduct D E) F) :
    StrictContFun D (StrictContFun E F) where
  toFun := fun d =>
    { toFun := fun e => f (SmashProduct.mk (D := D) (E := E) d e)
      continuous :=
        ScottContinuous.comp f.continuous
          (SmashProduct.mk_right_section_scottContinuous (D := D) (E := E)
            hDbot hEbot d)
      strict := by
        intro e he
        have hebot : e = ⊥ := hEbot e (he ⊥)
        subst e
        change Chapter2.IsLeast (f (SmashProduct.mk (D := D) (E := E) d ⊥))
        rw [SmashProduct.mk_bot_right (D := D) (E := E) d]
        exact f.strict (⊥ : SmashProduct D E)
          (SmashProduct.bot_isLeast (D := D) (E := E)) }
  continuous := by
    constructor
    · intro d₁ d₂ hd e
      exact f.continuous.1
        (SmashProduct.mk_monotone (D := D) (E := E) hDbot hEbot
          (show (d₁, e) ≤ (d₂, e) from ⟨hd, le_rfl⟩))
    · intro A s hA hs
      constructor
      · intro y hy e
        rcases hy with ⟨d, hdA, rfl⟩
        exact f.continuous.1
          (SmashProduct.mk_monotone (D := D) (E := E) hDbot hEbot
            (show (d, e) ≤ (s, e) from ⟨hs.1 hdA, le_rfl⟩))
      · intro g hg e
        have hsection :
            ScottContinuous (fun d : D => SmashProduct.mk (D := D) (E := E) d e) :=
          SmashProduct.mk_left_section_scottContinuous (D := D) (E := E)
            hDbot hEbot e
        have hsectionSup :
            IsSup ((fun d : D => SmashProduct.mk (D := D) (E := E) d e) '' A)
              (SmashProduct.mk (D := D) (E := E) s e) :=
          hsection.2 hA hs
        have hsectionDir :
            DirectedSet ((fun d : D => SmashProduct.mk (D := D) (E := E) d e) '' A) :=
          DirectedSet.image hsection.1 hA
        have hfSup :
            IsSup
              (f '' ((fun d : D => SmashProduct.mk (D := D) (E := E) d e) '' A))
              (f (SmashProduct.mk (D := D) (E := E) s e)) :=
          f.continuous.2 hsectionDir hsectionSup
        exact hfSup.2 (g e) (by
          intro y hy
          rcases hy with ⟨z, hz, rfl⟩
          rcases hz with ⟨d, hdA, rfl⟩
          exact hg ⟨d, hdA, rfl⟩ e)
  strict := by
    intro d hd g e
    have hdbot : d = ⊥ := hDbot d (hd ⊥)
    subst d
    change f (SmashProduct.mk (D := D) (E := E) ⊥ e) ≤ g e
    rw [SmashProduct.mk_bot_left (D := D) (E := E)]
    exact f.strict (⊥ : SmashProduct D E)
      (SmashProduct.bot_isLeast (D := D) (E := E)) (g e)

/-- The other direction of the concrete smash tensor/function-space adjunction:
a strict continuous map into the strict function space uncurries to a strict
continuous map out of the smash product.  This still does not claim the full
order-isomorphism package. -/
noncomputable def smashUncurryBundled
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F] [OrderBot D] [OrderBot E]
    (hF : IsDcpo F)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (g : StrictContFun D (StrictContFun E F)) :
    StrictContFun (SmashProduct D E) F where
  toFun := fun z => g (SmashProduct.toProd (D := D) (E := E) z).1
    (SmashProduct.toProd (D := D) (E := E) z).2
  continuous := by
    have hProduct :
        ScottContinuous (fun p : D × E => g p.1 p.2) := by
      exact (lemma_3_2_6_continuous_iff_separately_continuous
        (fun p : D × E => g p.1 p.2)).2
        ⟨fun d => (g d).continuous,
          fun e => ScottContinuous.comp
            (StrictContFun.eval_scottContinuous hF e) g.continuous⟩
    exact ScottContinuous.comp
      (f := fun p : D × E => g p.1 p.2)
      (g := SmashProduct.toProd (D := D) (E := E))
      hProduct
      (SmashProduct.toProd_scottContinuous (D := D) (E := E) hDbot hEbot)
  strict := by
    intro z hz y
    have hzbot : z = (⊥ : SmashProduct D E) :=
      SmashProduct.eq_bot_of_le_bot (D := D) (E := E) (hz ⊥)
    subst z
    change g ⊥ ⊥ ≤ y
    exact (g ⊥).strict ⊥ (fun e : E => bot_le) y

/-- Uncurrying after currying a strict map out of the smash product returns the
original strict map. -/
theorem smashUncurry_smashCurryBundled
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F] [OrderBot D] [OrderBot E]
    (hF : IsDcpo F)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (f : StrictContFun (SmashProduct D E) F) :
    StrictContFun.smashUncurryBundled hF hDbot hEbot
        (StrictContFun.smashCurryBundled hDbot hEbot f) = f := by
  apply StrictContFun.ext_apply
  intro z
  change f (SmashProduct.mk (D := D) (E := E)
    (SmashProduct.toProd (D := D) (E := E) z).1
    (SmashProduct.toProd (D := D) (E := E) z).2) = f z
  rw [SmashProduct.mk_toProd (D := D) (E := E) z]

/-- Currying after uncurrying a strict map into the strict function space
returns the original map.  The codomain antisymmetry hypothesis is needed in
the local preorder interface to identify the two least values produced when a
smash coordinate is bottom. -/
theorem smashCurry_smashUncurryBundled
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F] [OrderBot D] [OrderBot E]
    (hFdcpo : IsDcpo F) (hFanti : IsAntisymmetricOrder F)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (g : StrictContFun D (StrictContFun E F)) :
    StrictContFun.smashCurryBundled hDbot hEbot
        (StrictContFun.smashUncurryBundled hFdcpo hDbot hEbot g) = g := by
  apply StrictContFun.ext_apply
  intro d
  apply StrictContFun.ext_apply
  intro e
  change
    g (SmashProduct.toProd (D := D) (E := E)
        (SmashProduct.mk (D := D) (E := E) d e)).1
      (SmashProduct.toProd (D := D) (E := E)
        (SmashProduct.mk (D := D) (E := E) d e)).2 = g d e
  by_cases hd : d = ⊥
  · subst d
    rw [SmashProduct.mk_bot_left (D := D) (E := E)]
    have hleastFun : Chapter2.IsLeast (g (⊥ : D)) :=
      g.strict ⊥ (fun x : D => bot_le)
    have hleastValue : Chapter2.IsLeast ((g (⊥ : D)) ⊥) :=
      (g (⊥ : D)).strict ⊥ (fun y : E => bot_le)
    have hle₁ : (g (⊥ : D)) ⊥ ≤ (g (⊥ : D)) e := hleastValue _
    let hconst :
        StrictContFun E F :=
      StrictContFun.const (D := E) (E := F) ((g (⊥ : D)) ⊥) hleastValue
    have hle₂ : (g (⊥ : D)) e ≤ (g (⊥ : D)) ⊥ := by
      have hle₂' := hleastFun hconst e
      change (g (⊥ : D)) e ≤ hconst e at hle₂'
      simpa [hconst, StrictContFun.const] using hle₂'
    exact hFanti _ _ hle₁ hle₂
  · by_cases he : e = ⊥
    · subst e
      rw [SmashProduct.mk_bot_right (D := D) (E := E)]
      have hleastFun : Chapter2.IsLeast (g (⊥ : D)) :=
        g.strict ⊥ (fun x : D => bot_le)
      have hle₁ : (g (⊥ : D)) ⊥ ≤ (g d) ⊥ := hleastFun (g d) ⊥
      have hleastValue : Chapter2.IsLeast ((g d) ⊥) :=
        (g d).strict ⊥ (fun y : E => bot_le)
      have hle₂ : (g d) ⊥ ≤ (g (⊥ : D)) ⊥ := hleastValue _
      exact hFanti _ _ hle₁ hle₂
    · rw [SmashProduct.mk_of_ne (D := D) (E := E) hd he]
      simp [SmashProduct.toProd]

/-- Concrete order-isomorphism data for the smash tensor/function-space
correspondence in `DCPO⊥!`.  This is still a concrete carrier-level statement;
comparison with arbitrary chosen internal-hom objects remains separate. -/
noncomputable def smashTensorHomOrderIsoData
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F] [OrderBot D] [OrderBot E]
    (hFdcpo : IsDcpo F) (hFanti : IsAntisymmetricOrder F)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    OrderIsoData (StrictContFun (SmashProduct D E) F)
      (StrictContFun D (StrictContFun E F)) where
  toFun := StrictContFun.smashCurryBundled hDbot hEbot
  invFun := StrictContFun.smashUncurryBundled hFdcpo hDbot hEbot
  left_inv := StrictContFun.smashUncurry_smashCurryBundled hFdcpo hDbot hEbot
  right_inv := StrictContFun.smashCurry_smashUncurryBundled hFdcpo hFanti hDbot hEbot
  monotone_to := by
    intro f g hfg d e
    exact hfg (SmashProduct.mk (D := D) (E := E) d e)
  monotone_inv := by
    intro f g hfg z
    exact hfg (SmashProduct.toProd (D := D) (E := E) z).1
      (SmashProduct.toProd (D := D) (E := E) z).2

/-- The concrete smash tensor/function-space order isomorphism supplies the
tensor-hom support for `DCPO⊥!` in the current preorder interface. -/
theorem strictPointedTensorHomAdjunction :
    StrictPointedTensorHomAdjunction.{u} := by
  intro D E F _ _ _ _ _ _hDdcpo _hDanti _hDpointed _hEdcpo _hEanti _hEpointed
    hFdcpo hFanti _hFpointed hDbot hEbot
  exact ⟨StrictContFun.smashTensorHomOrderIsoData hFdcpo hFanti hDbot hEbot⟩

/-- The concrete strict function space and smash product supply the complete
local monoidal-closed interface. -/
theorem strictPointedDCPOMonoidalClosed :
    StrictPointedDCPOMonoidalClosed.{u} :=
  ⟨StrictContFun.strictPointedDCPOMonoidalClosedCore,
    StrictContFun.strictPointedTensorHomAdjunction⟩

/-- Compatibility theorem exposing both components of the monoidal-closed
interface. -/
theorem theorem_3_3_4_strict_pointed_dcpo_monoidal_closed_with_tensor_hom_concrete :
    StrictPointedDCPOMonoidalClosed.{u} :=
  StrictContFun.strictPointedDCPOMonoidalClosed

/-- Theorem 3.3.4: `DCPO⊥!` is monoidal closed, complete and cocomplete in
the chapter's concrete category interface.  Cocompleteness remains the
explicit book-omitted proof debt recorded above. -/
theorem theorem_3_3_4_strict_pointed_dcpo_monoidal_closed_complete_cocomplete :
    StrictPointedDCPOMonoidalClosed.{u} ∧
      StrictPointedDCPOHasAllLimits.{u, v, w, z} ∧
        StrictPointedDCPOHasAllColimits.{u, v, w, z} :=
  theorem_3_3_4_strict_pointed_dcpo_monoidal_closed_complete_cocomplete_of_monoidalClosed
    StrictContFun.strictPointedDCPOMonoidalClosed
    theorem_3_3_4_strict_pointed_dcpo_complete

end StrictContFun

namespace ContFun

/-- Evaluation of a directed family of continuous maps is directed pointwise. -/
theorem eval_directed
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {A : Set (ContFun D E)} (hA : DirectedSet A) (d : D) :
    DirectedSet ((fun f : ContFun D E => f d) '' A) :=
  DirectedSet.image (f := fun f : ContFun D E => f d)
    (by intro f g hfg; exact hfg d) hA

/-- Pointwise supremum of a directed family of continuous maps. -/
noncomputable def directedSupFun
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) : D → E :=
  fun d => Classical.choose (hE ((fun f : ContFun D E => f d) '' A)
    (ContFun.eval_directed hA d))

/-- The pointwise value of `directedSupFun` is the supremum of the pointwise
evaluation set. -/
theorem directedSupFun_isSup_eval
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) (d : D) :
    IsSup ((fun f : ContFun D E => f d) '' A)
      (ContFun.directedSupFun hE A hA d) :=
  Classical.choose_spec (hE ((fun f : ContFun D E => f d) '' A)
    (ContFun.eval_directed hA d))

/-- The pointwise directed supremum of continuous maps is monotone. -/
theorem directedSupFun_monotone
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) :
    Monotone (ContFun.directedSupFun hE A hA) := by
  intro d e hde
  exact (ContFun.directedSupFun_isSup_eval hE A hA d).2
    (ContFun.directedSupFun hE A hA e) (by
      intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact le_trans (f.continuous.1 hde)
        ((ContFun.directedSupFun_isSup_eval hE A hA e).1 ⟨f, hfA, rfl⟩))

/-- The pointwise directed supremum of continuous maps is Scott-continuous. -/
theorem directedSupFun_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) :
    ScottContinuous (ContFun.directedSupFun hE A hA) := by
  constructor
  · exact ContFun.directedSupFun_monotone hE A hA
  · intro B s hB hs
    constructor
    · intro y hy
      rcases hy with ⟨b, hb, rfl⟩
      exact ContFun.directedSupFun_monotone hE A hA (hs.1 hb)
    · intro y hy
      exact (ContFun.directedSupFun_isSup_eval hE A hA s).2 y (by
        intro z hz
        rcases hz with ⟨f, hfA, rfl⟩
        exact (f.continuous.2 hB hs).2 y (by
          intro fb hfb
          rcases hfb with ⟨b, hb, rfl⟩
          exact le_trans
            ((ContFun.directedSupFun_isSup_eval hE A hA b).1 ⟨f, hfA, rfl⟩)
            (hy ⟨b, hb, rfl⟩)))

/-- Directed supremum in the continuous function space. -/
noncomputable def directedSup
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) :
    ContFun D E where
  toFun := ContFun.directedSupFun hE A hA
  continuous := ContFun.directedSupFun_scottContinuous hE A hA

/-- The constructed pointwise continuous function is the supremum of the
directed family. -/
theorem directedSup_isSup
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) :
    IsSup A (ContFun.directedSup hE A hA) := by
  constructor
  · intro f hfA x
    change f x ≤ ContFun.directedSupFun hE A hA x
    exact (ContFun.directedSupFun_isSup_eval hE A hA x).1 ⟨f, hfA, rfl⟩
  · intro g hg x
    change ContFun.directedSupFun hE A hA x ≤ g x
    exact (ContFun.directedSupFun_isSup_eval hE A hA x).2 (g x) (by
      intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact hg hfA x)

/-- If the codomain is a dcpo, then continuous maps into it form a dcpo under
the pointwise order. -/
theorem isDcpo_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) : IsDcpo (ContFun D E) := by
  intro A hA
  exact ⟨ContFun.directedSup hE A hA, ContFun.directedSup_isSup hE A hA⟩

/-- Extensionality for bundled continuous maps. -/
theorem ext_apply
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {f g : ContFun D E} (h : ∀ x : D, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          have hfun : f = g := funext h
          subst hfun
          congr

/-- Evaluation at a point is Scott-continuous for the pointwise function-space
dcpo. -/
theorem eval_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (d : D) : ScottContinuous (fun f : ContFun D E => f d) := by
  constructor
  · intro f g hfg
    exact hfg d
  · intro A s hA hs
    constructor
    · intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact hs.1 hfA d
    · intro y hy
      have hPointSup : IsSup A (ContFun.directedSup hE A hA) :=
        ContFun.directedSup_isSup hE A hA
      exact le_trans ((hs.2 (ContFun.directedSup hE A hA) hPointSup.1) d)
        ((ContFun.directedSupFun_isSup_eval hE A hA d).2 y hy)

/-- The application map `[D -> E] × D -> E` is Scott-continuous. -/
theorem apply_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) :
    ScottContinuous (ContFun.apply : ContFun D E × D → E) := by
  exact (lemma_3_2_6_continuous_iff_separately_continuous
    (ContFun.apply : ContFun D E × D → E)).2
    ⟨fun f => f.continuous, fun d => ContFun.eval_scottContinuous hE d⟩

/-- Bundled currying from continuous maps on a product into the continuous
function space. -/
def curryBundled
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (f : ContFun (D × E) F) : ContFun D (ContFun E F) where
  toFun := fun d =>
    { toFun := fun e => f (d, e)
      continuous :=
        (lemma_3_2_6_continuous_iff_separately_continuous
          (fun p : D × E => f p)).1 f.continuous |>.1 d }
  continuous := by
    have hsep : SeparatelyScottContinuous (fun p : D × E => f p) :=
      (lemma_3_2_6_continuous_iff_separately_continuous
        (fun p : D × E => f p)).1 f.continuous
    constructor
    · intro d e hde x
      exact f.continuous.1 ⟨hde, le_rfl⟩
    · intro A s hA hs
      constructor
      · intro y hy x
        rcases hy with ⟨d, hdA, rfl⟩
        exact f.continuous.1 ⟨hs.1 hdA, le_rfl⟩
      · intro g hg x
        have hxSup : IsSup ((fun d : D => f (d, x)) '' A) (f (s, x)) :=
          (hsep.2 x).2 hA hs
        exact hxSup.2 (g x) (by
          intro y hy
          rcases hy with ⟨d, hdA, rfl⟩
          exact hg ⟨d, hdA, rfl⟩ x)

/-- Uncurrying from the continuous function space back to maps on the product. -/
def uncurryBundled
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (hF : IsDcpo F) (g : ContFun D (ContFun E F)) : ContFun (D × E) F where
  toFun := fun p => g p.1 p.2
  continuous := by
    exact (lemma_3_2_6_continuous_iff_separately_continuous
      (fun p : D × E => g p.1 p.2)).2
      ⟨fun d => (g d).continuous,
        fun e => (ContFun.eval_scottContinuous hF e).comp g.continuous⟩

/-- Uncurrying is inverse to bundled currying. -/
theorem uncurry_curryBundled
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (hF : IsDcpo F) (f : ContFun (D × E) F) :
    ContFun.uncurryBundled hF (ContFun.curryBundled f) = f := by
  apply ContFun.ext_apply
  intro p
  cases p
  rfl

/-- Bundled currying is inverse to uncurrying. -/
theorem curry_uncurryBundled
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (hF : IsDcpo F) (g : ContFun D (ContFun E F)) :
    ContFun.curryBundled (ContFun.uncurryBundled hF g) = g := by
  apply ContFun.ext_apply
  intro d
  apply ContFun.ext_apply
  intro e
  rfl

/-- The concrete currying order-isomorphism supporting the cartesian-closed
function-space interpretation. -/
def curryOrderIsoData
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (hF : IsDcpo F) : OrderIsoData (ContFun (D × E) F) (ContFun D (ContFun E F)) where
  toFun := ContFun.curryBundled
  invFun := ContFun.uncurryBundled hF
  left_inv := ContFun.uncurry_curryBundled hF
  right_inv := ContFun.curry_uncurryBundled hF
  monotone_to := by
    intro f g hfg d e
    exact hfg (d, e)
  monotone_inv := by
    intro f g hfg p
    exact hfg p.1 p.2

/-- Concrete `DCPO` function-space adjunction supplied by application and
currying. -/
theorem dcpoFunctionSpaceAdjunction :
    DCPOFunctionSpaceAdjunction.{u} := by
  intro C D E _ _ _ _hCdcpo _hCanti _hDdcpo _hDanti hEdcpo _hEanti
  exact ⟨ContFun.curryOrderIsoData hEdcpo⟩

/-- The concrete ordinary continuous function space supplies the internal-hom
comparison for `DCPO`. -/
theorem dcpoInternalHomComparison :
    DCPOInternalHomComparison.{u} := by
  intro D E _ _ _hDdcpo _hDanti hEdcpo hEanti
  refine ⟨ContFun D E, inferInstance, ?_, ?_, ?_⟩
  · exact ContFun.isDcpo_of_codomain hEdcpo
  · exact ContFun.antisymmetric_of_codomain hEanti
  · exact ⟨OrderIsoData.refl (ContFun D E)⟩

/-- Build the current `DCPO` cartesian-closed interface once the remaining
internal-hom comparison is supplied. -/
theorem dcpoCartesianClosed_of_internalHomComparison
    (h : DCPOInternalHomComparison.{u}) : DCPOCartesianClosed.{u} :=
  ⟨ContFun.dcpoFunctionSpaceAdjunction, h⟩

/-- The concrete ordinary continuous function-space carrier makes `DCPO`
cartesian closed in the current interface. -/
theorem dcpoCartesianClosed : DCPOCartesianClosed.{u} :=
  ContFun.dcpoCartesianClosed_of_internalHomComparison
    ContFun.dcpoInternalHomComparison

/-- Concrete `DCPO⊥` function-space adjunction.  Morphisms are ordinary
Scott-continuous maps, so the proof is the same curry/uncurry construction as
for `DCPO`; the pointed object hypotheses are retained in the interface. -/
theorem pointedDCPOFunctionSpaceAdjunction :
    PointedDCPOFunctionSpaceAdjunction.{u} := by
  intro C D E _ _ _ _hCdcpo _hCanti _hCpointed
    _hDdcpo _hDanti _hDpointed hEdcpo _hEanti _hEpointed
  exact ⟨ContFun.curryOrderIsoData hEdcpo⟩

/-- The concrete ordinary continuous function space supplies the pointed
internal-hom comparison for `DCPO⊥`. -/
theorem pointedDCPOInternalHomComparison :
    PointedDCPOInternalHomComparison.{u} := by
  intro D E _ _ _hDdcpo _hDanti _hDpointed hEdcpo hEanti hEpointed
  refine ⟨ContFun D E, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact ContFun.isDcpo_of_codomain hEdcpo
  · exact ContFun.antisymmetric_of_codomain hEanti
  · exact ContFun.hasLeastElement_of_codomain hEpointed
  · exact ⟨OrderIsoData.refl (ContFun D E)⟩

/-- Build the current `DCPO⊥` cartesian-closed interface once the remaining
pointed internal-hom comparison is supplied. -/
theorem pointedDCPOCartesianClosed_of_internalHomComparison
    (h : PointedDCPOInternalHomComparison.{u}) :
    PointedDCPOCartesianClosed.{u} :=
  ⟨ContFun.pointedDCPOFunctionSpaceAdjunction, h⟩

/-- The concrete ordinary continuous function-space carrier makes `DCPO⊥`
cartesian closed in the current interface. -/
theorem pointedDCPOCartesianClosed :
    PointedDCPOCartesianClosed.{u} :=
  ContFun.pointedDCPOCartesianClosed_of_internalHomComparison
    ContFun.pointedDCPOInternalHomComparison

end ContFun

/-- Theorem 3.3.3. PDF text: "DCPO is cartesian closed, complete and
cocomplete."

Current Lean spelling: in the local preorder-based interface, partial-order
dcpos with Scott-continuous morphisms are cartesian closed, complete, and
cocomplete.  Cartesian closedness is witnessed by the ordinary continuous
function-space carrier `ContFun D E`; cocompleteness is the documented external
theorem 3.3.2. -/
theorem theorem_3_3_3_dcpo_cartesian_closed_complete_cocomplete :
    DCPOCartesianClosed.{u} ∧ DCPOHasAllLimits.{u, v, w, z} ∧
      DCPOHasAllColimits.{u, v, w, z} :=
  theorem_3_3_3_dcpo_cartesian_closed_complete_cocomplete_of_cartesianClosed
    ContFun.dcpoCartesianClosed

/-- Theorem 3.3.5. PDF text: "DCPO⊥ is cartesian closed."

Current Lean spelling: in the local preorder-based interface, pointed dcpos
with ordinary Scott-continuous morphisms are cartesian closed.  The exponential
object is represented by the ordinary continuous function-space carrier
`ContFun D E`, with its pointwise dcpo, least element, and antisymmetric order
inherited from the codomain. -/
theorem theorem_3_3_5_pointed_dcpo_cartesian_closed :
    PointedDCPOCartesianClosed.{u} :=
  ContFun.pointedDCPOCartesianClosed

end Chapter3
end AbramskyJung

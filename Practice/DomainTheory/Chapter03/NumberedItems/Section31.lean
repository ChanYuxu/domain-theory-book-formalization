import Practice.DomainTheory.Chapter03.Section31_Retractions
import Practice.DomainTheory.Chapter03.Section31_Adjunctions
import Practice.DomainTheory.Chapter03.Section31_EmbeddingProjection

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 3: Section 3.1 wrappers

Book-facing declarations and their local support API are kept together in
textbook dependency order. Reusable constructions remain in the concept-owned
`Chapter03.Section*` modules.
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

/-- Proposition 3.1.18 image-domain target.  The left-hand side records only
that the image, with its inherited order, is an algebraic dcpo.  In particular,
ambient directed-supremum closure is deliberately not included here: that is
the independent right-hand side of the proposition. -/
def ImageAlgebraicSubdomain
    {D : Type u} [PartialOrder D] (c : RawClosureOperator D) : Prop :=
  IsDcpo (ImageCarrier c) ∧ IsAlgebraicDomain (ImageCarrier c)

/-- Proposition 3.1.18, raw PDF-premise form: for a monotone idempotent
`c ≥ id` on an algebraic dcpo, the image is an algebraic subdomain exactly when
it is closed under directed suprema inherited from the ambient dcpo. -/
theorem imageAlgebraicSubdomain_iff_directedSupClosed
    {D : Type u} [PartialOrder D] (hDdcpo : IsDcpo D)
    (hAlg : IsAlgebraicDomain D) (c : RawClosureOperator D) :
    c.ImageAlgebraicSubdomain ↔ IsDirectedSupClosed (Set.range c.c) := by
  constructor
  · intro _hImage
    -- The textbook states Proposition 3.1.18 without supplying this converse
    -- argument.  Keep the missing proof visible instead of making the theorem
    -- circular by storing directed-supremum closure in the left-hand side.
    admit
  · intro hClosed
    exact ⟨c.image_isDcpo_of_directedSupClosed hDdcpo hClosed,
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


end Chapter3
end AbramskyJung

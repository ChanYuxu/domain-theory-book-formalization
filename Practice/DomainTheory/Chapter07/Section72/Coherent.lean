import Practice.DomainTheory.Chapter07.Section72.LocallyCompact

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.2: coherent spaces and arithmetic lattices

This module follows a coherent dependency cluster inside the textbook section.
The stable public import remains `Practice.DomainTheory.Chapter07.Section72`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

/-- Pointwise infimum of two order filters in a complete lattice.  The source
uses this operation, not set-theoretic intersection, in the proof of
Theorem 7.2.19. -/
def PointwiseInfimumFilter
    {L : Type u} [CompleteLattice L] (F G : Set L) : Set L :=
  {z : L | ∃ x ∈ F, ∃ y ∈ G, x ⊓ y ≤ z}

/-- Arithmeticity implies that the pointwise infimum of two Scott-open order
filters is again a Scott-open order filter. -/
def ScottOpenFiltersClosedUnderPointwiseInfimum
    (L : Type u) [CompleteLattice L] : Prop :=
  ∀ F G : Set L,
    Chapter2.IsFilter F → Chapter2.ScottOpen F →
      Chapter2.IsFilter G → Chapter2.ScottOpen G →
        Chapter2.IsFilter (PointwiseInfimumFilter F G) ∧
          Chapter2.ScottOpen (PointwiseInfimumFilter F G)

/-- An arithmetic lattice object identified with the open-set lattice of a
coherent space.  This records the restricted `Ω` object map in Theorem 7.2.19. -/
structure OpenSetArithmeticLatticeObjectPresentation
    (X : Space.{u}) (L : ArithmeticLatticeObject.{u}) where
  presentation : OpenSetLatticePresentation X
  carrier_equiv : L.carrier ≃ presentation.carrier
  order_agrees :
    ∀ a b : L.carrier,
      @LE.le L.carrier L.lattice.toPreorder.toLE a b ↔
        @LE.le presentation.carrier presentation.lattice.toPreorder.toLE
          (carrier_equiv a) (carrier_equiv b)

/-- Dual-equivalence data for coherent spaces and arithmetic lattices.  It
records both the restricted dual-equivalence data and the proof ingredients from
the PDF: compact-saturated intersections on the coherent-space side and
Scott-open-filter intersection closure on the arithmetic-lattice side. -/
structure CoherentArithmeticDualityData : Type (u + 1) where
  duality : DualEquivalenceData CoherentSpaceObject.{u} ArithmeticLatticeObject.{u}
  left_is_opens :
    ∀ X : CoherentSpaceObject.{u},
      OpenSetArithmeticLatticeObjectPresentation X.space (duality.left X)
  right_is_points :
    ∀ L : ArithmeticLatticeObject.{u},
      @PointSpacePresentation L.carrier L.lattice (duality.right L).space
  space_unit :
    ∀ X : CoherentSpaceObject.{u}, X.space.Point →
      (duality.right (duality.left X)).space.Point
  space_unit_continuous :
    ∀ X : CoherentSpaceObject.{u},
      StoneContinuousMap X.space (duality.right (duality.left X)).space
  space_unit_agrees :
    ∀ X : CoherentSpaceObject.{u}, ∀ x : X.space.Point,
      (space_unit_continuous X).toFun x = space_unit X x
  space_unit_bijective :
    ∀ X : CoherentSpaceObject.{u}, Function.Bijective (space_unit X)
  lattice_unit :
    ∀ L : ArithmeticLatticeObject.{u}, L.carrier →
      (duality.left (duality.right L)).carrier
  lattice_unit_frame_hom :
    ∀ L : ArithmeticLatticeObject.{u},
      @FrameHom L.carrier (duality.left (duality.right L)).carrier
        L.lattice (duality.left (duality.right L)).lattice
  lattice_unit_agrees :
    ∀ L : ArithmeticLatticeObject.{u}, ∀ a : L.carrier,
      (@FrameHom.toFun L.carrier (duality.left (duality.right L)).carrier
        L.lattice (duality.left (duality.right L)).lattice
          (lattice_unit_frame_hom L)) a = lattice_unit L a
  lattice_unit_bijective :
    ∀ L : ArithmeticLatticeObject.{u}, Function.Bijective (lattice_unit L)
  left_preserves_arithmetic :
    ∀ X : CoherentSpaceObject.{u},
      @IsArithmeticLattice (duality.left X).carrier (duality.left X).lattice
  right_preserves_coherent :
    ∀ L : ArithmeticLatticeObject.{u}, IsCoherentSpace (duality.right L).space
  hofmann_mislove_filter_compact_correspondence :
    ∀ L : ArithmeticLatticeObject.{u},
      Nonempty (CompactSaturatedScottOpenFilterDualIso (duality.right L).space)
  coherent_compact_saturated_intersections :
    ∀ X : CoherentSpaceObject.{u},
      CompactSaturatedBinaryIntersectionsCompact X.space
  arithmetic_scott_open_filter_pointwise_infima :
    ∀ L : ArithmeticLatticeObject.{u},
      ScottOpenFiltersClosedUnderPointwiseInfimum L.carrier

/-- A Scott-open set contains a way-below member below each of its points in a
continuous domain. -/
theorem exists_mem_wayBelow_of_scottOpen
    {L : Type u} [Preorder L]
    (hContinuous : Chapter2.IsContinuousDomain L)
    {F : Set L} (hFOpen : Chapter2.ScottOpen F)
    {x : L} (hxF : x ∈ F) :
    ∃ y ∈ F, Chapter2.WayBelow y x := by
  have hSupported :=
    Chapter2.prop_2_3_6_open_supported_by_wayBelow hContinuous hFOpen
  have hxUnion : x ∈ ⋃ y ∈ F, Chapter2.wayBelowUpper y := by
    rw [← hSupported]
    exact hxF
  rw [Set.mem_iUnion] at hxUnion
  rcases hxUnion with ⟨y, hyUnion⟩
  rw [Set.mem_iUnion] at hyUnion
  exact ⟨y, hyUnion.1, hyUnion.2⟩

/-- Pointwise infima preserve the order-filter laws. -/
theorem pointwiseInfimumFilter_isFilter
    {L : Type u} [CompleteLattice L]
    {F G : Set L} (hF : Chapter2.IsFilter F)
    (hG : Chapter2.IsFilter G) :
    Chapter2.IsFilter (PointwiseInfimumFilter F G) := by
  constructor
  · intro z z' hz hzz'
    rcases hz with ⟨x, hxF, y, hyG, hxyz⟩
    exact ⟨x, hxF, y, hyG, hxyz.trans hzz'⟩
  · constructor
    · rcases hF.2.1 with ⟨x, hxF⟩
      rcases hG.2.1 with ⟨y, hyG⟩
      exact ⟨x ⊓ y, x, hxF, y, hyG, le_rfl⟩
    · intro z hz z' hz'
      rcases hz with ⟨x, hxF, y, hyG, hxyz⟩
      rcases hz' with ⟨x', hx'F, y', hy'G, hx'y'z'⟩
      rcases hF.2.2 hxF hx'F with ⟨a, haF, hax, hax'⟩
      rcases hG.2.2 hyG hy'G with ⟨b, hbG, hby, hby'⟩
      refine ⟨a ⊓ b, ⟨a, haF, b, hbG, le_rfl⟩, ?_, ?_⟩
      · exact (inf_le_inf hax hby).trans hxyz
      · exact (inf_le_inf hax' hby').trans hx'y'z'

/-- Multiplicativity of approximation is exactly the extra fact needed for
Scott openness of the pointwise infimum filter. -/
theorem pointwiseInfimumFilter_scottOpen
    {L : Type u} [CompleteLattice L]
    (hContinuous : Chapter2.IsContinuousDomain L)
    (hMultiplicative : MultiplicativeApproximation L)
    {F G : Set L} (hFOpen : Chapter2.ScottOpen F)
    (hGOpen : Chapter2.ScottOpen G) :
    Chapter2.ScottOpen (PointwiseInfimumFilter F G) := by
  constructor
  · intro z z' hz' hzz' hz
    rcases hz with ⟨x, hxF, y, hyG, hxyz⟩
    exact hz' ⟨x, hxF, y, hyG, hxyz.trans hzz'⟩
  · intro A s hA hACompl hs hsPointwise
    rcases hsPointwise with ⟨x, hxF, y, hyG, hxy_s⟩
    rcases exists_mem_wayBelow_of_scottOpen hContinuous hFOpen hxF with
      ⟨x', hx'F, hx'x⟩
    rcases exists_mem_wayBelow_of_scottOpen hContinuous hGOpen hyG with
      ⟨y', hy'G, hy'y⟩
    have hMeetX : x' ⊓ y' ≪ x :=
      Chapter2.prop_2_2_2_2 inf_le_left hx'x le_rfl
    have hMeetY : x' ⊓ y' ≪ y :=
      Chapter2.prop_2_2_2_2 inf_le_right hy'y le_rfl
    have hMeet : x' ⊓ y' ≪ x ⊓ y :=
      hMultiplicative (x' ⊓ y') x y hMeetX hMeetY
    have hMeetS : x' ⊓ y' ≪ s :=
      Chapter2.prop_2_2_2_2 le_rfl hMeet hxy_s
    rcases hMeetS hA hs le_rfl with ⟨a, haA, hMeetA⟩
    exact hACompl haA ⟨x', hx'F, y', hy'G, hMeetA⟩

theorem arithmetic_pointwiseInfimumFilter_closed
    (L : Type u) [CompleteLattice L]
    (hArithmetic : IsArithmeticLattice L) :
    ScottOpenFiltersClosedUnderPointwiseInfimum L := by
  intro F G hF hFOpen hG hGOpen
  exact ⟨pointwiseInfimumFilter_isFilter hF hG,
    pointwiseInfimumFilter_scottOpen hArithmetic.1.2 hArithmetic.2
      hFOpen hGOpen⟩

/-- Basic-open indices whose basic opens contain a fixed compact saturated set. -/
def CompactSaturatedBasicNeighborhoodFilter
    {L : Type u} [CompleteLattice L] (K : Set (Point L)) : Set L :=
  {a : L | K ⊆ pointBasicOpen a}

theorem compactSaturatedBasicNeighborhoodFilter_isFilter
    {L : Type u} [CompleteLattice L] (K : Set (Point L)) :
    Chapter2.IsFilter (CompactSaturatedBasicNeighborhoodFilter K) := by
  constructor
  · intro a b ha hab F hFa
    exact F.2.1.2.1 (ha hFa) hab
  · constructor
    · refine ⟨⊤, ?_⟩
      intro F _hFK
      exact F.2.1.1
    · intro a ha b hb
      refine ⟨a ⊓ b, ?_, inf_le_left, inf_le_right⟩
      intro F hFK
      exact F.2.1.2.2 (ha hFK) (hb hFK)

/-- Compactness makes the basic-neighborhood filter Scott-open. -/
theorem compactSaturatedBasicNeighborhoodFilter_scottOpen
    {L : Type u} [CompleteLattice L]
    {K : Set (Point L)} (hK : IsCompactSaturated (pointSpace L) K) :
    Chapter2.ScottOpen (CompactSaturatedBasicNeighborhoodFilter K) := by
  constructor
  · intro a b hb hab ha
    exact hb (fun F hFK => F.2.1.2.1 (ha hFK) hab)
  · intro A s hA hACompl hs hsNeighborhood
    have hSupEq : sSup A = s := Chapter2.IsSup.unique
      (by
        constructor
        · intro a ha
          exact le_sSup ha
        · intro y hy
          exact sSup_le hy)
      hs
    let cover : Set (Set (Point L)) := pointBasicOpen '' A
    have hCoverOpen : ∀ U ∈ cover, (pointSpace L).IsOpen U := by
      intro U hU
      rcases hU with ⟨a, _haA, rfl⟩
      exact PointOpen.basic a
    have hKCover : K ⊆ ⋃₀ cover := by
      intro F hFK
      have hFs : s ∈ F.1 := hsNeighborhood hFK
      have hFSup : sSup A ∈ F.1 := by simpa [hSupEq] using hFs
      rcases F.2.2 A hFSup with ⟨a, haA, haF⟩
      exact ⟨pointBasicOpen a, ⟨a, haA, rfl⟩, haF⟩
    rcases hK.1 cover hCoverOpen hKCover with
      ⟨finiteCover, hFiniteSub, hFinite, hKFinite⟩
    let chosen : {U : Set (Point L) // U ∈ finiteCover} → L := fun U =>
      Classical.choose (hFiniteSub U.2)
    have hChosenSpec :
        ∀ U : {U : Set (Point L) // U ∈ finiteCover},
          chosen U ∈ A ∧ pointBasicOpen (chosen U) = U.1 := by
      intro U
      exact Classical.choose_spec (hFiniteSub U.2)
    let chosenSet : Set L := Set.range chosen
    letI : Finite {U : Set (Point L) // U ∈ finiteCover} :=
      Set.finite_coe_iff.mpr hFinite
    have hChosenFinite : chosenSet.Finite := Set.finite_range chosen
    have hChosenSub : chosenSet ⊆ A := by
      intro a ha
      rcases ha with ⟨U, rfl⟩
      exact (hChosenSpec U).1
    rcases Chapter2.DirectedSet.exists_upper_finite hA hChosenFinite hChosenSub with
      ⟨a, haA, hUpper⟩
    have haNeighborhood : a ∈ CompactSaturatedBasicNeighborhoodFilter K := by
      intro F hFK
      rcases hKFinite hFK with ⟨U, hUfinite, hFU⟩
      let U' : {U : Set (Point L) // U ∈ finiteCover} := ⟨U, hUfinite⟩
      have hChosenF : chosen U' ∈ F.1 := by
        change F ∈ pointBasicOpen (chosen U')
        rw [(hChosenSpec U').2]
        exact hFU
      exact F.2.1.2.1 hChosenF (hUpper (chosen U') ⟨U', rfl⟩)
    exact hACompl haA haNeighborhood

/-- A compact saturated set is recovered as the points containing its
basic-neighborhood filter. -/
theorem pointsContaining_compactSaturatedBasicNeighborhoodFilter
    {L : Type u} [CompleteLattice L]
    {K : Set (Point L)} (hK : IsCompactSaturated (pointSpace L) K) :
    {F : Point L | CompactSaturatedBasicNeighborhoodFilter K ⊆ F.1} = K := by
  apply Set.Subset.antisymm
  · intro F hF
    have hAllNeighborhoods : F ∈ ⋂₀ OpenNeighborhoodsOf (pointSpace L) K := by
      intro U hU
      rcases epsilon_surjective L U hU.1 with ⟨a, hUa⟩
      have haNeighborhood : a ∈ CompactSaturatedBasicNeighborhoodFilter K := by
        intro G hGK
        change G ∈ EpsilonMap a
        rw [← hUa]
        exact hU.2 hGK
      rw [hUa]
      exact hF haNeighborhood
    rw [saturated_eq_sInter_openNeighborhoods hK.2] at hAllNeighborhoods
    exact hAllNeighborhoods
  · intro F hFK a haNeighborhood
    exact haNeighborhood hFK

/-- Points containing a pointwise-infimum filter are exactly the intersection
of the point sets determined by its two factors. -/
theorem pointsContaining_pointwiseInfimumFilter
    {L : Type u} [CompleteLattice L]
    {F G : Set L} (hF : Chapter2.IsFilter F)
    (hG : Chapter2.IsFilter G) :
    {P : Point L | PointwiseInfimumFilter F G ⊆ P.1} =
      {P : Point L | F ⊆ P.1} ∩ {P : Point L | G ⊆ P.1} := by
  ext P
  constructor
  · intro hP
    rcases hG.2.1 with ⟨topG, htopG⟩
    rcases hF.2.1 with ⟨topF, htopF⟩
    have hTopG : (⊤ : L) ∈ G := hG.1 htopG le_top
    have hTopF : (⊤ : L) ∈ F := hF.1 htopF le_top
    constructor
    · intro x hxF
      exact hP ⟨x, hxF, ⊤, hTopG, by simp⟩
    · intro y hyG
      exact hP ⟨⊤, hTopF, y, hyG, by simp⟩
  · intro hP z hz
    rcases hz with ⟨x, hxF, y, hyG, hxyz⟩
    exact P.2.1.2.1 (P.2.1.2.2 (hP.1 hxF) (hP.2 hyG)) hxyz

/-- The point space of an arithmetic lattice is coherent. -/
theorem pointSpace_coherent_of_arithmetic
    (L : Type u) [CompleteLattice L]
    (hArithmetic : IsArithmeticLattice L) :
    IsCoherentSpace (pointSpace L) := by
  have hContinuous := hArithmetic.1.2
  have hDistributive := hArithmetic.1.1
  refine ⟨(theorem_7_2_7_points_sober_opens_spatial
    L (pointSpace L)).1,
    pointSpace_locallyCompact_of_distributiveContinuous
      L hContinuous hDistributive, ?_⟩
  intro K M hK hM
  let F : Set L := CompactSaturatedBasicNeighborhoodFilter K
  let G : Set L := CompactSaturatedBasicNeighborhoodFilter M
  let H : Set L := PointwiseInfimumFilter F G
  have hFFilter : Chapter2.IsFilter F :=
    compactSaturatedBasicNeighborhoodFilter_isFilter K
  have hGFilter : Chapter2.IsFilter G :=
    compactSaturatedBasicNeighborhoodFilter_isFilter M
  have hFOpen : Chapter2.ScottOpen F :=
    compactSaturatedBasicNeighborhoodFilter_scottOpen hK
  have hGOpen : Chapter2.ScottOpen G :=
    compactSaturatedBasicNeighborhoodFilter_scottOpen hM
  have hHFilter : Chapter2.IsFilter H :=
    pointwiseInfimumFilter_isFilter hFFilter hGFilter
  have hHOpen : Chapter2.ScottOpen H :=
    pointwiseInfimumFilter_scottOpen hContinuous hArithmetic.2 hFOpen hGOpen
  have hSpatial : IsSpatialLattice L :=
    lemma_7_2_15_distributive_continuous_lattices_spatial
      L hContinuous hDistributive
  have hHCompact :
      IsCompactSaturated (pointSpace L) {P : Point L | H ⊆ P.1} :=
    pointsContainingFilter_compactSaturated hSpatial hHOpen hHFilter
  have hEq : {P : Point L | H ⊆ P.1} = K ∩ M := by
    calc
      {P : Point L | H ⊆ P.1} =
          {P : Point L | F ⊆ P.1} ∩ {P : Point L | G ⊆ P.1} :=
        pointsContaining_pointwiseInfimumFilter hFFilter hGFilter
      _ = K ∩ M := by
        rw [pointsContaining_compactSaturatedBasicNeighborhoodFilter hK,
          pointsContaining_compactSaturatedBasicNeighborhoodFilter hM]
        rfl
  exact hEq ▸ hHCompact.1

/-- Coherence makes approximation in the open-set lattice multiplicative. -/
theorem openSet_multiplicativeApproximation_of_coherent
    (X : Space.{u}) (hX : IsCoherentSpace X) :
    MultiplicativeApproximation (OpenSet X) := by
  intro O U V hOU hOV
  let AU : Set (OpenSet X) := {W | CompactBetweenOpenSets X W U}
  let AV : Set (OpenSet X) := {W | CompactBetweenOpenSets X W V}
  rcases hOU (compactBetweenOpenSets_directed X U)
      (compactBetweenOpenSets_isSup X hX.2.1 U) le_rfl with
    ⟨WU, hWU, hOWU⟩
  rcases hOV (compactBetweenOpenSets_directed X V)
      (compactBetweenOpenSets_isSup X hX.2.1 V) le_rfl with
    ⟨WV, hWV, hOWV⟩
  rcases hWU with ⟨K, hK, hWUK, hKU⟩
  rcases hWV with ⟨M, hM, hWVM, hMV⟩
  have hKM : IsCompactSaturated X (K ∩ M) :=
    coherent_compactSaturated_inter hX hK hM
  apply compactBetweenImpliesWayBelowOpens X
  refine ⟨K ∩ M, hKM, ?_, ?_⟩
  · intro x hxO
    exact ⟨hWUK (hOWU hxO), hWVM (hOWV hxO)⟩
  · intro x hx
    rw [OpenSet.inf_eq_inter X U V]
    exact ⟨hKU hx.1, hMV hx.2⟩

/-- The restricted open-set object map for coherent spaces. -/
def coherentArithmeticLeft (X : CoherentSpaceObject.{u}) :
    ArithmeticLatticeObject.{u} where
  carrier := OpenSet X.space
  lattice := OpenSet.completeLattice X.space
  arithmetic := ⟨⟨openSet_frameDistributive X.space,
    openSet_continuous_of_locallyCompact X.space X.coherent.2.1⟩,
    openSet_multiplicativeApproximation_of_coherent X.space X.coherent⟩

/-- The restricted point-space object map for arithmetic lattices. -/
def arithmeticPointRight (L : ArithmeticLatticeObject.{u}) :
    CoherentSpaceObject.{u} where
  space := pointSpace L.carrier
  coherent := pointSpace_coherent_of_arithmetic L.carrier L.arithmetic

/-- Theorem 7.2.19 PDF-facing statement. -/
theorem theorem_7_2_19_coherent_arithmetic_duality :
    Nonempty (CoherentArithmeticDualityData.{u}) := by
  refine ⟨{
    duality := {
      left := coherentArithmeticLeft
      right := arithmeticPointRight
      unit_isomorphism :=
        ∀ X : CoherentSpaceObject.{u},
          Function.Bijective (stoneUnitPoint X.space)
      unit_isomorphism_holds := fun X =>
        stoneUnitPoint_bijective_of_sober X.space X.coherent.1
      counit_isomorphism :=
        ∀ L : ArithmeticLatticeObject.{u},
          Function.Bijective
            (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun
      counit_isomorphism_holds := fun L =>
        stoneEpsilon_bijective_of_distributiveContinuous {
          carrier := L.carrier
          lattice := L.lattice
          continuous := L.arithmetic.1.2
          distributive := L.arithmetic.1.1 } }
    left_is_opens := ?_
    right_is_points := ?_
    space_unit := fun X => stoneUnitPoint X.space
    space_unit_continuous := fun X => stoneUnitContinuous X.space
    space_unit_agrees := ?_
    space_unit_bijective := fun X =>
      stoneUnitPoint_bijective_of_sober X.space X.coherent.1
    lattice_unit := fun L =>
      (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun
    lattice_unit_frame_hom := fun L =>
      stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})
    lattice_unit_agrees := ?_
    lattice_unit_bijective := ?_
    left_preserves_arithmetic := ?_
    right_preserves_coherent := ?_
    hofmann_mislove_filter_compact_correspondence := ?_
    coherent_compact_saturated_intersections := ?_
    arithmetic_scott_open_filter_pointwise_infima := ?_ }⟩
  · intro X
    exact {
      presentation := {
        carrier := OpenSet X.space
        lattice := OpenSet.completeLattice X.space
        toOpen := fun U => U
        ofOpen := fun U => U
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        order_compatible := fun _ _ => Iff.rfl }
      carrier_equiv := Equiv.refl _
      order_agrees := fun _ _ => Iff.rfl }
  · intro L
    exact {
      point_equiv := Equiv.refl _
      open_agrees := by
        intro U
        change PointOpen L.carrier U ↔ PointOpen L.carrier U
        exact Iff.rfl }
  · intro X x
    rfl
  · intro L a
    rfl
  · intro L
    exact stoneEpsilon_bijective_of_distributiveContinuous {
      carrier := L.carrier
      lattice := L.lattice
      continuous := L.arithmetic.1.2
      distributive := L.arithmetic.1.1 }
  · intro X
    exact (coherentArithmeticLeft X).arithmetic
  · intro L
    exact pointSpace_coherent_of_arithmetic L.carrier L.arithmetic
  · intro L
    exact cor_7_2_10_compact_saturated_filters_dual
      (pointSpace L.carrier)
      (theorem_7_2_7_points_sober_opens_spatial
        L.carrier (pointSpace L.carrier)).1
  · intro X
    exact X.coherent.2.2
  · intro L
    exact arithmetic_pointwiseInfimumFilter_closed L.carrier L.arithmetic


end Chapter7
end AbramskyJung

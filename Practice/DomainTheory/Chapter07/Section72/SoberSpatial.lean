import Practice.DomainTheory.Chapter07.Section72.Core

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.2: sober-spatial equivalence and Hofmann-Mislove

This module follows a coherent dependency cluster inside the textbook section.
The stable public import remains `Practice.DomainTheory.Chapter07.Section72`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

/-- Proposition 7.2.2: the sober unit detects `T0` and generic irreducible closed sets. -/
theorem prop_7_2_2_sober_unit_characterization (X : Space.{u}) :
    (SoberUnitInjective X ↔ IsT0Space X) ∧
      (SoberUnitSurjective X ↔ EveryIrreducibleClosedHasGenericPoint X) := by
  exact
    ⟨stoneUnitPoint_injective_iff_t0 X,
      stoneUnitPoint_surjective_iff_generic_points X⟩

/-- Proposition 7.2.4 PDF-facing statement.  The equivalence chain beyond the
direct monotonicity/surjectivity clauses is proof debt from the book. -/
theorem prop_7_2_4_lattice_unit_spatiality
    (L : Type u) [CompleteLattice L] :
    EpsilonSurjective L ∧ Monotone (EpsilonMap : L → Set (Point L)) ∧
      (EpsilonInjective L ↔ CompletelyPrimeFiltersSeparate L) ∧
        (CompletelyPrimeFiltersSeparate L ↔
          MeetGeneratedBy ({x : L | IsFiniteMeetPrime x})) ∧
          (MeetGeneratedBy ({x : L | IsFiniteMeetPrime x}) ↔
            CompletelyPrimeFiltersOrderSeparate L) ∧
            (CompletelyPrimeFiltersOrderSeparate L ↔ EpsilonOrderReflecting L) ∧
              (EpsilonOrderReflecting L ↔ EpsilonInjective L) := by
  have hMeetGeneration :
      (CompletelyPrimeFiltersSeparate L ↔
        MeetGeneratedBy ({x : L | IsFiniteMeetPrime x})) ∧
        (MeetGeneratedBy ({x : L | IsFiniteMeetPrime x}) ↔
          CompletelyPrimeFiltersOrderSeparate L) := by
    have hSepOrder :
        CompletelyPrimeFiltersSeparate L ↔ CompletelyPrimeFiltersOrderSeparate L := by
      calc
        CompletelyPrimeFiltersSeparate L ↔ EpsilonInjective L :=
          (epsilon_injective_iff_filter_separate L).symm
        _ ↔ EpsilonOrderReflecting L :=
          (epsilon_order_reflecting_iff_injective L).symm
        _ ↔ CompletelyPrimeFiltersOrderSeparate L :=
          (order_separate_iff_epsilon_reflecting L).symm
    have hGeneratedOrder :
        MeetGeneratedBy ({x : L | IsFiniteMeetPrime x}) ↔
          CompletelyPrimeFiltersOrderSeparate L :=
      meetGenerated_finiteMeetPrime_iff_orderSeparate L
    exact ⟨hSepOrder.trans hGeneratedOrder.symm, hGeneratedOrder⟩
  exact
    ⟨epsilon_surjective L, epsilon_monotone L,
      epsilon_injective_iff_filter_separate L,
      hMeetGeneration.1,
      hMeetGeneration.2,
      order_separate_iff_epsilon_reflecting L,
      epsilon_order_reflecting_iff_injective L⟩

/-- Theorem 7.2.6 PDF-facing statement. -/
theorem theorem_7_2_6_spatial_lattice_frame
    (L : Type u) [CompleteLattice L] :
    IsSpatialLattice L → IsFrameDistributive L := by
  intro hSpatial x S
  refine hSpatial.1 (x ⊓ sSup S) (sSup ((fun y : L => x ⊓ y) '' S)) ?_
  ext F
  constructor
  · intro hMeetSup
    have hx : x ∈ F.1 := F.2.1.2.1 hMeetSup inf_le_left
    have hSup : sSup S ∈ F.1 := F.2.1.2.1 hMeetSup inf_le_right
    rcases F.2.2 S hSup with ⟨s, hsS, hsF⟩
    have hMeet : x ⊓ s ∈ F.1 := F.2.1.2.2 hx hsF
    exact F.2.1.2.1 hMeet (le_sSup (Set.mem_image_of_mem (fun y : L => x ⊓ y) hsS))
  · intro hSup
    rcases F.2.2 ((fun y : L => x ⊓ y) '' S) hSup with ⟨z, hzImage, hzF⟩
    rcases hzImage with ⟨s, hsS, rfl⟩
    exact F.2.1.2.1 hzF (inf_le_inf_left x (le_sSup hsS))

/-- Theorem 7.2.7 PDF-facing statement. -/
theorem theorem_7_2_7_points_sober_opens_spatial
    (L : Type u) [CompleteLattice L] (X : Space.{u}) :
    IsSober (pointSpace L) ∧ OpenSetLatticeSpatial X := by
  exact
    ⟨⟨pointSpace_t0 L, pointSpace_irreducible_closed_has_generic_point L⟩,
      openSetLatticeSpatial X⟩

/-- The open-set object of a sober space, restricted to spatial lattices. -/
def soberSpatialLeft (X : SoberSpaceObject.{u}) : SpatialLatticeObject.{u} where
  carrier := OpenSet X.space
  lattice := OpenSet.completeLattice X.space
  spatial := ⟨openSet_epsilon_injective X.space, epsilon_surjective (OpenSet X.space)⟩

/-- The point-space object of a spatial lattice, restricted to sober spaces. -/
def soberSpatialRight (L : SpatialLatticeObject.{u}) : SoberSpaceObject.{u} where
  space := @pointSpace L.carrier L.lattice
  sober := ⟨pointSpace_t0 L.carrier,
    pointSpace_irreducible_closed_has_generic_point L.carrier⟩

/-- Spatiality is precisely what makes the lattice-side Stone unit bijective. -/
theorem stoneEpsilon_bijective_of_spatial (L : SpatialLatticeObject.{u}) :
    Function.Bijective
      (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun := by
  constructor
  · intro a b hab
    apply L.spatial.1 a b
    exact congrArg Subtype.val hab
  · intro U
    rcases L.spatial.2 U.1 U.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha.symm

/-- Concrete data for the dual equivalence between sober spaces and spatial
complete lattices.  It augments the high-level duality package with explicit
space-side and lattice-side unit maps and bijectivity/frame-homomorphism data. -/
structure SoberSpatialDualEquivalenceData : Type (u + 1) where
  duality : DualEquivalenceData SoberSpaceObject.{u} SpatialLatticeObject.{u}
  left_is_opens :
    ∀ X : SoberSpaceObject.{u},
      OpenSetLatticeObjectPresentation X.space (duality.left X)
  right_is_points :
    ∀ L : SpatialLatticeObject.{u},
      @PointSpacePresentation L.carrier L.lattice (duality.right L).space
  space_unit :
    ∀ X : SoberSpaceObject.{u}, X.space.Point →
      (duality.right (duality.left X)).space.Point
  space_unit_continuous :
    ∀ X : SoberSpaceObject.{u},
      StoneContinuousMap X.space (duality.right (duality.left X)).space
  space_unit_agrees :
    ∀ X : SoberSpaceObject.{u}, ∀ x : X.space.Point,
      (space_unit_continuous X).toFun x = space_unit X x
  space_unit_bijective :
    ∀ X : SoberSpaceObject.{u}, Function.Bijective (space_unit X)
  lattice_unit :
    ∀ L : SpatialLatticeObject.{u}, L.carrier →
      (duality.left (duality.right L)).carrier
  lattice_unit_frame_hom :
    ∀ L : SpatialLatticeObject.{u},
      @FrameHom L.carrier (duality.left (duality.right L)).carrier
        L.lattice (duality.left (duality.right L)).lattice
  lattice_unit_agrees :
    ∀ L : SpatialLatticeObject.{u}, ∀ a : L.carrier,
      (@FrameHom.toFun L.carrier (duality.left (duality.right L)).carrier
        L.lattice (duality.left (duality.right L)).lattice
          (lattice_unit_frame_hom L)) a = lattice_unit L a
  lattice_unit_bijective :
    ∀ L : SpatialLatticeObject.{u}, Function.Bijective (lattice_unit L)
  left_preserves_spatial :
    ∀ X : SoberSpaceObject.{u},
      @IsSpatialLattice (duality.left X).carrier (duality.left X).lattice
  right_preserves_sober :
    ∀ L : SpatialLatticeObject.{u}, IsSober (duality.right L).space

/-- Corollary 7.2.8 PDF-facing statement. -/
theorem cor_7_2_8_sober_spatial_dual_equivalence :
    Nonempty (SoberSpatialDualEquivalenceData.{u}) := by
  refine ⟨{
    duality := {
      left := soberSpatialLeft
      right := soberSpatialRight
      unit_isomorphism :=
        ∀ X : SoberSpaceObject.{u}, Function.Bijective (stoneUnitPoint X.space)
      unit_isomorphism_holds := fun X => stoneUnitPoint_bijective_of_sober X.space X.sober
      counit_isomorphism :=
        ∀ L : SpatialLatticeObject.{u},
          Function.Bijective
            (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun
      counit_isomorphism_holds := stoneEpsilon_bijective_of_spatial }
    left_is_opens := ?_
    right_is_points := ?_
    space_unit := fun X => stoneUnitPoint X.space
    space_unit_continuous := fun X => stoneUnitContinuous X.space
    space_unit_agrees := ?_
    space_unit_bijective := fun X => stoneUnitPoint_bijective_of_sober X.space X.sober
    lattice_unit := fun L =>
      (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun
    lattice_unit_frame_hom := fun L =>
      stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})
    lattice_unit_agrees := ?_
    lattice_unit_bijective := stoneEpsilon_bijective_of_spatial
    left_preserves_spatial := fun X => (soberSpatialLeft X).spatial
    right_preserves_sober := fun L => (soberSpatialRight L).sober }⟩
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
      open_agrees := fun _ => Iff.rfl }
  · intro X x
    rfl
  · intro L a
    rfl

/-- Corollary 7.2.10 data: compact saturated sets ordered by inclusion are
dually isomorphic to Scott-open filters of opens, also ordered by inclusion. -/
structure CompactSaturatedScottOpenFilterDualIso (X : Space.{u}) where
  toFilter :
    {K : Set X.Point // IsCompactSaturated X K} →
      {F : Set (Set X.Point) // IsScottOpenFilterOfOpens X F}
  toCompactSaturated :
    {F : Set (Set X.Point) // IsScottOpenFilterOfOpens X F} →
      {K : Set X.Point // IsCompactSaturated X K}
  neighborhood_filter :
    ∀ K : {K : Set X.Point // IsCompactSaturated X K},
      (toFilter K).1 = OpenNeighborhoodsOf X K.1
  left_inverse :
    ∀ K : {K : Set X.Point // IsCompactSaturated X K},
      toCompactSaturated (toFilter K) = K
  right_inverse :
    ∀ F : {F : Set (Set X.Point) // IsScottOpenFilterOfOpens X F},
      toFilter (toCompactSaturated F) = F
  inverse_is_intersection :
    ∀ F : {F : Set (Set X.Point) // IsScottOpenFilterOfOpens X F},
      (toCompactSaturated F).1 = ⋂₀ F.1
  order_dual :
    ∀ K L : {K : Set X.Point // IsCompactSaturated X K},
      K.1 ⊆ L.1 ↔ (toFilter L).1 ⊆ (toFilter K).1

/-- Theorem 7.2.9 data: Hofmann-Mislove represents Scott-open filters of
opens as neighborhood filters of compact saturated sets, with the canonical
choice `K = ⋂₀ F` from the proof. -/
structure HofmannMisloveRepresentation (X : Space.{u}) : Prop where
  neighborhoods_iff :
    ∀ F : Set (Set X.Point),
      IsScottOpenFilterOfOpens X F ↔
        ∃ K : Set X.Point, IsCompactSaturated X K ∧ F = OpenNeighborhoodsOf X K
  intersection_candidate :
    ∀ F : Set (Set X.Point),
      IsScottOpenFilterOfOpens X F →
        IsCompactSaturated X (⋂₀ F) ∧ F = OpenNeighborhoodsOf X (⋂₀ F)

/-- Theorem 7.2.9 PDF-facing statement. -/
theorem theorem_7_2_9_hofmann_mislove_sober
    (X : Space.{u}) :
    IsSober X → HofmannMisloveRepresentation X := by
  intro hX
  have hMaxExtension :
      ∀ F : Set (Set X.Point), IsScottOpenFilterOfOpens X F →
        ∀ O : Set X.Point, X.IsOpen O → O ∉ F →
          ∃ M : Set X.Point, O ⊆ M ∧ MaximalOpenOutsideFilter X F M := by
    intro F hF O hOOpen hOOutside
    exact maximalOpenOutsideFilter_extension hF hOOpen hOOutside
  refine
    { neighborhoods_iff := ?_
      intersection_candidate := ?_ }
  · intro F
    constructor
    · intro hF
      have hCandidate :
          IsCompactSaturated X (⋂₀ F) ∧
            F = OpenNeighborhoodsOf X (⋂₀ F) :=
        hofmannMislove_candidate_representation_of_maximal_extension hX hF
          (hMaxExtension F hF)
      exact ⟨⋂₀ F, hCandidate.1, hCandidate.2⟩
    · intro hNeighborhoods
      rcases hNeighborhoods with ⟨K, hK, rfl⟩
      exact openNeighborhoods_scottOpenFilter hK
  · intro F hF
    exact hofmannMislove_candidate_representation_of_maximal_extension hX hF
      (hMaxExtension F hF)

/-- Corollary 7.2.11 support: Hofmann--Mislove applied to the Scott-open filter
generated by a filtered compact-saturated family gives compactness and open
reflection for the filtered intersection. -/
theorem filteredCompactSaturatedIntersectionResult_of_hofmannMislove
    (X : Space.{u}) {𝒦 : Set (Set X.Point)}
    (hRep : HofmannMisloveRepresentation X)
    (hFiltered : IsFilteredFamily 𝒦)
    (hCompact : ∀ K ∈ 𝒦, IsCompactSaturated X K) :
    FilteredCompactSaturatedIntersectionResult X 𝒦 := by
  let F : Set (Set X.Point) := FilteredOpenNeighborhoodsOf X 𝒦
  have hF : IsScottOpenFilterOfOpens X F :=
    filteredOpenNeighborhoods_scottOpenFilter X hFiltered hCompact
  have hCandidate := hRep.intersection_candidate F hF
  have hEq : ⋂₀ F = ⋂₀ 𝒦 :=
    sInter_filteredOpenNeighborhoods_eq_sInter X hCompact
  have hOpenReflection :
      ∀ O : Set X.Point, X.IsOpen O → (⋂₀ 𝒦) ⊆ O → ∃ K ∈ 𝒦, K ⊆ O := by
    intro O hO hSub
    have hFO : (⋂₀ F) ⊆ O := by
      intro x hx
      exact hSub (by simpa [hEq] using hx)
    have hONeighborhood : O ∈ OpenNeighborhoodsOf X (⋂₀ F) := ⟨hO, hFO⟩
    have hOF : O ∈ F := by
      rw [hCandidate.2]
      exact hONeighborhood
    rcases (show O ∈ FilteredOpenNeighborhoodsOf X 𝒦 from hOF) with
      ⟨_hO, K, hK, hKO⟩
    exact ⟨K, hK, hKO⟩
  refine
    { compact_intersection := ?_
      saturated_intersection := ?_
      nonempty_intersection := ?_
      open_reflection := hOpenReflection }
  · simpa [hEq] using hCandidate.1.1
  · simpa [hEq] using hCandidate.1.2
  · intro hMembers
    by_contra hEmpty
    have hSubEmpty : (⋂₀ 𝒦) ⊆ (∅ : Set X.Point) := by
      intro x hx
      exact False.elim (hEmpty ⟨x, hx⟩)
    rcases hOpenReflection ∅ (Space.empty_open X) hSubEmpty with
      ⟨K, hK, hKempty⟩
    rcases hMembers K hK with ⟨x, hxK⟩
    exact hKempty hxK

/-- Corollary 7.2.10 support: Hofmann--Mislove representation data yields the
dual isomorphism between compact saturated subsets and Scott-open filters of
opens. -/
def compactSaturatedScottOpenFilterDualIso_of_hofmannMislove
    (X : Space.{u}) (hRep : HofmannMisloveRepresentation X) :
    CompactSaturatedScottOpenFilterDualIso X where
  toFilter := fun K =>
    ⟨OpenNeighborhoodsOf X K.1,
      openNeighborhoods_scottOpenFilter K.2⟩
  toCompactSaturated := fun F =>
    ⟨⋂₀ F.1, (hRep.intersection_candidate F.1 F.2).1⟩
  neighborhood_filter := by
    intro K
    rfl
  left_inverse := by
    intro K
    apply Subtype.ext
    exact saturated_eq_sInter_openNeighborhoods K.2.2
  right_inverse := by
    intro F
    apply Subtype.ext
    exact (hRep.intersection_candidate F.1 F.2).2.symm
  inverse_is_intersection := by
    intro F
    rfl
  order_dual := by
    intro K L
    constructor
    · intro hKL U hU
      exact ⟨hU.1, fun x hxK => hU.2 (hKL hxK)⟩
    · intro hNeighborhoods x hxK
      have hxInter : x ∈ ⋂₀ OpenNeighborhoodsOf X L.1 := by
        intro U hU
        exact (hNeighborhoods hU).2 hxK
      have hEq : ⋂₀ OpenNeighborhoodsOf X L.1 = L.1 :=
        saturated_eq_sInter_openNeighborhoods L.2.2
      exact hEq ▸ hxInter

/-- Corollary 7.2.10 PDF-facing statement. -/
theorem cor_7_2_10_compact_saturated_filters_dual
    (X : Space.{u}) :
    IsSober X →
      Nonempty (CompactSaturatedScottOpenFilterDualIso X) := by
  intro hX
  exact
    ⟨compactSaturatedScottOpenFilterDualIso_of_hofmannMislove X
      (theorem_7_2_9_hofmann_mislove_sober X hX)⟩

/-- Corollary 7.2.11 PDF-facing statement. -/
theorem cor_7_2_11_filtered_intersections_compact_saturated
    (X : Space.{u}) (𝒦 : Set (Set X.Point)) :
    IsSober X → IsFilteredFamily 𝒦 →
      (∀ K ∈ 𝒦, IsCompactSaturated X K) →
        FilteredCompactSaturatedIntersectionResult X 𝒦 := by
  intro hX hFiltered hCompact
  exact
    filteredCompactSaturatedIntersectionResult_of_hofmannMislove X
      (theorem_7_2_9_hofmann_mislove_sober X hX) hFiltered hCompact

/-- Proposition 7.2.12: a `T0` topology refines the weak upper topology. -/
theorem prop_7_2_12_t0_weak_upper_topology (X : Space.{u}) :
    IsT0Space X → TopologyFinerThanWeakUpper X := by
  classical
  intro _hT0 x
  let S : Set (Set X.Point) :=
    {U | X.IsOpen U ∧ U ⊆ {y : X.Point | ¬ SpecializationLE X y x}}
  have hOpen : X.IsOpen (⋃₀ S) := by
    exact X.sUnion_open S (by
      intro U hU
      exact hU.1)
  have hEq : ⋃₀ S = {y : X.Point | ¬ SpecializationLE X y x} := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨U, hUS, hyU⟩
      exact hUS.2 hyU
    · intro hy
      simp only [Set.mem_setOf_eq] at hy
      rw [SpecializationLE] at hy
      rcases not_forall.mp hy with ⟨U, hU⟩
      have hUParts : X.IsOpen U ∧ ¬(y ∈ U → x ∈ U) := Classical.not_imp.mp hU
      rcases hUParts with ⟨hUOpen, hRest⟩
      have hRestParts : y ∈ U ∧ x ∉ U := Classical.not_imp.mp hRest
      rcases hRestParts with ⟨hyU, hxU⟩
      refine ⟨U, ?_, hyU⟩
      constructor
      · exact hUOpen
      · intro z hzU hzspec
        exact hxU (hzspec U hUOpen hzU)
  simpa [hEq] using hOpen


end Chapter7
end AbramskyJung

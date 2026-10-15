import Practice.DomainTheory.Chapter07.Section72.Coherent

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.2: algebraic distributive duality

This module follows a coherent dependency cluster inside the textbook section.
The stable public import remains `Practice.DomainTheory.Chapter07.Section72`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

/-- A compact-open neighborhood basis is, in particular, a local-compactness
basis by taking the compact neighborhood and its open core to be the same set. -/
theorem locallyCompact_of_compactOpenNeighborhoodBasis
    (X : Space.{u}) (hBasis : HasCompactOpenNeighborhoodBasis X) :
    IsLocallyCompact X := by
  intro x U hUOpen hxU
  rcases hBasis x U hUOpen hxU with ⟨V, hV, hxV, hVU⟩
  exact ⟨V, V, compactOpen_isCompactSaturated hV, hV.1, hxV,
    Set.Subset.rfl, hVU⟩

/-- Compact-open subsets are compact elements of the lattice of opens. -/
theorem compactOpen_isCompactOpenSetElement
    {X : Space.{u}} {U : Set X.Point} (hU : IsCompactOpenSubset X U) :
    Chapter2.Compact (⟨U, hU.1⟩ : OpenSet X) := by
  exact compactBetweenImpliesWayBelowOpens X ⟨U, hU.1⟩ ⟨U, hU.1⟩
    ⟨U, compactOpen_isCompactSaturated hU, Set.Subset.rfl, Set.Subset.rfl⟩

/-- If compact-open neighborhoods form a basis, the complete lattice of opens
is algebraic, with its compact-open elements as a concrete compact basis. -/
theorem openSet_algebraic_of_compactOpenNeighborhoodBasis
    (X : Space.{u}) (hBasis : HasCompactOpenNeighborhoodBasis X) :
    Chapter2.IsAlgebraicDomain (OpenSet X) := by
  intro O
  let A : Set (OpenSet X) :=
    {V : OpenSet X | IsCompactOpenSubset X V.1 ∧ V.1 ⊆ O.1}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro V hV
    exact ⟨compactOpen_isCompactOpenSetElement hV.1,
      Chapter2.prop_2_2_2_2 le_rfl
        (compactOpen_isCompactOpenSetElement hV.1) hV.2⟩
  · constructor
    · let E : OpenSet X := ⟨∅, Space.empty_open X⟩
      refine ⟨E, ?_⟩
      exact ⟨⟨Space.empty_open X, compactSubset_empty X⟩, Set.empty_subset O.1⟩
    · intro U hU V hV
      let W : OpenSet X := ⟨U.1 ∪ V.1, X.union_open U.2 V.2⟩
      refine ⟨W, ?_, ?_, ?_⟩
      · exact ⟨⟨X.union_open U.2 V.2,
          compactSubset_union hU.1.2 hV.1.2⟩,
          fun x hx => hx.elim (fun hxU => hU.2 hxU) (fun hxV => hV.2 hxV)⟩
      · intro x hx
        exact Or.inl hx
      · intro x hx
        exact Or.inr hx
  · constructor
    · intro V hV
      exact hV.2
    · intro Y hUpper x hxO
      rcases hBasis x O.1 O.2 hxO with ⟨V, hV, hxV, hVO⟩
      let V' : OpenSet X := ⟨V, hV.1⟩
      exact (hUpper (a := V') ⟨hV, hVO⟩) hxV

/-- Algebraicity supplies continuity by choosing the compact basis itself. -/
theorem continuous_of_algebraic
    {L : Type u} [Preorder L]
    (hAlgebraic : Chapter2.IsAlgebraicDomain L) :
    Chapter2.IsContinuousDomain L :=
  ⟨Chapter2.CompactSet, hAlgebraic⟩

/-- Every member of a completely prime filter on an algebraic lattice lies
above a compact member of that filter. -/
theorem exists_compact_mem_below_of_algebraic_point
    {L : Type u} [CompleteLattice L]
    (hAlgebraic : Chapter2.IsAlgebraicDomain L)
    (F : Point L) {x : L} (hxF : x ∈ F.1) :
    ∃ k : L, Chapter2.Compact k ∧ k ∈ F.1 ∧ k ≤ x := by
  have hBasis := Chapter2.prop_2_2_4_1 hAlgebraic x
  have hSupEq :
      sSup (Chapter2.Approximants Chapter2.CompactSet x) = x :=
    Chapter2.IsSup.unique
      (by
        constructor
        · intro y hy
          exact le_sSup hy
        · intro y hy
          exact sSup_le hy)
      hBasis.2
  have hJoinF : sSup (Chapter2.Approximants Chapter2.CompactSet x) ∈ F.1 := by
    simpa [hSupEq] using hxF
  rcases F.2.2 _ hJoinF with ⟨k, hkApprox, hkF⟩
  exact ⟨k, hkApprox.1, hkF, Chapter2.prop_2_2_2_1 hkApprox.2⟩

/-- A compact lattice element determines a compact basic open in the point
space.  This is the basis-level compactness argument used in Theorem 7.2.20. -/
theorem pointBasicOpen_compact_of_compact
    {L : Type u} [CompleteLattice L]
    (hContinuous : Chapter2.IsContinuousDomain L)
    (hDistributive : IsFrameDistributive L)
    {k : L} (hk : Chapter2.Compact k) :
    IsCompactSubset (pointSpace L) (pointBasicOpen k) := by
  let G : Set L := {x : L | k ≤ x}
  have hGOpen : Chapter2.ScottOpen G := by
    constructor
    · intro x y hy hxy hxG
      exact hy (hxG.trans hxy)
    · intro A s hA hACompl hs hks
      rcases hk hA hs hks with ⟨a, haA, hka⟩
      exact hACompl haA hka
  have hGFilter : Chapter2.IsFilter G := by
    constructor
    · intro x y hx hxy
      exact hx.trans hxy
    · exact ⟨⟨k, le_rfl⟩, fun x hx y hy => ⟨k, le_rfl, hx, hy⟩⟩
  have hSpatial : IsSpatialLattice L :=
    lemma_7_2_15_distributive_continuous_lattices_spatial
      L hContinuous hDistributive
  have hCompact :
      IsCompactSaturated (pointSpace L) {F : Point L | G ⊆ F.1} :=
    pointsContainingFilter_compactSaturated hSpatial hGOpen hGFilter
  have hEq : {F : Point L | G ⊆ F.1} = pointBasicOpen k := by
    ext F
    constructor
    · intro hF
      exact hF le_rfl
    · intro hkF x hkx
      exact F.2.1.2.1 hkF hkx
  exact hEq ▸ hCompact.1

/-- The point space of an algebraic distributive lattice has a compact-open
neighborhood basis consisting of basic opens indexed by compact elements. -/
theorem pointSpace_compactOpenBasis_of_algebraicDistributive
    (L : Type u) [CompleteLattice L]
    (hAlgebraic : Chapter2.IsAlgebraicDomain L)
    (hDistributive : IsFrameDistributive L) :
    HasCompactOpenNeighborhoodBasis (pointSpace L) := by
  intro F U hUOpen hFU
  rcases epsilon_surjective L U hUOpen with ⟨x, hUx⟩
  have hxF : x ∈ F.1 := by
    rw [hUx] at hFU
    exact hFU
  rcases exists_compact_mem_below_of_algebraic_point hAlgebraic F hxF with
    ⟨k, hkCompact, hkF, hkx⟩
  refine ⟨pointBasicOpen k, ?_, hkF, ?_⟩
  · exact ⟨PointOpen.basic k,
      pointBasicOpen_compact_of_compact
        (continuous_of_algebraic hAlgebraic) hDistributive hkCompact⟩
  · intro G hkG
    rw [hUx]
    exact G.2.1.2.1 hkG hkx

/-- Compact-open subsets below each open set generate the topology.  This is the
space-side algebraicity witness used in Theorem 7.2.20. -/
structure CompactOpenBasisGeneratesTopology (X : Space.{u}) : Prop where
  open_eq_sUnion_compact_open_below :
    ∀ U : Set X.Point, X.IsOpen U →
      U = ⋃₀ {V : Set X.Point | IsCompactOpenSubset X V ∧ V ⊆ U}

/-- Compact-open bases generate every open as a union of compact opens below it. -/
theorem compactOpenBasisGeneratesTopology
    (X : Space.{u}) (hBasis : HasCompactOpenNeighborhoodBasis X) :
    CompactOpenBasisGeneratesTopology X := by
  constructor
  intro U hUOpen
  apply Set.Subset.antisymm
  · intro x hxU
    rcases hBasis x U hUOpen hxU with ⟨V, hV, hxV, hVU⟩
    exact ⟨V, ⟨hV, hVU⟩, hxV⟩
  · intro x hx
    rcases hx with ⟨V, hV, hxV⟩
    exact hV.2 hxV

/-- The restricted open-set object map for Theorem 7.2.20. -/
def compactOpenSoberAlgebraicLeft
    (X : CompactOpenSoberSpaceObject.{u}) :
    AlgebraicDistributiveLatticeObject.{u} where
  carrier := OpenSet X.space
  lattice := OpenSet.completeLattice X.space
  algebraic := openSet_algebraic_of_compactOpenNeighborhoodBasis
    X.space X.compactOpenBasis
  distributive := openSet_frameDistributive X.space

/-- The restricted point-space object map for Theorem 7.2.20. -/
def algebraicDistributivePointRight
    (L : AlgebraicDistributiveLatticeObject.{u}) :
    CompactOpenSoberSpaceObject.{u} where
  space := pointSpace L.carrier
  sober := (theorem_7_2_7_points_sober_opens_spatial
    L.carrier (pointSpace L.carrier)).1
  compactOpenBasis := pointSpace_compactOpenBasis_of_algebraicDistributive
    L.carrier L.algebraic L.distributive

/-- Forget algebraicity to obtain the distributive-continuous object used by
the already established Theorem 7.2.16 units. -/
def algebraicDistributiveToContinuous
    (L : AlgebraicDistributiveLatticeObject.{u}) :
    DistributiveContinuousLatticeObject.{u} where
  carrier := L.carrier
  lattice := L.lattice
  continuous := continuous_of_algebraic L.algebraic
  distributive := L.distributive

/-- Point spaces of algebraic distributive lattices have compact basic opens
below every basic neighborhood. -/
structure PointSpaceCompactBasicNeighborhoods
    (L : Type u) [CompleteLattice L] : Prop where
  compact_basic_neighborhood :
    ∀ F : Point L, ∀ x : L, x ∈ F.1 →
      ∃ k : L,
        k ∈ F.1 ∧ IsCompactLatticeElement k ∧ k ≤ x ∧
          PointOpen L (pointBasicOpen k) ∧
            IsCompactSubset (pointSpace L) (pointBasicOpen k)

/-- A distributive algebraic lattice object identified with the open-set
lattice of a space with compact-open neighborhood basis.  This records the
restricted `Ω` object map in Theorem 7.2.20. -/
structure OpenSetAlgebraicDistributiveLatticeObjectPresentation
    (X : Space.{u}) (L : AlgebraicDistributiveLatticeObject.{u}) where
  presentation : OpenSetLatticePresentation X
  carrier_equiv : L.carrier ≃ presentation.carrier
  order_agrees :
    ∀ a b : L.carrier,
      @LE.le L.carrier L.lattice.toPreorder.toLE a b ↔
        @LE.le presentation.carrier presentation.lattice.toPreorder.toLE
          (carrier_equiv a) (carrier_equiv b)

/-- Dual-equivalence data for sober spaces with compact-open neighborhood bases
and distributive algebraic lattices.  Besides the units and preservation data,
the record stores the compact-open generation witnesses used in the proof. -/
structure CompactOpenSoberAlgebraicDistributiveDualityData : Type (u + 1) where
  duality :
    DualEquivalenceData
      CompactOpenSoberSpaceObject.{u}
      AlgebraicDistributiveLatticeObject.{u}
  left_is_opens :
    ∀ X : CompactOpenSoberSpaceObject.{u},
      OpenSetAlgebraicDistributiveLatticeObjectPresentation X.space (duality.left X)
  right_is_points :
    ∀ L : AlgebraicDistributiveLatticeObject.{u},
      @PointSpacePresentation L.carrier L.lattice (duality.right L).space
  space_unit :
    ∀ X : CompactOpenSoberSpaceObject.{u}, X.space.Point →
      (duality.right (duality.left X)).space.Point
  space_unit_continuous :
    ∀ X : CompactOpenSoberSpaceObject.{u},
      StoneContinuousMap X.space (duality.right (duality.left X)).space
  space_unit_agrees :
    ∀ X : CompactOpenSoberSpaceObject.{u}, ∀ x : X.space.Point,
      (space_unit_continuous X).toFun x = space_unit X x
  space_unit_bijective :
    ∀ X : CompactOpenSoberSpaceObject.{u}, Function.Bijective (space_unit X)
  lattice_unit :
    ∀ L : AlgebraicDistributiveLatticeObject.{u}, L.carrier →
      (duality.left (duality.right L)).carrier
  lattice_unit_frame_hom :
    ∀ L : AlgebraicDistributiveLatticeObject.{u},
      @FrameHom L.carrier (duality.left (duality.right L)).carrier
        L.lattice (duality.left (duality.right L)).lattice
  lattice_unit_agrees :
    ∀ L : AlgebraicDistributiveLatticeObject.{u}, ∀ a : L.carrier,
      (@FrameHom.toFun L.carrier (duality.left (duality.right L)).carrier
        L.lattice (duality.left (duality.right L)).lattice
          (lattice_unit_frame_hom L)) a = lattice_unit L a
  lattice_unit_bijective :
    ∀ L : AlgebraicDistributiveLatticeObject.{u}, Function.Bijective (lattice_unit L)
  left_preserves_algebraic_distributive :
    ∀ X : CompactOpenSoberSpaceObject.{u},
      @Chapter2.IsAlgebraicDomain (duality.left X).carrier
          (duality.left X).lattice.toPreorder ∧
        @IsFrameDistributive (duality.left X).carrier (duality.left X).lattice
  right_preserves_compact_open_sober :
    ∀ L : AlgebraicDistributiveLatticeObject.{u},
      IsSober (duality.right L).space ∧
        HasCompactOpenNeighborhoodBasis (duality.right L).space
  compact_open_basis_generates :
    ∀ X : CompactOpenSoberSpaceObject.{u},
      CompactOpenBasisGeneratesTopology X.space
  point_space_compact_basic_neighborhoods :
    ∀ L : AlgebraicDistributiveLatticeObject.{u},
      @PointSpaceCompactBasicNeighborhoods L.carrier L.lattice

/-- Theorem 7.2.20 PDF-facing statement. -/
theorem theorem_7_2_20_algebraic_distributive_duality :
    Nonempty
      (CompactOpenSoberAlgebraicDistributiveDualityData.{u}) := by
  refine ⟨{
    duality := {
      left := compactOpenSoberAlgebraicLeft
      right := algebraicDistributivePointRight
      unit_isomorphism :=
        ∀ X : CompactOpenSoberSpaceObject.{u},
          Function.Bijective (stoneUnitPoint X.space)
      unit_isomorphism_holds := fun X =>
        stoneUnitPoint_bijective_of_sober X.space X.sober
      counit_isomorphism :=
        ∀ L : AlgebraicDistributiveLatticeObject.{u},
          Function.Bijective
            (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun
      counit_isomorphism_holds := fun L =>
        stoneEpsilon_bijective_of_distributiveContinuous
          (algebraicDistributiveToContinuous L) }
    left_is_opens := ?_
    right_is_points := ?_
    space_unit := fun X => stoneUnitPoint X.space
    space_unit_continuous := fun X => stoneUnitContinuous X.space
    space_unit_agrees := ?_
    space_unit_bijective := fun X =>
      stoneUnitPoint_bijective_of_sober X.space X.sober
    lattice_unit := fun L =>
      (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun
    lattice_unit_frame_hom := fun L =>
      stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})
    lattice_unit_agrees := ?_
    lattice_unit_bijective := fun L =>
      stoneEpsilon_bijective_of_distributiveContinuous
        (algebraicDistributiveToContinuous L)
    left_preserves_algebraic_distributive := ?_
    right_preserves_compact_open_sober := ?_
    compact_open_basis_generates := ?_
    point_space_compact_basic_neighborhoods := ?_ }⟩
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
  · intro X
    exact ⟨openSet_algebraic_of_compactOpenNeighborhoodBasis
      X.space X.compactOpenBasis, openSet_frameDistributive X.space⟩
  · intro L
    exact ⟨(theorem_7_2_7_points_sober_opens_spatial
      L.carrier (pointSpace L.carrier)).1,
      pointSpace_compactOpenBasis_of_algebraicDistributive
        L.carrier L.algebraic L.distributive⟩
  · intro X
    exact compactOpenBasisGeneratesTopology X.space X.compactOpenBasis
  · intro L
    constructor
    intro F x hxF
    rcases exists_compact_mem_below_of_algebraic_point L.algebraic F hxF with
      ⟨k, hkCompact, hkF, hkx⟩
    exact ⟨k, hkF, hkCompact, hkx, PointOpen.basic k,
      pointBasicOpen_compact_of_compact
        (continuous_of_algebraic L.algebraic) L.distributive hkCompact⟩


end Chapter7
end AbramskyJung

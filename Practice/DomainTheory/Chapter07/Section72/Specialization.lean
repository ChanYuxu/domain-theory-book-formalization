import Practice.DomainTheory.Chapter07.Section72.SoberSpatial

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.2: specialization order and spatiality

This module follows a coherent dependency cluster inside the textbook section.
The stable public import remains `Practice.DomainTheory.Chapter07.Section72`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

/-- The closure of a set as the intersection of all closed supersets. -/
def ClosureOfSet (X : Space.{u}) (A : Set X.Point) : Set X.Point :=
  ⋂₀ {C : Set X.Point | IsClosed X C ∧ A ⊆ C}

/-- The closure operator contains the original set. -/
theorem subset_closureOfSet (X : Space.{u}) (A : Set X.Point) :
    A ⊆ ClosureOfSet X A := by
  intro x hx C hC
  exact hC.2 hx

/-- Closed supersets contain the closure. -/
theorem closureOfSet_minimal (X : Space.{u}) {A C : Set X.Point}
    (hC : IsClosed X C) (hAC : A ⊆ C) :
    ClosureOfSet X A ⊆ C := by
  intro x hx
  exact hx C ⟨hC, hAC⟩

/-- The closure, defined as an intersection of closed sets, is closed. -/
theorem closureOfSet_closed (X : Space.{u}) (A : Set X.Point) :
    IsClosed X (ClosureOfSet X A) := by
  classical
  let S : Set (Set X.Point) := {C : Set X.Point | IsClosed X C ∧ A ⊆ C}
  have hOpen :
      X.IsOpen (⋃₀ ((fun C : Set X.Point => Cᶜ) '' S)) := by
    exact X.sUnion_open _ (by
      intro U hU
      rcases hU with ⟨C, hCS, rfl⟩
      exact hCS.1)
  have hEq :
      (ClosureOfSet X A)ᶜ = ⋃₀ ((fun C : Set X.Point => Cᶜ) '' S) := by
    ext x
    constructor
    · intro hx
      by_contra hxUnion
      have hxClosure : x ∈ ClosureOfSet X A := by
        intro C hC
        by_contra hxC
        exact hxUnion ⟨Cᶜ, ⟨C, hC, rfl⟩, hxC⟩
      exact hx hxClosure
    · intro hx hxClosure
      rcases hx with ⟨U, hU, hxU⟩
      rcases hU with ⟨C, hCS, rfl⟩
      exact hxU (hxClosure C hCS)
  change X.IsOpen (ClosureOfSet X A)ᶜ
  rw [hEq]
  exact hOpen

/-- Closed sets are downward closed for the specialization preorder. -/
theorem closed_downward_specialization (X : Space.{u}) {C : Set X.Point}
    (hC : IsClosed X C) {x y : X.Point} (hy : y ∈ C)
    (hxy : SpecializationLE X x y) :
    x ∈ C := by
  by_contra hxC
  exact (hxy Cᶜ hC hxC) hy

/-- In a `T0` space, point closures are closed in the lightweight interface. -/
theorem pointClosure_closed_of_t0 (X : Space.{u}) (hT0 : IsT0Space X)
    (x : X.Point) :
    IsClosed X (PointClosure X x) := by
  simpa [IsClosed, PointClosure, Set.compl_setOf] using
    prop_7_2_12_t0_weak_upper_topology X hT0 x

/-- The closure of a directed set is irreducible. -/
theorem directedSet_closure_irreducible
    (X : Space.{u}) {A : Set X.Point}
    (hA : @Chapter2.DirectedSet X.Point (specializationPreorder X) A) :
    IsIrreducibleClosed X (ClosureOfSet X A) := by
  classical
  refine ⟨closureOfSet_closed X A, ?_, ?_⟩
  · rcases hA.1 with ⟨a, ha⟩
    exact ⟨a, subset_closureOfSet X A ha⟩
  · intro B C hB hC hSub
    by_cases hAB : A ⊆ B
    · exact Or.inl (closureOfSet_minimal X hB hAB)
    · right
      have hAC : A ⊆ C := by
        have hbExists : ∃ b : X.Point, b ∈ A ∧ b ∉ B := by
          by_contra hnone
          apply hAB
          intro b hbA
          by_contra hbB
          exact hnone ⟨b, hbA, hbB⟩
        rcases hbExists with ⟨b, hbA, hbB⟩
        intro a haA
        by_contra haC
        rcases hA.2 haA hbA with ⟨d, hdA, had, hbd⟩
        have hdClosure : d ∈ ClosureOfSet X A :=
          subset_closureOfSet X A hdA
        rcases hSub hdClosure with hdB | hdC
        · exact hbB (closed_downward_specialization X hB hdB hbd)
        · exact haC (closed_downward_specialization X hC hdC had)
      exact closureOfSet_minimal X hC hAC

/-- A generic point of the directed closure is the directed supremum in the
specialization preorder. -/
theorem closure_generic_isSup
    (X : Space.{u}) (hT0 : IsT0Space X) {A : Set X.Point} {s : X.Point}
    (hsC : ClosureOfSet X A = PointClosure X s) :
    @Chapter2.IsSup X.Point (specializationPreorder X) A s := by
  constructor
  · intro a ha
    have haClosure : a ∈ ClosureOfSet X A :=
      subset_closureOfSet X A ha
    simpa [hsC, PointClosure] using haClosure
  · intro y hy
    have hPointClosed : IsClosed X (PointClosure X y) :=
      pointClosure_closed_of_t0 X hT0 y
    have hA_y : A ⊆ PointClosure X y := by
      intro a ha
      exact hy ha
    have hClosure_y : ClosureOfSet X A ⊆ PointClosure X y :=
      closureOfSet_minimal X hPointClosed hA_y
    have hsClosure : s ∈ ClosureOfSet X A := by
      rw [hsC]
      intro U _hU hsU
      exact hsU
    exact hClosure_y hsClosure

/-- Sober spaces have directed suprema in their specialization preorder. -/
theorem sober_specialization_isDcpo (X : Space.{u}) (hX : IsSober X) :
    @Chapter2.IsDcpo X.Point (specializationPreorder X) := by
  intro A hA
  have hIrred : IsIrreducibleClosed X (ClosureOfSet X A) :=
    directedSet_closure_irreducible X hA
  rcases hX.2 (ClosureOfSet X A) hIrred with ⟨s, hsC⟩
  exact ⟨s, closure_generic_isSup X hX.1 hsC⟩

/-- Every open set of a sober space is Scott-open for the specialization order. -/
theorem sober_topologyBelowSpecializationScott (X : Space.{u})
    (hX : IsSober X) :
    TopologyBelowSpecializationScott X := by
  classical
  intro U hU
  change
    @Chapter2.IsLowerSet X.Point (specializationPreorder X) Uᶜ ∧
      (∀ ⦃A : Set X.Point⦄ ⦃s : X.Point⦄,
        @Chapter2.DirectedSet X.Point (specializationPreorder X) A →
        A ⊆ Uᶜ →
        @Chapter2.IsSup X.Point (specializationPreorder X) A s →
        s ∈ Uᶜ)
  constructor
  · intro x y hy hxy hxU
    exact hy (hxy U hU hxU)
  · intro A s hA hAs hsSup
    have hIrred : IsIrreducibleClosed X (ClosureOfSet X A) :=
      directedSet_closure_irreducible X hA
    rcases hX.2 (ClosureOfSet X A) hIrred with ⟨g, hgC⟩
    have hgSup :
        @Chapter2.IsSup X.Point (specializationPreorder X) A g :=
      closure_generic_isSup X hX.1 hgC
    have hsClosure : s ∈ ClosureOfSet X A := by
      rw [hgC]
      exact hsSup.2 g hgSup.1
    have hClosedCompl : IsClosed X Uᶜ := by
      simpa [IsClosed] using hU
    have hClosureCompl : ClosureOfSet X A ⊆ Uᶜ :=
      closureOfSet_minimal X hClosedCompl hAs
    exact hClosureCompl hsClosure

namespace StoneContinuousMap

/-- Identity continuous map for the lightweight Chapter 7 spaces. -/
def id (X : Space.{u}) : StoneContinuousMap X X where
  toFun := fun x => x
  preimage_open := by
    intro U hU
    simpa using hU

/-- Composition of continuous maps between lightweight Chapter 7 spaces. -/
def comp {X Y Z : Space.{u}}
    (f : StoneContinuousMap X Y) (g : StoneContinuousMap Y Z) :
    StoneContinuousMap X Z where
  toFun := fun x => g.toFun (f.toFun x)
  preimage_open := by
    intro U hU
    exact f.preimage_open {y : Y.Point | g.toFun y ∈ U}
      (g.preimage_open U hU)

/-- Continuous maps pull closed sets back to closed sets. -/
theorem preimage_closed {X Y : Space.{u}} (f : StoneContinuousMap X Y)
    {C : Set Y.Point} (hC : IsClosed Y C) :
    IsClosed X {x : X.Point | f.toFun x ∈ C} := by
  simpa [IsClosed, Set.compl_setOf] using f.preimage_open Cᶜ hC

/-- Continuous maps are monotone for specialization preorders. -/
theorem specialization {X Y : Space.{u}} (f : StoneContinuousMap X Y)
    {x y : X.Point} (hxy : SpecializationLE X x y) :
    SpecializationLE Y (f.toFun x) (f.toFun y) := by
  intro U hU hxU
  exact hxy {z : X.Point | f.toFun z ∈ U} (f.preimage_open U hU) hxU

/-- The closure of the continuous image of an irreducible closed set is
irreducible closed. -/
theorem image_closure_irreducible {X Y : Space.{u}}
    (f : StoneContinuousMap X Y) {C : Set X.Point}
    (hC : IsIrreducibleClosed X C) :
    IsIrreducibleClosed Y (ClosureOfSet Y (f.toFun '' C)) := by
  classical
  refine ⟨closureOfSet_closed Y (f.toFun '' C), ?_, ?_⟩
  · rcases hC.2.1 with ⟨x, hxC⟩
    exact ⟨f.toFun x, subset_closureOfSet Y (f.toFun '' C) ⟨x, hxC, rfl⟩⟩
  · intro A B hA hB hSub
    have hPreA : IsClosed X {x : X.Point | f.toFun x ∈ A} :=
      preimage_closed f hA
    have hPreB : IsClosed X {x : X.Point | f.toFun x ∈ B} :=
      preimage_closed f hB
    have hCsub :
        C ⊆ {x : X.Point | f.toFun x ∈ A} ∪
          {x : X.Point | f.toFun x ∈ B} := by
      intro x hxC
      have hxClosure :
          f.toFun x ∈ ClosureOfSet Y (f.toFun '' C) :=
        subset_closureOfSet Y (f.toFun '' C) ⟨x, hxC, rfl⟩
      exact hSub hxClosure
    rcases hC.2.2
        {x : X.Point | f.toFun x ∈ A}
        {x : X.Point | f.toFun x ∈ B}
        hPreA hPreB hCsub with hCA | hCB
    · left
      exact closureOfSet_minimal Y hA (by
        intro y hy
        rcases hy with ⟨x, hxC, rfl⟩
        exact hCA hxC)
    · right
      exact closureOfSet_minimal Y hB (by
        intro y hy
        rcases hy with ⟨x, hxC, rfl⟩
        exact hCB hxC)

end StoneContinuousMap

/-- A topological retract of a `T0` sober space is `T0`. -/
theorem topRetractOfSoberSpace_t0
    (X : Space.{u}) (Y : SoberSpaceObject.{u})
    (R : TopRetractOfSoberSpace X Y) :
    IsT0Space X := by
  intro x y hxy
  have hSectionNe :
      R.sectionMap.toFun x ≠ R.sectionMap.toFun y := by
    intro hSection
    apply hxy
    calc
      x = R.retraction.toFun (R.sectionMap.toFun x) := (R.retract_eq x).symm
      _ = R.retraction.toFun (R.sectionMap.toFun y) := by rw [hSection]
      _ = y := R.retract_eq y
  rcases Y.sober.1 (R.sectionMap.toFun x) (R.sectionMap.toFun y)
      hSectionNe with ⟨U, hUOpen, hSep⟩
  refine ⟨{z : X.Point | R.sectionMap.toFun z ∈ U},
    R.sectionMap.preimage_open U hUOpen, ?_⟩
  rcases hSep with hSep | hSep
  · exact Or.inl hSep
  · exact Or.inr hSep

/-- A topological retract of a sober space has generic points for irreducible
closed subsets. -/
theorem topRetractOfSoberSpace_generic
    (X : Space.{u}) (Y : SoberSpaceObject.{u})
    (R : TopRetractOfSoberSpace X Y) :
    EveryIrreducibleClosedHasGenericPoint X := by
  intro C hC
  let imageC : Set Y.space.Point := R.sectionMap.toFun '' C
  have hImageIrred :
      IsIrreducibleClosed Y.space (ClosureOfSet Y.space imageC) :=
    StoneContinuousMap.image_closure_irreducible R.sectionMap hC
  rcases Y.sober.2 (ClosureOfSet Y.space imageC) hImageIrred with
    ⟨y, hyGeneric⟩
  refine ⟨R.retraction.toFun y, ?_⟩
  apply Set.Subset.antisymm
  · intro x hxC
    have hsxClosure : R.sectionMap.toFun x ∈ ClosureOfSet Y.space imageC :=
      subset_closureOfSet Y.space imageC ⟨x, hxC, rfl⟩
    have hsxLeY :
        SpecializationLE Y.space (R.sectionMap.toFun x) y := by
      simpa [hyGeneric, PointClosure] using hsxClosure
    have hxLeX :
        SpecializationLE X x (R.retraction.toFun y) := by
      have hRetracted :=
        StoneContinuousMap.specialization R.retraction hsxLeY
      simpa [R.retract_eq x] using hRetracted
    simpa [PointClosure] using hxLeX
  · intro x hxClosure
    have hyInClosure : y ∈ ClosureOfSet Y.space imageC := by
      rw [hyGeneric]
      intro U _hU hyU
      exact hyU
    have hPreClosed :
        IsClosed Y.space {z : Y.space.Point | R.retraction.toFun z ∈ C} :=
      StoneContinuousMap.preimage_closed R.retraction hC.1
    have hImageSubPre :
        imageC ⊆ {z : Y.space.Point | R.retraction.toFun z ∈ C} := by
      intro z hz
      rcases hz with ⟨c, hcC, rfl⟩
      simpa [R.retract_eq c] using hcC
    have hryC : R.retraction.toFun y ∈ C :=
      closureOfSet_minimal Y.space hPreClosed hImageSubPre hyInClosure
    exact closed_downward_specialization X hC.1 hryC
      (by simpa [PointClosure] using hxClosure)

/-- Sober spaces are closed under topological retracts. -/
theorem topRetractOfSoberSpace_sober
    (X : Space.{u}) (Y : SoberSpaceObject.{u})
    (R : TopRetractOfSoberSpace X Y) :
    IsSober X :=
  ⟨topRetractOfSoberSpace_t0 X Y R,
    topRetractOfSoberSpace_generic X Y R⟩

/-- Object-level prototype used for Theorem 7.2.14.

The retract component is substantive. The chosen `limit` and `colimit`
components are placeholders for a future categorical construction and must not
be read as a proof that sober spaces are complete or cocomplete. -/
def soberSpaceCompleteCocompleteRetractClosed :
    @CompleteCocompleteRetractClosed.{u + 1} SoberSpaceObject.{u} where
  Hom X Y := ULift.{u + 1, u} (@StoneContinuousMap.{u} X.space Y.space)
  id X := ⟨StoneContinuousMap.id X.space⟩
  comp f g := ⟨StoneContinuousMap.comp f.down g.down⟩
  Diagram := SoberSpaceObject.{u}
  Cone D X := ULift.{u + 1, u} (@StoneContinuousMap.{u} X.space D.space)
  Cocone D X := ULift.{u + 1, u} (@StoneContinuousMap.{u} D.space X.space)
  limit D := D
  colimit D := D
  limit_cone D := ⟨StoneContinuousMap.id D.space⟩
  colimit_cocone D := ⟨StoneContinuousMap.id D.space⟩
  limit_lift c := c
  colimit_desc c := c
  Retract X Y := ULift.{u + 1, u} (@TopRetractOfSoberSpace.{u} X.space Y)
  retract_section r := ⟨r.down.sectionMap⟩
  retract_retraction r := ⟨r.down.retraction⟩
  retract_equation := fun {X} {_Y} r =>
    ∀ x : X.space.Point,
      r.down.retraction.toFun (r.down.sectionMap.toFun x) = x
  retract_closed := fun {X Y} r =>
    ⟨{ space := X.space,
        sober := topRetractOfSoberSpace_sober X.space Y r.down }⟩

/-- Proposition 7.2.13 proof data: under the sober/spatial identification, the
specialization order becomes inclusion of completely prime filters; directed
unions of such filters are points, and the basic opens are Scott-open. -/
structure SoberSpecializationProofData (X : Space.{u}) : Type (u + 1) where
  specialization_dcpo : @Chapter2.IsDcpo X.Point (specializationPreorder X)
  topology_below_scott : TopologyBelowSpecializationScott X
  represented_as_points_of_complete_lattice : Prop
  specialization_matches_filter_inclusion : Prop
  directed_union_of_completely_prime_filters : Prop
  basic_opens_scott_open : Prop

/-- Proposition 7.2.13 PDF-facing statement. -/
theorem prop_7_2_13_sober_specialization_dcpo
    (X : Space.{u}) :
    IsSober X →
      @Chapter2.IsDcpo X.Point (specializationPreorder X) ∧
        TopologyBelowSpecializationScott X := by
  intro hX
  exact ⟨sober_specialization_isDcpo X hX,
    sober_topologyBelowSpecializationScott X hX⟩

/-- Theorem 7.2.14 object-level support declaration.

The second conjunct proves closure under topological retracts. The first
conjunct only packages the lightweight prototype above, so the source theorem's
categorical completeness and cocompleteness remain `interface-only`. -/
theorem theorem_7_2_14_sober_complete_cocomplete_retracts :
    Nonempty (CompleteCocompleteRetractClosed SoberSpaceObject.{u}) ∧
      ∀ (X : Space.{u}) (Y : SoberSpaceObject.{u}),
        TopRetractOfSoberSpace X Y → IsSober X := by
  constructor
  · exact ⟨soberSpaceCompleteCocompleteRetractClosed⟩
  · intro X Y R
    exact topRetractOfSoberSpace_sober X Y R

/-- Lemma 7.2.15 proof data: continuous lattices are meet-generated by
meet-irreducibles, distributivity turns these into meet-primes, and hence the
lattice is spatial. -/
structure DistributiveContinuousSpatialProofData
    (L : Type u) [CompleteLattice L] : Prop where
  meet_irreducible_generation :
    MeetGeneratedBy ({x : L | IsFiniteMeetIrreducible x})
  irreducibles_are_prime :
    ∀ x : L, IsFiniteMeetIrreducible x → IsFiniteMeetPrime x
  meet_prime_generation :
    MeetGeneratedBy ({x : L | IsFiniteMeetPrime x})
  spatial : IsSpatialLattice L

/-- The complete proof package behind Lemma 7.2.15. -/
theorem distributiveContinuousSpatialProofData
    (L : Type u) [CompleteLattice L]
    (hContinuous : Chapter2.IsContinuousDomain L)
    (hDistributive : IsFrameDistributive L) :
    DistributiveContinuousSpatialProofData L := by
  have hContinuousComplete : IsContinuousCompleteLattice L :=
    ⟨completeLattice_isDcpo L, hContinuous⟩
  have hIrredGenerated :
      MeetGeneratedBy ({x : L | IsFiniteMeetIrreducible x}) :=
    theorem_7_1_7_continuous_lattice_meet_generated L hContinuousComplete
  have hPrimeIrred :
      ∀ x : L, IsFiniteMeetPrime x → IsFiniteMeetIrreducible x :=
    (prop_7_1_6_meet_prime_irreducible L).1
  have hIrredPrime :
      ∀ x : L, IsFiniteMeetIrreducible x → IsFiniteMeetPrime x :=
    (prop_7_1_6_meet_prime_irreducible L).2 hDistributive
  have hPrimeGenerated :
      MeetGeneratedBy ({x : L | IsFiniteMeetPrime x}) := by
    intro x
    have hSetEq :
        {g : L | g ∈ ({y : L | IsFiniteMeetIrreducible y} : Set L) ∧ x ≤ g} =
          {g : L | g ∈ ({y : L | IsFiniteMeetPrime y} : Set L) ∧ x ≤ g} := by
      ext g
      constructor
      · intro hg
        exact ⟨hIrredPrime g hg.1, hg.2⟩
      · intro hg
        exact ⟨hPrimeIrred g hg.1, hg.2⟩
    calc
      x = sInf {g : L | g ∈ ({y : L | IsFiniteMeetIrreducible y} : Set L) ∧ x ≤ g} :=
        hIrredGenerated x
      _ = sInf {g : L | g ∈ ({y : L | IsFiniteMeetPrime y} : Set L) ∧ x ≤ g} := by
        rw [hSetEq]
  have hUnit := prop_7_2_4_lattice_unit_spatiality L
  have hSeparated : CompletelyPrimeFiltersSeparate L :=
    hUnit.2.2.2.1.2 hPrimeGenerated
  have hInjective : EpsilonInjective L :=
    hUnit.2.2.1.2 hSeparated
  exact
    { meet_irreducible_generation := hIrredGenerated
      irreducibles_are_prime := hIrredPrime
      meet_prime_generation := hPrimeGenerated
      spatial := ⟨hInjective, hUnit.1⟩ }

/-- Lemma 7.2.15 PDF-facing statement. -/
theorem lemma_7_2_15_distributive_continuous_lattices_spatial
    (L : Type u) [CompleteLattice L] :
    Chapter2.IsContinuousDomain L → IsFrameDistributive L → IsSpatialLattice L := by
  intro hContinuous hDistributive
  exact (distributiveContinuousSpatialProofData L hContinuous hDistributive).spatial


end Chapter7
end AbramskyJung

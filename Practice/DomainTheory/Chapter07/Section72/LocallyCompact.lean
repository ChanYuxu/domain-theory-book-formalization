import Practice.DomainTheory.Chapter07.Section72.Specialization

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.2: locally compact duality

This module follows a coherent dependency cluster inside the textbook section.
The stable public import remains `Practice.DomainTheory.Chapter07.Section72`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

private theorem punit_isBasisRaw :
    @Chapter2.IsBasisRaw PUnit inferInstance (Set.univ : Set PUnit) := by
  intro x
  refine ⟨Set.univ, ?_, ?_, ?_⟩
  · intro a _ha
    constructor
    · trivial
    · intro A _s hdir _hsup _hxs
      rcases hdir.1 with ⟨b, hb⟩
      exact ⟨b, hb, by cases a; cases b; exact le_rfl⟩
  · constructor
    · exact ⟨PUnit.unit, trivial⟩
    · intro a _ha b _hb
      exact ⟨PUnit.unit, trivial, by cases a; exact le_rfl, by cases b; exact le_rfl⟩
  · constructor
    · intro y _hy
      cases x
      cases y
      exact le_rfl
    · intro y _hy
      cases x
      cases y
      exact le_rfl

private def punitDiscreteSpace : Space.{u} where
  Point := PUnit
  IsOpen := fun _ => True
  univ_open := trivial
  inter_open := by
    intro _ _ _ _
    trivial
  sUnion_open := by
    intro _ _
    trivial

private theorem punitDiscreteSpace_sober : IsSober punitDiscreteSpace.{u} := by
  constructor
  · intro x y hxy
    cases x
    cases y
    exact False.elim (hxy rfl)
  · intro C hC
    have hC_univ : C = Set.univ := by
      ext x
      constructor
      · intro _hx
        trivial
      · intro _hx
        rcases hC.2.1 with ⟨y, hy⟩
        cases x
        cases y
        exact hy
    refine ⟨PUnit.unit, ?_⟩
    rw [hC_univ]
    ext x
    constructor
    · intro _hx
      cases x
      intro U _hU hxU
      exact hxU
    · intro _hx
      trivial

private theorem punitDiscreteSpace_compact_univ :
    IsCompactSubset punitDiscreteSpace.{u} (Set.univ : Set PUnit) := by
  intro cover _hOpen hcover
  have hmem : PUnit.unit ∈ ⋃₀ cover := hcover trivial
  rcases hmem with ⟨U, hUcover, hUnitU⟩
  refine ⟨{U}, ?_, Set.finite_singleton U, ?_⟩
  · intro V hV
    have hVU : V = U := by
      simpa using hV
    simpa [hVU] using hUcover
  · intro x _hx
    cases x
    exact ⟨U, by simp, hUnitU⟩

private theorem punitDiscreteSpace_compact_subset (K : Set PUnit) :
    IsCompactSubset punitDiscreteSpace.{u} K := by
  intro cover _hOpen hcover
  by_cases hK : K.Nonempty
  · rcases hK with ⟨x, hxK⟩
    cases x
    have hmem : PUnit.unit ∈ ⋃₀ cover := hcover hxK
    rcases hmem with ⟨U, hUcover, hUnitU⟩
    refine ⟨{U}, ?_, Set.finite_singleton U, ?_⟩
    · intro V hV
      have hVU : V = U := by
        simpa using hV
      simpa [hVU] using hUcover
    · intro y _hy
      cases y
      exact ⟨U, by simp, hUnitU⟩
  · refine ⟨∅, ?_, Set.finite_empty, ?_⟩
    · intro U hU
      cases hU
    · intro x hx
      exact False.elim (hK ⟨x, hx⟩)

private theorem punitDiscreteSpace_locallyCompact :
    IsLocallyCompact punitDiscreteSpace.{u} := by
  intro x U _hU hxU
  refine ⟨Set.univ, Set.univ, ?_, trivial, trivial, ?_, ?_⟩
  · constructor
    · exact punitDiscreteSpace_compact_univ
    · intro _y _z _hy _hyz
      trivial
  · intro y _hy
    trivial
  · intro y _hy
    cases x
    cases y
    exact hxU

private theorem punit_frameDistributive : IsFrameDistributive PUnit := by
  intro x S
  exact Subsingleton.elim _ _

private theorem punit_wayBelow_unit : Chapter2.WayBelow PUnit.unit PUnit.unit := by
  intro A _s hdir _hsup _hle
  rcases hdir.1 with ⟨a, ha⟩
  exact ⟨a, ha, by cases a; exact le_rfl⟩

private theorem punit_multiplicativeApproximation :
    MultiplicativeApproximation PUnit := by
  intro x y z _hxy _hxz
  cases x
  cases y
  cases z
  exact punit_wayBelow_unit

private theorem punit_arithmeticLattice : IsArithmeticLattice PUnit := by
  exact ⟨⟨punit_frameDistributive, ⟨Set.univ, punit_isBasisRaw⟩⟩,
    punit_multiplicativeApproximation⟩

private theorem punit_algebraic :
    Chapter2.IsAlgebraicDomain PUnit := by
  intro x
  refine ⟨Set.univ, ?_, ?_, ?_⟩
  · intro a _ha
    constructor
    · cases a
      exact punit_wayBelow_unit
    · cases a
      cases x
      exact punit_wayBelow_unit
  · constructor
    · exact ⟨PUnit.unit, trivial⟩
    · intro a _ha b _hb
      exact ⟨PUnit.unit, trivial, by cases a; exact le_rfl, by cases b; exact le_rfl⟩
  · constructor
    · intro y _hy
      cases x
      cases y
      exact le_rfl
    · intro y _hy
      cases x
      cases y
      exact le_rfl

private theorem punit_algebraicArithmetic :
    IsAlgebraicArithmeticLattice PUnit := by
  exact ⟨punit_arithmeticLattice, punit_algebraic⟩

private theorem punitDiscreteSpace_coherent :
    IsCoherentSpace punitDiscreteSpace.{u} := by
  refine ⟨punitDiscreteSpace_sober, punitDiscreteSpace_locallyCompact, ?_⟩
  intro K L _hK _hL
  exact punitDiscreteSpace_compact_subset (K ∩ L)

private theorem punitDiscreteSpace_spectral :
    IsSpectralSpace punitDiscreteSpace.{u} := by
  refine ⟨punitDiscreteSpace_coherent, ?_⟩
  intro x U _hU hxU
  refine ⟨Set.univ, ⟨trivial, punitDiscreteSpace_compact_univ⟩, trivial, ?_⟩
  intro y _hy
  cases x
  cases y
  exact hxU

/-- An open `O` is compactly below an open `O'` when a compact saturated set lies
between them.  Both arguments live in the open-set lattice `Omega(X)`, as in the
textbook; using the entire powerset would state a strictly stronger and generally
false way-below claim. -/
def CompactBetweenOpenSets (X : Space.{u})
    (O O' : OpenSet X) : Prop :=
  ∃ K : Set X.Point, IsCompactSaturated X K ∧ O.1 ⊆ K ∧ K ⊆ O'.1

/-- The compact-between-open-sets criterion used in the proof of Theorem 7.2.16:
if a compact saturated set lies between `O` and `O'`, then `O` is way-below
`O'` in the open-set lattice. -/
def CompactBetweenImpliesWayBelowOpens (X : Space.{u}) : Prop :=
  ∀ O O' : OpenSet X,
    CompactBetweenOpenSets X O O' →
      Chapter2.WayBelow O O'

/-- The local-compactness proof ingredient for Theorem 7.2.16: every open set is
the union of open subsets with compact saturated sets between them and the target
open set. -/
structure OpenSetCompactApproximationBasis (X : Space.{u}) : Prop where
  open_eq_union_compactly_below :
    ∀ O : OpenSet X,
      O = sSup {V : OpenSet X | CompactBetweenOpenSets X V O}

/-- The empty subset is compact in every lightweight space. -/
theorem compactSubset_empty (X : Space.{u}) :
    IsCompactSubset X (∅ : Set X.Point) := by
  intro cover _hOpen _hCover
  exact ⟨∅, Set.empty_subset cover, Set.finite_empty, Set.empty_subset _⟩

/-- Finite unions preserve compactness in the open-cover formulation. -/
theorem compactSubset_union
    {X : Space.{u}} {K L : Set X.Point}
    (hK : IsCompactSubset X K) (hL : IsCompactSubset X L) :
    IsCompactSubset X (K ∪ L) := by
  intro cover hOpen hCover
  have hKCover : K ⊆ ⋃₀ cover := fun x hx => hCover (Or.inl hx)
  have hLCover : L ⊆ ⋃₀ cover := fun x hx => hCover (Or.inr hx)
  rcases hK cover hOpen hKCover with ⟨coverK, hKsub, hKfinite, hKcovered⟩
  rcases hL cover hOpen hLCover with ⟨coverL, hLsub, hLfinite, hLcovered⟩
  refine ⟨coverK ∪ coverL, ?_, hKfinite.union hLfinite, ?_⟩
  · intro U hU
    exact hU.elim (fun hUK => hKsub hUK) (fun hUL => hLsub hUL)
  · intro x hx
    rcases hx with hxK | hxL
    · rcases hKcovered hxK with ⟨U, hU, hxU⟩
      exact ⟨U, Or.inl hU, hxU⟩
    · rcases hLcovered hxL with ⟨U, hU, hxU⟩
      exact ⟨U, Or.inr hU, hxU⟩

/-- Saturated subsets are closed under binary unions. -/
theorem saturated_union
    {X : Space.{u}} {K L : Set X.Point}
    (hK : IsSaturated X K) (hL : IsSaturated X L) :
    IsSaturated X (K ∪ L) := by
  intro x y hx hxy
  exact hx.elim (fun hxK => Or.inl (hK hxK hxy))
    (fun hxL => Or.inr (hL hxL hxy))

/-- Compact saturated subsets are closed under binary unions. -/
theorem compactSaturated_union
    {X : Space.{u}} {K L : Set X.Point}
    (hK : IsCompactSaturated X K) (hL : IsCompactSaturated X L) :
    IsCompactSaturated X (K ∪ L) :=
  ⟨compactSubset_union hK.1 hL.1, saturated_union hK.2 hL.2⟩

/-- A compact saturated set between two opens proves the corresponding
way-below relation in the open-set lattice. -/
theorem compactBetweenImpliesWayBelowOpens (X : Space.{u}) :
    CompactBetweenImpliesWayBelowOpens X := by
  intro O O' hBetween A s hDirected hSup hO's
  rcases hBetween with ⟨K, hK, hOK, hKO'⟩
  have hSupCanonical : Chapter2.IsSup A (sSup A : OpenSet X) :=
    OpenSet.sSup_isLUB X A
  have hsEq : s = sSup A := Chapter2.IsSup.unique hSup hSupCanonical
  let cover : Set (Set X.Point) := (fun U : OpenSet X => U.1) '' A
  have hCoverOpen : ∀ U ∈ cover, X.IsOpen U := by
    intro U hU
    rcases hU with ⟨V, _hVA, rfl⟩
    exact V.2
  have hKCover : K ⊆ ⋃₀ cover := by
    intro x hxK
    have hxs : x ∈ s.1 := hO's (hKO' hxK)
    have hxSup : x ∈ (sSup A : OpenSet X).1 := by
      rw [← hsEq]
      exact hxs
    rcases (OpenSet.mem_sSup_iff X A x).1 hxSup with ⟨U, hUA, hxU⟩
    exact ⟨U.1, ⟨U, hUA, rfl⟩, hxU⟩
  rcases hK.1 cover hCoverOpen hKCover with
    ⟨finiteCover, hFiniteSub, hFinite, hKFinite⟩
  have hChoose : ∀ V : {V : Set X.Point // V ∈ finiteCover},
      ∃ U : OpenSet X, U ∈ A ∧ U.1 = V.1 := by
    intro V
    rcases hFiniteSub V.2 with ⟨U, hUA, hUV⟩
    exact ⟨U, hUA, hUV⟩
  let pick : {V : Set X.Point // V ∈ finiteCover} → OpenSet X :=
    fun V => Classical.choose (hChoose V)
  let selected : Set (OpenSet X) := Set.range pick
  letI : Finite {V : Set X.Point // V ∈ finiteCover} :=
    Set.finite_coe_iff.mpr hFinite
  have hSelectedFinite : selected.Finite := Set.finite_range pick
  have hSelectedSub : selected ⊆ A := by
    intro U hU
    rcases hU with ⟨V, rfl⟩
    exact (Classical.choose_spec (hChoose V)).1
  rcases Chapter2.DirectedSet.exists_upper_finite hDirected
      hSelectedFinite hSelectedSub with ⟨U, hUA, hUpper⟩
  refine ⟨U, hUA, ?_⟩
  intro x hxO
  rcases hKFinite (hOK hxO) with ⟨V, hVfinite, hxV⟩
  let V' : {V : Set X.Point // V ∈ finiteCover} := ⟨V, hVfinite⟩
  have hPickEq : (pick V').1 = V := (Classical.choose_spec (hChoose V')).2
  have hxPick : x ∈ (pick V').1 := by
    rw [hPickEq]
    exact hxV
  exact hUpper (pick V') (Set.mem_range_self V') hxPick

/-- For a fixed target open, compactly enclosed opens form a directed family. -/
theorem compactBetweenOpenSets_directed (X : Space.{u}) (O : OpenSet X) :
    Chapter2.DirectedSet {V : OpenSet X | CompactBetweenOpenSets X V O} := by
  let emptyOpen : OpenSet X := ⟨∅, Space.empty_open X⟩
  have hEmptyCompactSaturated : IsCompactSaturated X (∅ : Set X.Point) :=
    ⟨compactSubset_empty X, by intro x _y hx; cases hx⟩
  constructor
  · exact ⟨emptyOpen,
      ⟨∅, hEmptyCompactSaturated, Set.empty_subset _, Set.empty_subset _⟩⟩
  · intro V hV W hW
    rcases hV with ⟨K, hK, hVK, hKO⟩
    rcases hW with ⟨L, hL, hWL, hLO⟩
    let U : OpenSet X := ⟨V.1 ∪ W.1, X.union_open V.2 W.2⟩
    refine ⟨U, ?_, ?_, ?_⟩
    · refine ⟨K ∪ L, compactSaturated_union hK hL, ?_, ?_⟩
      · intro x hx
        exact hx.elim (fun hxV => Or.inl (hVK hxV))
          (fun hxW => Or.inr (hWL hxW))
      · intro x hx
        exact hx.elim (fun hxK => hKO hxK) (fun hxL => hLO hxL)
    · intro x hx
      exact Or.inl hx
    · intro x hx
      exact Or.inr hx

/-- Local compactness identifies each open as the supremum of its compactly
enclosed open subsets. -/
theorem compactBetweenOpenSets_isSup
    (X : Space.{u}) (hLocal : IsLocallyCompact X) (O : OpenSet X) :
    Chapter2.IsSup {V : OpenSet X | CompactBetweenOpenSets X V O} O := by
  constructor
  · intro V hV
    rcases hV with ⟨K, _hK, hVK, hKO⟩
    exact fun x hx => hKO (hVK hx)
  · intro Y hUpper x hxO
    rcases hLocal x O.1 O.2 hxO with ⟨K, V, hK, hVOpen, hxV, hVK, hKO⟩
    let V' : OpenSet X := ⟨V, hVOpen⟩
    exact (hUpper (a := V') ⟨K, hK, hVK, hKO⟩) hxV

/-- The compact-approximation basis supplied by local compactness. -/
theorem openSetCompactApproximationBasis_of_locallyCompact
    (X : Space.{u}) (hLocal : IsLocallyCompact X) :
    OpenSetCompactApproximationBasis X := by
  constructor
  intro O
  exact Chapter2.IsSup.unique
    (compactBetweenOpenSets_isSup X hLocal O)
    (OpenSet.sSup_isLUB X _)

/-- The open-set lattice of a locally compact space is continuous. -/
theorem openSet_continuous_of_locallyCompact
    (X : Space.{u}) (hLocal : IsLocallyCompact X) :
    Chapter2.IsContinuousDomain (OpenSet X) := by
  refine ⟨Set.univ, ?_⟩
  intro O
  let A : Set (OpenSet X) := {V : OpenSet X | CompactBetweenOpenSets X V O}
  refine ⟨A, ?_, compactBetweenOpenSets_directed X O,
    compactBetweenOpenSets_isSup X hLocal O⟩
  intro V hV
  exact ⟨Set.mem_univ V, compactBetweenImpliesWayBelowOpens X V O hV⟩

/-- The point-space compact-neighborhood proof ingredient from Theorem 7.2.16:
if a completely prime filter `F` contains `x`, then a way-below `y` and a compact
saturated neighborhood lie between `O_y` and `O_x`. -/
structure PointSpaceCompactNeighborhoodBasis
    (L : Type u) [CompleteLattice L] : Prop where
  basic_compact_neighborhood :
    ∀ F : Point L, ∀ x : L, x ∈ F.1 →
      ∃ y : L, ∃ K : Set (Point L),
        y ∈ F.1 ∧ Chapter2.WayBelow y x ∧
          IsCompactSaturated (pointSpace L) K ∧
            pointBasicOpen y ⊆ K ∧ K ⊆ pointBasicOpen x

/-- Every completely prime lattice filter is Scott-open.  Complete primeness
reflects membership of an arbitrary supremum to one member of the family. -/
theorem completelyPrimeFilter_scottOpen
    {L : Type u} [CompleteLattice L] {F : Set L}
    (hF : IsCompletelyPrimeFilter F) :
    Chapter2.ScottOpen F := by
  constructor
  · intro x y hy hxy hxF
    exact hy (hF.1.2.1 hxF hxy)
  · intro A s hDirected hAComplement hSup hsF
    have hSupEq : sSup A = s := by
      apply le_antisymm
      · exact sSup_le hSup.1
      · exact hSup.2 (sSup A) (fun a ha => le_sSup ha)
    have hsSupF : sSup A ∈ F := by
      rw [hSupEq]
      exact hsF
    rcases hF.2 A hsSupF with ⟨a, haA, haF⟩
    exact hAComplement haA haF

/-- The interpolating filter supplied by Lemma 2.3.8 lies inside the principal
upper set of its source approximation. -/
theorem interpolatingFilter_subset_upperClosure
    {L : Type u} [Preorder L]
    (hContinuous : Chapter2.IsContinuousDomain L)
    {y x : L} (hyx : Chapter2.WayBelow y x) :
    Chapter2.interpolatingFilter hContinuous hyx ⊆
      Chapter2.upperClosure ({y} : Set L) := by
  intro z hz
  rw [Chapter2.interpolatingFilter, Set.mem_iUnion] at hz
  rcases hz with ⟨n, hnz⟩
  refine ⟨y, by simp, ?_⟩
  exact le_trans
    (Chapter2.prop_2_2_2_1
      (Chapter2.wayBelowInterpSeq_source_wayBelow hContinuous hyx n))
    (Chapter2.prop_2_2_2_1 hnz)

/-- The family of basic point opens indexed by a lattice filter. -/
def pointOpensOfLatticeFilter
    {L : Type u} [CompleteLattice L] (G : Set L) :
    Set (Set (Point L)) :=
  {U : Set (Point L) | ∃ a ∈ G, U = pointBasicOpen a}

/-- Intersecting the basic opens indexed by `G` gives exactly the points whose
underlying completely prime filters contain `G`. -/
theorem sInter_pointOpensOfLatticeFilter
    {L : Type u} [CompleteLattice L] (G : Set L) :
    ⋂₀ pointOpensOfLatticeFilter G = {F : Point L | G ⊆ F.1} := by
  ext F
  constructor
  · intro hF a haG
    exact hF (pointBasicOpen a) ⟨a, haG, rfl⟩
  · intro hF U hU
    rcases hU with ⟨a, haG, rfl⟩
    exact hF haG

/-- In a spatial lattice, a Scott-open order filter indexes a Scott-open filter
of opens of the point space. -/
theorem pointOpensOfLatticeFilter_scottOpen
    {L : Type u} [CompleteLattice L] {G : Set L}
    (hSpatial : IsSpatialLattice L)
    (hGOpen : Chapter2.ScottOpen G)
    (hGFilter : Chapter2.IsFilter G) :
    IsScottOpenFilterOfOpens (pointSpace L)
      (pointOpensOfLatticeFilter G) := by
  let reflectOrder : EpsilonOrderReflecting L :=
    (epsilon_order_reflecting_iff_injective L).2 hSpatial.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    rcases hU with ⟨a, _haG, rfl⟩
    exact PointOpen.basic a
  · rcases hGFilter.2.1 with ⟨a, haG⟩
    have hTopG : (⊤ : L) ∈ G := hGFilter.1 haG le_top
    exact ⟨⊤, hTopG, (prop_7_1_13_point_topology L).top_eq_univ.symm⟩
  · intro U V hU hUV hVOpen
    rcases hU with ⟨a, haG, rfl⟩
    rcases epsilon_surjective L V hVOpen with ⟨b, hVb⟩
    have hab : a ≤ b := reflectOrder a b (by
      intro F hFa
      have hFV : F ∈ V := hUV hFa
      rw [hVb] at hFV
      exact hFV)
    exact ⟨b, hGFilter.1 haG hab, hVb⟩
  · intro U V hU hV
    rcases hU with ⟨a, haG, rfl⟩
    rcases hV with ⟨b, hbG, rfl⟩
    rcases hGFilter.2.2 haG hbG with ⟨c, hcG, hca, hcb⟩
    have hInfG : a ⊓ b ∈ G := hGFilter.1 hcG (le_inf hca hcb)
    exact ⟨a ⊓ b, hInfG,
      (prop_7_1_13_point_topology L).inter_eq a b |>.symm⟩
  · intro A hAOpen hADirected hUnion
    let B : Set L := {a : L | pointBasicOpen a ∈ A}
    have hBDirected : Chapter2.DirectedSet B := by
      constructor
      · rcases hADirected.1 with ⟨U, hUA⟩
        rcases epsilon_surjective L U (hAOpen U hUA) with ⟨a, hUa⟩
        exact ⟨a, by simpa [B, hUa] using hUA⟩
      · intro a haB b hbB
        rcases hADirected.2 haB hbB with ⟨U, hUA, haU, hbU⟩
        rcases epsilon_surjective L U (hAOpen U hUA) with ⟨c, hUc⟩
        have hac : a ≤ c := reflectOrder a c (by
          intro F hFa
          have hFU : F ∈ U := haU hFa
          rw [hUc] at hFU
          exact hFU)
        have hbc : b ≤ c := reflectOrder b c (by
          intro F hFb
          have hFU : F ∈ U := hbU hFb
          rw [hUc] at hFU
          exact hFU)
        exact ⟨c, by simpa [B, hUc] using hUA, hac, hbc⟩
    have hUnionEq : ⋃₀ A = pointBasicOpen (sSup B) := by
      rw [(prop_7_1_13_point_topology L).sUnion_eq B]
      apply Set.Subset.antisymm
      · intro F hF
        rcases hF with ⟨U, hUA, hFU⟩
        rcases epsilon_surjective L U (hAOpen U hUA) with ⟨a, hUa⟩
        refine ⟨pointBasicOpen a, ?_, ?_⟩
        · exact ⟨a, by simpa [B, hUa] using hUA, rfl⟩
        · have hFEpsilon : F ∈ EpsilonMap a := by
            rw [← hUa]
            exact hFU
          simpa [EpsilonMap] using hFEpsilon
      · intro F hF
        rcases hF with ⟨U, ⟨a, haB, rfl⟩, hFa⟩
        exact ⟨pointBasicOpen a, haB, hFa⟩
    rcases hUnion with ⟨d, hdG, hUnionD⟩
    have hSupG : sSup B ∈ G := by
      have hMapEq : EpsilonMap (sSup B) = EpsilonMap d := by
        change pointBasicOpen (sSup B) = pointBasicOpen d
        exact hUnionEq.symm.trans hUnionD
      have hSupEq : sSup B = d := hSpatial.1 (sSup B) d hMapEq
      rw [hSupEq]
      exact hdG
    have hBIsSup : Chapter2.IsSup B (sSup B) := by
      constructor
      · intro b hb
        exact le_sSup hb
      · intro z hz
        exact sSup_le hz
    have hExists : ∃ b ∈ B, b ∈ G := by
      by_contra hNone
      have hBComplement : B ⊆ Gᶜ := by
        intro b hbB hbG
        exact hNone ⟨b, hbB, hbG⟩
      exact (hGOpen.2 hBDirected hBComplement hBIsSup) hSupG
    rcases hExists with ⟨b, hbB, hbG⟩
    exact ⟨pointBasicOpen b, hbB, ⟨b, hbG, rfl⟩⟩

/-- The points containing a Scott-open filter form a compact saturated subset
of the point space.  This is the Hofmann--Mislove step in Theorem 7.2.16. -/
theorem pointsContainingFilter_compactSaturated
    {L : Type u} [CompleteLattice L] {G : Set L}
    (hSpatial : IsSpatialLattice L)
    (hGOpen : Chapter2.ScottOpen G)
    (hGFilter : Chapter2.IsFilter G) :
    IsCompactSaturated (pointSpace L) {F : Point L | G ⊆ F.1} := by
  let Φ : Set (Set (Point L)) := pointOpensOfLatticeFilter G
  have hΦ : IsScottOpenFilterOfOpens (pointSpace L) Φ :=
    pointOpensOfLatticeFilter_scottOpen hSpatial hGOpen hGFilter
  have hSober : IsSober (pointSpace L) :=
    (theorem_7_2_7_points_sober_opens_spatial L (pointSpace L)).1
  have hCompact : IsCompactSaturated (pointSpace L) (⋂₀ Φ) :=
    (theorem_7_2_9_hofmann_mislove_sober
      (pointSpace L) hSober).intersection_candidate Φ hΦ |>.1
  dsimp [Φ] at hCompact
  have hEq := sInter_pointOpensOfLatticeFilter G
  exact Eq.mp (congrArg (IsCompactSaturated (pointSpace L)) hEq) hCompact

/-- The compact-neighborhood basis of the point space of a distributive
continuous lattice, following the proof of Theorem 7.2.16. -/
theorem pointSpaceCompactNeighborhoodBasis_of_distributiveContinuous
    (L : Type u) [CompleteLattice L]
    (hContinuous : Chapter2.IsContinuousDomain L)
    (hDistributive : IsFrameDistributive L) :
    PointSpaceCompactNeighborhoodBasis L := by
  have hSpatial : IsSpatialLattice L :=
    lemma_7_2_15_distributive_continuous_lattices_spatial L
      hContinuous hDistributive
  constructor
  intro F x hxF
  have hFOpen : Chapter2.ScottOpen F.1 :=
    completelyPrimeFilter_scottOpen F.2
  have hSupported :=
    Chapter2.prop_2_3_6_open_supported_by_wayBelow hContinuous hFOpen
  have hxUnion : x ∈ ⋃ y ∈ F.1, Chapter2.wayBelowUpper y := by
    rw [← hSupported]
    exact hxF
  rw [Set.mem_iUnion] at hxUnion
  rcases hxUnion with ⟨y, hyUnion⟩
  rw [Set.mem_iUnion] at hyUnion
  rcases hyUnion with ⟨hyF, hyx⟩
  let G : Set L := Chapter2.interpolatingFilter hContinuous hyx
  let K : Set (Point L) := {H : Point L | G ⊆ H.1}
  have hGOpen : Chapter2.ScottOpen G :=
    Chapter2.interpolatingFilter_scottOpen hContinuous hyx
  have hGFilter : Chapter2.IsFilter G :=
    Chapter2.interpolatingFilter_isFilter hContinuous hyx
  have hGUpper : G ⊆ Chapter2.upperClosure ({y} : Set L) :=
    interpolatingFilter_subset_upperClosure hContinuous hyx
  have hxG : x ∈ G :=
    Chapter2.interpolatingFilter_mem_target hContinuous hyx
  have hKCompact : IsCompactSaturated (pointSpace L) K :=
    pointsContainingFilter_compactSaturated hSpatial hGOpen hGFilter
  refine ⟨y, K, hyF, hyx, hKCompact, ?_, ?_⟩
  · intro H hyH z hzG
    rcases hGUpper hzG with ⟨y', hy', hyz⟩
    have hyy' : y' = y := by simpa using hy'
    exact H.2.1.2.1 hyH (by simpa [hyy'] using hyz)
  · intro H hHK
    exact hHK hxG

/-- A distributive-continuous lattice object identified with the open-set
lattice of a space.  This is the restricted `Ω` object map used in
Theorem 7.2.16. -/
structure OpenSetDistributiveLatticeObjectPresentation
    (X : Space.{u}) (L : DistributiveContinuousLatticeObject.{u}) where
  presentation : OpenSetLatticePresentation X
  carrier_equiv : L.carrier ≃ presentation.carrier
  order_agrees :
    ∀ a b : L.carrier,
      @LE.le L.carrier L.lattice.toPreorder.toLE a b ↔
        @LE.le presentation.carrier presentation.lattice.toPreorder.toLE
          (carrier_equiv a) (carrier_equiv b)

/-- The concrete lattice of opens is frame-distributive. -/
theorem openSet_frameDistributive (X : Space.{u}) :
    IsFrameDistributive (OpenSet X) := by
  exact theorem_7_2_6_spatial_lattice_frame (OpenSet X)
    ⟨openSet_epsilon_injective X, epsilon_surjective (OpenSet X)⟩

/-- The point space of a distributive continuous lattice is locally compact. -/
theorem pointSpace_locallyCompact_of_distributiveContinuous
    (L : Type u) [CompleteLattice L]
    (hContinuous : Chapter2.IsContinuousDomain L)
    (hDistributive : IsFrameDistributive L) :
    IsLocallyCompact (pointSpace L) := by
  let hBasis :=
    pointSpaceCompactNeighborhoodBasis_of_distributiveContinuous
      L hContinuous hDistributive
  intro F U hUOpen hFU
  rcases epsilon_surjective L U hUOpen with ⟨x, hUx⟩
  have hxF : x ∈ F.1 := by
    have : F ∈ EpsilonMap x := by
      rw [← hUx]
      exact hFU
    exact this
  rcases hBasis.basic_compact_neighborhood F x hxF with
    ⟨y, K, hyF, _hyx, hK, hOyK, hKOx⟩
  refine ⟨K, pointBasicOpen y, hK, PointOpen.basic y, hyF, hOyK, ?_⟩
  intro H hHK
  rw [hUx]
  exact hKOx hHK

/-- The restricted open-set object map in Theorem 7.2.16. -/
def locallyCompactDistributiveLeft
    (X : LocallyCompactSoberSpaceObject.{u}) :
    DistributiveContinuousLatticeObject.{u} where
  carrier := OpenSet X.space
  lattice := OpenSet.completeLattice X.space
  continuous := openSet_continuous_of_locallyCompact X.space X.locallyCompact
  distributive := openSet_frameDistributive X.space

/-- The restricted point-space object map in Theorem 7.2.16. -/
def distributiveContinuousPointRight
    (L : DistributiveContinuousLatticeObject.{u}) :
    LocallyCompactSoberSpaceObject.{u} where
  space := pointSpace L.carrier
  sober := (theorem_7_2_7_points_sober_opens_spatial
    L.carrier (pointSpace L.carrier)).1
  locallyCompact := pointSpace_locallyCompact_of_distributiveContinuous
    L.carrier L.continuous L.distributive

/-- Distributive continuity supplies the spatiality needed for bijectivity of
the lattice-side Stone unit. -/
theorem stoneEpsilon_bijective_of_distributiveContinuous
    (L : DistributiveContinuousLatticeObject.{u}) :
    Function.Bijective
      (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun := by
  let S : SpatialLatticeObject.{u} :=
    { carrier := L.carrier
      lattice := L.lattice
      spatial := lemma_7_2_15_distributive_continuous_lattices_spatial
        L.carrier L.continuous L.distributive }
  exact stoneEpsilon_bijective_of_spatial S

/-- Dual-equivalence data for locally compact sober spaces and distributive
continuous lattices.  It records the restricted functors, unit maps, continuity
and frame-homomorphism witnesses, bijectivity of the units, and the compact
approximation data used in the proof. -/
structure LocallyCompactDistributiveDualityData : Type (u + 1) where
  duality :
    DualEquivalenceData
      LocallyCompactSoberSpaceObject.{u}
      DistributiveContinuousLatticeObject.{u}
  left_is_opens :
    ∀ X : LocallyCompactSoberSpaceObject.{u},
      OpenSetDistributiveLatticeObjectPresentation X.space (duality.left X)
  right_is_points :
    ∀ L : DistributiveContinuousLatticeObject.{u},
      @PointSpacePresentation L.carrier L.lattice (duality.right L).space
  space_unit :
    ∀ X : LocallyCompactSoberSpaceObject.{u}, X.space.Point →
      (duality.right (duality.left X)).space.Point
  space_unit_continuous :
    ∀ X : LocallyCompactSoberSpaceObject.{u},
      StoneContinuousMap X.space (duality.right (duality.left X)).space
  space_unit_agrees :
    ∀ X : LocallyCompactSoberSpaceObject.{u}, ∀ x : X.space.Point,
      (space_unit_continuous X).toFun x = space_unit X x
  space_unit_bijective :
    ∀ X : LocallyCompactSoberSpaceObject.{u}, Function.Bijective (space_unit X)
  lattice_unit :
    ∀ L : DistributiveContinuousLatticeObject.{u}, L.carrier →
      (duality.left (duality.right L)).carrier
  lattice_unit_frame_hom :
    ∀ L : DistributiveContinuousLatticeObject.{u},
      @FrameHom L.carrier (duality.left (duality.right L)).carrier
        L.lattice (duality.left (duality.right L)).lattice
  lattice_unit_agrees :
    ∀ L : DistributiveContinuousLatticeObject.{u}, ∀ a : L.carrier,
      (@FrameHom.toFun L.carrier (duality.left (duality.right L)).carrier
        L.lattice (duality.left (duality.right L)).lattice
          (lattice_unit_frame_hom L)) a = lattice_unit L a
  lattice_unit_bijective :
    ∀ L : DistributiveContinuousLatticeObject.{u}, Function.Bijective (lattice_unit L)
  left_preserves_distributive_continuous :
    ∀ X : LocallyCompactSoberSpaceObject.{u},
      @Chapter2.IsContinuousDomain (duality.left X).carrier
          (duality.left X).lattice.toPreorder ∧
        @IsFrameDistributive (duality.left X).carrier (duality.left X).lattice
  right_preserves_locally_compact_sober :
    ∀ L : DistributiveContinuousLatticeObject.{u},
      IsSober (duality.right L).space ∧ IsLocallyCompact (duality.right L).space
  open_lattice_compact_approximation :
    ∀ X : LocallyCompactSoberSpaceObject.{u},
      OpenSetCompactApproximationBasis X.space
  compact_between_way_below :
    ∀ X : LocallyCompactSoberSpaceObject.{u},
      CompactBetweenImpliesWayBelowOpens X.space
  point_lattice_spatiality_data :
    ∀ L : DistributiveContinuousLatticeObject.{u},
      @DistributiveContinuousSpatialProofData L.carrier L.lattice
  point_space_compact_neighborhood_basis :
    ∀ L : DistributiveContinuousLatticeObject.{u},
      @PointSpaceCompactNeighborhoodBasis L.carrier L.lattice

/-- Theorem 7.2.16 PDF-facing statement. -/
theorem theorem_7_2_16_locally_compact_distributive_duality :
    Nonempty
      (LocallyCompactDistributiveDualityData.{u}) := by
  refine ⟨{
    duality := {
      left := locallyCompactDistributiveLeft
      right := distributiveContinuousPointRight
      unit_isomorphism :=
        ∀ X : LocallyCompactSoberSpaceObject.{u},
          Function.Bijective (stoneUnitPoint X.space)
      unit_isomorphism_holds := fun X =>
        stoneUnitPoint_bijective_of_sober X.space X.sober
      counit_isomorphism :=
        ∀ L : DistributiveContinuousLatticeObject.{u},
          Function.Bijective
            (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun
      counit_isomorphism_holds :=
        stoneEpsilon_bijective_of_distributiveContinuous }
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
    lattice_unit_bijective :=
      stoneEpsilon_bijective_of_distributiveContinuous
    left_preserves_distributive_continuous := ?_
    right_preserves_locally_compact_sober := ?_
    open_lattice_compact_approximation := ?_
    compact_between_way_below := ?_
    point_lattice_spatiality_data := ?_
    point_space_compact_neighborhood_basis := ?_ }⟩
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
  · intro X
    exact ⟨openSet_continuous_of_locallyCompact X.space X.locallyCompact,
      openSet_frameDistributive X.space⟩
  · intro L
    exact ⟨(theorem_7_2_7_points_sober_opens_spatial
      L.carrier (pointSpace L.carrier)).1,
      pointSpace_locallyCompact_of_distributiveContinuous
        L.carrier L.continuous L.distributive⟩
  · intro X
    exact openSetCompactApproximationBasis_of_locallyCompact
      X.space X.locallyCompact
  · intro X
    exact compactBetweenImpliesWayBelowOpens X.space
  · intro L
    exact distributiveContinuousSpatialProofData
      L.carrier L.continuous L.distributive
  · intro L
    exact pointSpaceCompactNeighborhoodBasis_of_distributiveContinuous
      L.carrier L.continuous L.distributive


end Chapter7
end AbramskyJung

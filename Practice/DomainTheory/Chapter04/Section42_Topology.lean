import Practice.DomainTheory.Chapter04.Section42_ProjectionFS

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 4, Section 4.2.13--4.2.20

Compact saturated sets, coherence, and the Lawson topology.
-/

universe u

namespace AbramskyJung
namespace Chapter4

/-- Theorem 4.2.13, PDF text: for a continuous domain, neighborhoods of
compact saturated sets are precisely the Scott-open filters in `σD`.  The text
identifies this as a Hofmann-Mislove special case; the proof is not available
in the current import order, so this direct statement is registered as local
proof debt. -/
theorem theorem_4_2_13_hofmann_mislove_neighborhoods
    (D : OrderedDomain.{u}) (hDcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) :
    (∀ A : Set D.carrier,
      IsCompactSaturated D A → IsScottOpenFilter D (ScottNeighborhoods D A)) ∧
      ∀ F : Set (Set D.carrier),
        IsScottOpenFilter D F →
          ∃ A : Set D.carrier, IsCompactSaturated D A ∧ F = ScottNeighborhoods D A := by
  admit

/-- Filtered families of compact saturated sets, ordered by reverse inclusion. -/
def IsFilteredCompactSaturatedFamily
    (D : OrderedDomain.{u}) (K : Set (Set D.carrier)) : Prop :=
  K.Nonempty ∧
    (∀ A ∈ K, IsCompactSaturated D A) ∧
      ∀ A ∈ K, ∀ B ∈ K, ∃ C ∈ K, C ⊆ A ∧ C ⊆ B

/-- In the reverse-inclusion order on `κD`, the supremum of a filtered family is
its intersection. -/
def CompactSaturatedSupremumByIntersection
    (D : OrderedDomain.{u}) (K : Set (Set D.carrier)) : Prop :=
  IsFilteredCompactSaturatedFamily D K →
    ∃ hcompact : IsCompactSaturated D (⋂₀ K),
      Chapter3.IsSup
        ({A : CompactSaturatedCarrier D | A.carrierSet ∈ K})
        ({ carrierSet := ⋂₀ K, compact_saturated := hcompact } : CompactSaturatedCarrier D)

/-- Proposition 4.2.14, PDF text: for a continuous domain, `κD` and
`κD \ {∅}` are dcpos, filtered suprema in `κD` are intersections, and
Scott-open compactness detects filtered intersections.  The full compact
saturated set proof is registered as local proof debt. -/
theorem prop_4_2_14_compact_saturated_scott_open_filters
    (D : OrderedDomain.{u}) (hDcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) :
    Chapter3.IsDcpo (CompactSaturatedCarrier D) ∧
      Chapter3.IsDcpo (NonemptyCompactSaturatedCarrier D) ∧
      (∀ K : Set (Set D.carrier), CompactSaturatedSupremumByIntersection D K) ∧
      (∀ K : Set (Set D.carrier),
        IsFilteredCompactSaturatedFamily D K →
          IsCompactSaturated D (⋂₀ K)) ∧
      (∀ K : Set (Set D.carrier), ∀ O : Set D.carrier,
        IsFilteredCompactSaturatedFamily D K → Chapter2.ScottOpen O →
          (⋂₀ K) ⊆ O → ∃ A ∈ K, A ⊆ O) ∧
        ∀ K : Set (Set D.carrier),
            IsFilteredCompactSaturatedFamily D K →
              (∀ A ∈ K, A.Nonempty) → (⋂₀ K).Nonempty := by
  admit

/-- A finite union of principal upper sets is Scott-compact and saturated. -/
theorem finiteUpperClosure_isCompactSaturated
    (D : OrderedDomain.{u}) {M : Set D.carrier} (hM : M.Finite) :
    IsCompactSaturated D (Chapter2.upperClosure M) := by
  classical
  constructor
  · intro cover hOpen hCover
    have hMemberCovered :
        ∀ m ∈ M, ∃ U ∈ cover, m ∈ U := by
      intro m hm
      have hmUpper : m ∈ Chapter2.upperClosure M := ⟨m, hm, le_rfl⟩
      rcases Set.mem_sUnion.mp (hCover hmUpper) with ⟨U, hUcover, hmU⟩
      exact ⟨U, hUcover, hmU⟩
    let chosenOpen : D.carrier → Set D.carrier := fun m =>
      if hm : m ∈ M then Classical.choose (hMemberCovered m hm) else ∅
    have chosenOpen_mem :
        ∀ m ∈ M, chosenOpen m ∈ cover := by
      intro m hm
      simp only [chosenOpen, dif_pos hm]
      exact (Classical.choose_spec (hMemberCovered m hm)).1
    have member_mem_chosenOpen :
        ∀ m ∈ M, m ∈ chosenOpen m := by
      intro m hm
      simp only [chosenOpen, dif_pos hm]
      exact (Classical.choose_spec (hMemberCovered m hm)).2
    refine ⟨chosenOpen '' M, ?_, hM.image chosenOpen, ?_⟩
    · intro U hU
      rcases hU with ⟨m, hm, rfl⟩
      exact chosenOpen_mem m hm
    · intro x hx
      rcases hx with ⟨m, hm, hmx⟩
      apply Set.mem_sUnion_of_mem
      · exact Chapter2.scottOpen_upper
          (hOpen (chosenOpen m) (chosenOpen_mem m hm))
          (member_mem_chosenOpen m hm) hmx
      · exact ⟨m, hm, rfl⟩
  · exact Chapter2.isUpperSet_upperClosure M

/-- The finite-upper-set approximation used in the proof of Proposition 4.2.15:
inside every Scott-open neighborhood of a compact saturated set there is a
finite generated upper set. -/
theorem exists_finiteUpperClosure_between
    (D : OrderedDomain.{u}) (hD : Chapter3.IsContinuousDomain D.carrier)
    {K O : Set D.carrier} (hK : IsCompactSaturated D K)
    (hO : Chapter2.ScottOpen O) (hKO : K ⊆ O) :
    ∃ M : Set D.carrier, M.Finite ∧ M ⊆ O ∧
      ∃ V : Set D.carrier, Chapter2.ScottOpen V ∧ K ⊆ V ∧
        V ⊆ Chapter2.upperClosure M ∧ Chapter2.upperClosure M ⊆ O := by
  classical
  have hD2 : Chapter2.IsContinuousDomain D.carrier := by
    rcases hD with ⟨B, hB⟩
    exact ⟨B, Chapter2.basis_to_raw hB⟩
  have hPointApprox :
      ∀ x ∈ K, ∃ b : D.carrier, b ∈ O ∧ Chapter3.WayBelow b x := by
    intro x hx
    have hDir := Chapter2.continuous_wayBelowLower_directed hD2 x
    have hSup := Chapter2.continuous_wayBelowLower_isSup hD2 x
    rcases ((Chapter2.prop_2_3_3_sup_iff_neighborhoods hDir).1 hSup).2
        O ⟨hO, hKO hx⟩ with ⟨b, hbx, hbO⟩
    exact ⟨b, hbO, hbx⟩
  let basisPoint : D.carrier → D.carrier := fun x =>
    if hx : x ∈ K then Classical.choose (hPointApprox x hx) else x
  have basisPoint_mem :
      ∀ x ∈ K, basisPoint x ∈ O := by
    intro x hx
    simp only [basisPoint, dif_pos hx]
    exact (Classical.choose_spec (hPointApprox x hx)).1
  have basisPoint_wayBelow :
      ∀ x ∈ K, Chapter3.WayBelow (basisPoint x) x := by
    intro x hx
    simp only [basisPoint, dif_pos hx]
    exact (Classical.choose_spec (hPointApprox x hx)).2
  let cover : Set (Set D.carrier) :=
    {U | ∃ x ∈ K, U = Chapter2.wayBelowUpper (basisPoint x)}
  have hCoverOpen : ∀ U ∈ cover, Chapter2.ScottOpen U := by
    intro U hU
    rcases hU with ⟨x, hx, rfl⟩
    exact Chapter2.scottOpen_wayBelowUpper hD2 (basisPoint x)
  have hKcover : K ⊆ ⋃₀ cover := by
    intro x hx
    apply Set.mem_sUnion_of_mem
      (t := Chapter2.wayBelowUpper (basisPoint x))
      (basisPoint_wayBelow x hx)
    exact ⟨x, hx, rfl⟩
  rcases hK.1 cover hCoverOpen hKcover with
    ⟨finiteCover, hFiniteCoverSub, hFiniteCover, hFiniteCoverCovers⟩
  have hOpenWitness :
      ∀ U ∈ finiteCover,
        ∃ x ∈ K, U = Chapter2.wayBelowUpper (basisPoint x) := by
    intro U hU
    exact hFiniteCoverSub hU
  let witnessPoint : {U : Set D.carrier // U ∈ finiteCover} → D.carrier := fun U =>
    Classical.choose (hOpenWitness U.1 U.2)
  let M : Set D.carrier := Set.range (fun U => basisPoint (witnessPoint U))
  letI : Finite {U : Set D.carrier // U ∈ finiteCover} :=
    Set.finite_coe_iff.mp hFiniteCover
  have hMfinite : M.Finite := Set.finite_range _
  have witnessPoint_mem :
      ∀ U : {U : Set D.carrier // U ∈ finiteCover}, witnessPoint U ∈ K := by
    intro U
    exact (Classical.choose_spec (hOpenWitness U.1 U.2)).1
  have witnessOpen_eq :
      ∀ U : {U : Set D.carrier // U ∈ finiteCover},
        U.1 = Chapter2.wayBelowUpper (basisPoint (witnessPoint U)) := by
    intro U
    exact (Classical.choose_spec (hOpenWitness U.1 U.2)).2
  let V : Set D.carrier := ⋃₀ finiteCover
  have hVOpen : Chapter2.ScottOpen V := by
    have hOpen :
        Chapter2.ScottOpen
          (⋃ U : {U : Set D.carrier // U ∈ finiteCover}, U.1) :=
      Chapter2.scottOpen_iUnion (fun U => hCoverOpen U.1 (hFiniteCoverSub U.2))
    have hEq :
        V = ⋃ U : {U : Set D.carrier // U ∈ finiteCover}, U.1 := by
      ext x
      simp [V]
    rw [hEq]
    exact hOpen
  refine ⟨M, hMfinite, ?_, V, hVOpen, hFiniteCoverCovers, ?_, ?_⟩
  · intro b hb
    rcases hb with ⟨U, rfl⟩
    exact basisPoint_mem (witnessPoint U) (witnessPoint_mem U)
  · intro x hx
    rcases Set.mem_sUnion.mp hx with ⟨U, hU, hxU⟩
    let U' : {V : Set D.carrier // V ∈ finiteCover} := ⟨U, hU⟩
    have hxWay :
        Chapter3.WayBelow (basisPoint (witnessPoint U')) x := by
      change x ∈ (U' : Set D.carrier) at hxU
      rw [witnessOpen_eq U'] at hxU
      exact hxU
    exact ⟨basisPoint (witnessPoint U'),
      ⟨U', rfl⟩,
      Chapter3.wayBelow_le hxWay⟩
  · intro x hx
    rcases hx with ⟨b, hb, hbx⟩
    exact Chapter2.scottOpen_upper hO (by
      rcases hb with ⟨U, rfl⟩
      exact basisPoint_mem (witnessPoint U) (witnessPoint_mem U)) hbx

/-- Finite unions of basic Scott opens generated by way-below points. -/
def FiniteWayBelowOpen (D : OrderedDomain.{u}) (M : Set D.carrier) : Set D.carrier :=
  ⋃ b ∈ M, Chapter2.wayBelowUpper b

/-- A finite-way-below union is Scott-open; finiteness is used later for the
compact saturated upper closure, not for openness. -/
theorem finiteWayBelowOpen_scottOpen
    (D : OrderedDomain.{u}) (hD : Chapter2.IsContinuousDomain D.carrier)
    (M : Set D.carrier) :
    Chapter2.ScottOpen (FiniteWayBelowOpen D M) := by
  have hOpen :
      Chapter2.ScottOpen
        (⋃ b : {b : D.carrier // b ∈ M}, Chapter2.wayBelowUpper b.1) :=
    Chapter2.scottOpen_iUnion (fun b =>
      Chapter2.scottOpen_wayBelowUpper hD b.1)
  simpa only [FiniteWayBelowOpen, Set.iUnion_subtype] using hOpen

/-- Every finite-way-below union lies in the ordinary upper closure of the
same generating set. -/
theorem finiteWayBelowOpen_subset_upperClosure
    (D : OrderedDomain.{u}) (M : Set D.carrier) :
    FiniteWayBelowOpen D M ⊆ Chapter2.upperClosure M := by
  intro x hx
  rw [FiniteWayBelowOpen, Set.mem_iUnion] at hx
  rcases hx with ⟨b, hx⟩
  rw [Set.mem_iUnion] at hx
  rcases hx with ⟨hbM, hbx⟩
  exact ⟨b, hbM, Chapter3.wayBelow_le hbx⟩

/-- If the generators lie in an upper Scott-open set, so does their ordinary
upper closure. -/
theorem upperClosure_subset_scottOpen
    (D : OrderedDomain.{u}) {M U : Set D.carrier}
    (hM : M ⊆ U) (hU : Chapter2.ScottOpen U) :
    Chapter2.upperClosure M ⊆ U := by
  intro x hx
  rcases hx with ⟨b, hbM, hbx⟩
  exact Chapter2.scottOpen_upper hU (hM hbM) hbx

/-- The Scott-open carrier represented by a finite-way-below union. -/
def finiteWayBelowOpenCarrier
    (D : OrderedDomain.{u}) (hD : Chapter2.IsContinuousDomain D.carrier)
    (M : Set D.carrier) : ScottOpenCarrier D where
  carrierSet := FiniteWayBelowOpen D M
  scott_open := finiteWayBelowOpen_scottOpen D hD M

/-- Enlarging the generator set enlarges the corresponding basic open union. -/
theorem finiteWayBelowOpen_mono
    (D : OrderedDomain.{u}) {M N : Set D.carrier} (hMN : M ⊆ N) :
    FiniteWayBelowOpen D M ⊆ FiniteWayBelowOpen D N := by
  intro x hx
  rw [FiniteWayBelowOpen, Set.mem_iUnion] at hx ⊢
  rcases hx with ⟨b, hx⟩
  rw [Set.mem_iUnion] at hx
  rcases hx with ⟨hbM, hbx⟩
  refine ⟨b, ?_⟩
  rw [Set.mem_iUnion]
  exact ⟨hMN hbM, hbx⟩

/-- The way-below relation on compact saturated sets ordered by reverse inclusion. -/
def CompactSaturatedWayBelow
    (D : OrderedDomain.{u}) (A B : CompactSaturatedCarrier D) : Prop :=
  Chapter3.WayBelow A B

/-- Proposition 4.2.15(2) criterion for compact-saturated way-below. -/
def CompactSaturatedWayBelowByOpen
    (D : OrderedDomain.{u}) (A B : CompactSaturatedCarrier D) : Prop :=
  ∃ O : Set D.carrier, Chapter2.ScottOpen O ∧ B.carrierSet ⊆ O ∧ O ⊆ A.carrierSet

/-- Open-neighborhood approximants of a compact saturated set, ordered by
reverse inclusion. -/
def CompactSaturatedOpenApproximants
    (D : OrderedDomain.{u}) (B : CompactSaturatedCarrier D) :
    Set (CompactSaturatedCarrier D) :=
  {A | CompactSaturatedWayBelowByOpen D A B}

/-- The open-neighborhood approximants form a directed family with supremum the
original compact saturated set. -/
theorem compactSaturatedOpenApproximants_directed_isSup
    (D : OrderedDomain.{u}) (hD : Chapter3.IsContinuousDomain D.carrier)
    (B : CompactSaturatedCarrier D) :
    Chapter3.DirectedSet (CompactSaturatedOpenApproximants D B) ∧
      Chapter3.IsSup (CompactSaturatedOpenApproximants D B) B := by
  classical
  have hNonempty : (CompactSaturatedOpenApproximants D B).Nonempty := by
    rcases exists_finiteUpperClosure_between D hD B.compact_saturated
        Chapter2.scottOpen_univ (Set.subset_univ _) with
      ⟨M, hMfinite, _hMuniv, V, hVopen, hBV, hVupper, _hUpperUniv⟩
    let A : CompactSaturatedCarrier D :=
      ⟨Chapter2.upperClosure M, finiteUpperClosure_isCompactSaturated D hMfinite⟩
    exact ⟨A, ⟨V, hVopen, hBV, hVupper⟩⟩
  have hDirected : Chapter3.DirectedSet (CompactSaturatedOpenApproximants D B) := by
    constructor
    · exact hNonempty
    · intro A hA C hC
      rcases hA with ⟨OA, hOAopen, hBOA, hOAA⟩
      rcases hC with ⟨OC, hOCopen, hBOC, hOCC⟩
      have hInterOpen : Chapter2.ScottOpen (OA ∩ OC) :=
        Chapter2.scottOpen_inter hOAopen hOCopen
      have hBInter : B.carrierSet ⊆ OA ∩ OC := fun x hx =>
        ⟨hBOA hx, hBOC hx⟩
      rcases exists_finiteUpperClosure_between D hD B.compact_saturated
          hInterOpen hBInter with
        ⟨M, hMfinite, _hMinter, V, hVopen, hBV, hVupper, hUpperInter⟩
      let E : CompactSaturatedCarrier D :=
        ⟨Chapter2.upperClosure M, finiteUpperClosure_isCompactSaturated D hMfinite⟩
      refine ⟨E, ⟨V, hVopen, hBV, hVupper⟩, ?_, ?_⟩
      · exact Set.Subset.trans hUpperInter
          (Set.Subset.trans Set.inter_subset_left hOAA)
      · exact Set.Subset.trans hUpperInter
          (Set.Subset.trans Set.inter_subset_right hOCC)
  refine ⟨hDirected, ?_⟩
  constructor
  · intro A hA
    rcases hA with ⟨O, _hOopen, hBO, hOA⟩
    exact Set.Subset.trans hBO hOA
  · intro Z hZ
    intro x hxZ
    by_contra hxB
    let O : Set D.carrier :=
      (Chapter2.lowerClosure ({x} : Set D.carrier))ᶜ
    have hOopen : Chapter2.ScottOpen O := by
      simpa [O, Chapter2.ScottOpen] using
        (Chapter2.scottClosed_principal_ideal x)
    have hBO : B.carrierSet ⊆ O := by
      intro b hbB hbLower
      rcases hbLower with ⟨y, hy, hby⟩
      have hyx : y = x := by simpa using hy
      exact hxB (B.compact_saturated.2 hbB (by simpa [hyx] using hby))
    rcases exists_finiteUpperClosure_between D hD B.compact_saturated
        hOopen hBO with
      ⟨M, hMfinite, _hMO, V, hVopen, hBV, hVupper, hUpperO⟩
    let A : CompactSaturatedCarrier D :=
      ⟨Chapter2.upperClosure M, finiteUpperClosure_isCompactSaturated D hMfinite⟩
    have hAapprox : A ∈ CompactSaturatedOpenApproximants D B :=
      ⟨V, hVopen, hBV, hVupper⟩
    have hxA : x ∈ A.carrierSet := hZ hAapprox hxZ
    have hxO : x ∈ O := hUpperO hxA
    exact hxO ⟨x, by simp, le_rfl⟩

/-- Proposition 4.2.15(2): way-below in compact saturated sets ordered by
reverse inclusion is equivalent to interpolation by a Scott-open set. -/
theorem compactSaturatedWayBelow_iff_open
    (D : OrderedDomain.{u}) (hDcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier)
    (A B : CompactSaturatedCarrier D) :
    CompactSaturatedWayBelow D A B ↔
      CompactSaturatedWayBelowByOpen D A B := by
  classical
  rcases prop_4_2_14_compact_saturated_scott_open_filters D hDcpo hD with
    ⟨_hKdcpo, _hNonemptyKdcpo, _hSupIntersection, hIntersectionCompact,
      hOpenDetectsIntersection, _hNonemptyIntersection⟩
  constructor
  · intro hAB
    have hApprox :=
      compactSaturatedOpenApproximants_directed_isSup D hD B
    rcases hAB hApprox.1 hApprox.2 le_rfl with ⟨C, hC, hAC⟩
    rcases hC with ⟨O, hOopen, hBO, hOC⟩
    exact ⟨O, hOopen, hBO, Set.Subset.trans hOC hAC⟩
  · rintro ⟨O, hOopen, hBO, hOA⟩
    intro family S hFamilyDirected hFamilySup hBS
    let compactSetFamily : Set (Set D.carrier) :=
      CompactSaturatedCarrier.carrierSet '' family
    have hFiltered : IsFilteredCompactSaturatedFamily D compactSetFamily := by
      constructor
      · rcases hFamilyDirected.1 with ⟨C, hC⟩
        exact ⟨C.carrierSet, ⟨C, hC, rfl⟩⟩
      · constructor
        · intro C hC
          rcases hC with ⟨X, hX, rfl⟩
          exact X.compact_saturated
        · intro C hC E hE
          rcases hC with ⟨X, hX, rfl⟩
          rcases hE with ⟨Y, hY, rfl⟩
          rcases hFamilyDirected.2 hX hY with ⟨Z, hZ, hXZ, hYZ⟩
          exact ⟨Z.carrierSet, ⟨Z, hZ, rfl⟩, hXZ, hYZ⟩
    have hInterCompact :
        IsCompactSaturated D (⋂₀ compactSetFamily) :=
      hIntersectionCompact compactSetFamily hFiltered
    let I : CompactSaturatedCarrier D :=
      ⟨⋂₀ compactSetFamily, hInterCompact⟩
    have hFamilyLeI : Chapter3.IsUpperBound family I := by
      intro C hC
      intro x hx
      exact (Set.mem_sInter.mp hx) C.carrierSet ⟨C, hC, rfl⟩
    have hSLeI : S ≤ I :=
      hFamilySup.2 I hFamilyLeI
    have hInterO : (⋂₀ compactSetFamily) ⊆ O :=
      Set.Subset.trans hSLeI (Set.Subset.trans hBS hBO)
    rcases hOpenDetectsIntersection compactSetFamily O hFiltered hOopen hInterO with
      ⟨Cset, hCset, hCsetO⟩
    rcases hCset with ⟨C, hC, rfl⟩
    exact ⟨C, hC, Set.Subset.trans hCsetO hOA⟩

/-- Proposition 4.2.15(1): compact saturated sets ordered by reverse inclusion
form a continuous domain. -/
theorem compactSaturatedCarrier_isContinuous
    (D : OrderedDomain.{u}) (hDcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) :
    Chapter3.IsContinuousDomain (CompactSaturatedCarrier D) := by
  refine ⟨Set.univ, ?_⟩
  intro B
  have hApprox :=
    compactSaturatedOpenApproximants_directed_isSup D hD B
  have hEq :
      Chapter2.Approximants (Set.univ : Set (CompactSaturatedCarrier D)) B =
        CompactSaturatedOpenApproximants D B := by
    ext A
    constructor
    · intro hA
      exact (compactSaturatedWayBelow_iff_open D hDcpo hD A B).1 hA.2
    · intro hA
      exact ⟨Set.mem_univ A,
        (compactSaturatedWayBelow_iff_open D hDcpo hD A B).2 hA⟩
  rw [hEq]
  exact hApprox

/-- The actual way-below relation in the lattice `σD` of Scott opens. -/
def ScottOpenWayBelow (D : OrderedDomain.{u}) (O U : ScottOpenCarrier D) : Prop :=
  Chapter3.WayBelow O U

/-- Proposition 4.2.15(3) criterion for Scott-open way-below. -/
def ScottOpenWayBelowByCompactCarrier
    (D : OrderedDomain.{u}) (O U : ScottOpenCarrier D) : Prop :=
  ∃ A : Set D.carrier, IsCompactSaturated D A ∧ O.carrierSet ⊆ A ∧ A ⊆ U.carrierSet

/-- The open-set approximation relation from Proposition 4.2.15. -/
def ScottOpenWayBelowByCompact
    (D : OrderedDomain.{u}) (O U : Set D.carrier) : Prop :=
  Chapter2.ScottOpen O ∧ Chapter2.ScottOpen U ∧
    ∃ A : Set D.carrier, IsCompactSaturated D A ∧ O ⊆ A ∧ A ⊆ U

/-- Proposition 4.2.15(3): way-below in the inclusion order of Scott opens is
equivalent to interpolation by a compact saturated set. -/
theorem scottOpenWayBelow_iff_compactCarrier
    (D : OrderedDomain.{u}) (hD : Chapter3.IsContinuousDomain D.carrier)
    (O U : ScottOpenCarrier D) :
    ScottOpenWayBelow D O U ↔ ScottOpenWayBelowByCompactCarrier D O U := by
  classical
  have hD2 : Chapter2.IsContinuousDomain D.carrier := by
    rcases hD with ⟨B, hB⟩
    exact ⟨B, Chapter2.basis_to_raw hB⟩
  constructor
  · intro hOU
    let I := {M : Set D.carrier // M.Finite ∧ M ⊆ U.carrierSet}
    let family : Set (ScottOpenCarrier D) :=
      Set.range (fun M : I => finiteWayBelowOpenCarrier D hD2 M.1)
    have hFamilyDirected : Chapter3.DirectedSet family := by
      constructor
      · let M0 : I := ⟨∅, Set.finite_empty, Set.empty_subset _⟩
        exact ⟨finiteWayBelowOpenCarrier D hD2 M0.1, ⟨M0, rfl⟩⟩
      · intro V hV W hW
        rcases hV with ⟨M, rfl⟩
        rcases hW with ⟨N, rfl⟩
        let P : I := ⟨M.1 ∪ N.1, M.2.1.union N.2.1,
          Set.union_subset M.2.2 N.2.2⟩
        refine ⟨finiteWayBelowOpenCarrier D hD2 P.1, ⟨P, rfl⟩, ?_, ?_⟩
        · exact finiteWayBelowOpen_mono D Set.subset_union_left
        · exact finiteWayBelowOpen_mono D Set.subset_union_right
    have hFamilySup : Chapter3.IsSup family U := by
      constructor
      · intro V hV
        rcases hV with ⟨M, rfl⟩
        exact Set.Subset.trans
          (finiteWayBelowOpen_subset_upperClosure D M.1)
          (upperClosure_subset_scottOpen D M.2.2 U.scott_open)
      · intro Z hZ
        intro x hxU
        have hDir := Chapter2.continuous_wayBelowLower_directed hD2 x
        have hSup := Chapter2.continuous_wayBelowLower_isSup hD2 x
        rcases ((Chapter2.prop_2_3_3_sup_iff_neighborhoods hDir).1 hSup).2
            U.carrierSet ⟨U.scott_open, hxU⟩ with ⟨b, hbx, hbU⟩
        let M : I := ⟨{b}, Set.finite_singleton b, by
          intro y hy
          have hyb : y = b := by simpa using hy
          simpa [hyb] using hbU⟩
        have hMember :
            finiteWayBelowOpenCarrier D hD2 M.1 ∈ family := ⟨M, rfl⟩
        exact hZ hMember (by
          change x ∈ FiniteWayBelowOpen D M.1
          rw [FiniteWayBelowOpen, Set.mem_iUnion]
          refine ⟨b, ?_⟩
          rw [Set.mem_iUnion]
          have hbM : b ∈ M.1 := by
            change b ∈ ({b} : Set D.carrier)
            simp
          exact ⟨hbM, hbx⟩)
    rcases hOU hFamilyDirected hFamilySup le_rfl with ⟨V, hV, hOV⟩
    rcases hV with ⟨M, rfl⟩
    refine ⟨Chapter2.upperClosure M.1,
      finiteUpperClosure_isCompactSaturated D M.2.1, ?_, ?_⟩
    · exact Set.Subset.trans hOV
        (finiteWayBelowOpen_subset_upperClosure D M.1)
    · exact upperClosure_subset_scottOpen D M.2.2 U.scott_open
  · rintro ⟨A, hA, hOA, hAU⟩
    intro family S hFamilyDirected hFamilySup hUS
    let unionSet : Set D.carrier :=
      ⋃ V : {V : ScottOpenCarrier D // V ∈ family}, V.1.carrierSet
    have hUnionOpen : Chapter2.ScottOpen unionSet := by
      exact Chapter2.scottOpen_iUnion (fun V => V.1.scott_open)
    let unionCarrier : ScottOpenCarrier D := ⟨unionSet, hUnionOpen⟩
    have hFamilyLeUnion : Chapter3.IsUpperBound family unionCarrier := by
      intro V hV
      intro x hx
      change x ∈ (⋃ W : {W : ScottOpenCarrier D // W ∈ family},
        W.1.carrierSet)
      rw [Set.mem_iUnion]
      exact ⟨⟨V, hV⟩, hx⟩
    have hSUnion : S ≤ unionCarrier :=
      hFamilySup.2 unionCarrier hFamilyLeUnion
    have hAUnion : A ⊆ unionSet :=
      Set.Subset.trans hAU (Set.Subset.trans hUS hSUnion)
    let cover : Set (Set D.carrier) :=
      ScottOpenCarrier.carrierSet '' family
    have hCoverOpen : ∀ V ∈ cover, Chapter2.ScottOpen V := by
      intro V hV
      rcases hV with ⟨W, hW, rfl⟩
      exact W.scott_open
    have hACover : A ⊆ ⋃₀ cover := by
      intro x hx
      have hxUnion := hAUnion hx
      change x ∈ (⋃ W : {W : ScottOpenCarrier D // W ∈ family},
        W.1.carrierSet) at hxUnion
      rw [Set.mem_iUnion] at hxUnion
      rcases hxUnion with ⟨V, hxV⟩
      exact Set.mem_sUnion_of_mem hxV ⟨V.1, V.2, rfl⟩
    rcases hA.1 cover hCoverOpen hACover with
      ⟨finiteCover, hFiniteSub, hFinite, hFiniteCovers⟩
    have hCoverWitness :
        ∀ C ∈ finiteCover, ∃ V ∈ family, V.carrierSet = C := by
      intro C hC
      rcases hFiniteSub hC with ⟨V, hV, rfl⟩
      exact ⟨V, hV, rfl⟩
    let selected :
        {C : Set D.carrier // C ∈ finiteCover} → ScottOpenCarrier D := fun C =>
      Classical.choose (hCoverWitness C.1 C.2)
    have selected_mem :
        ∀ C : {C : Set D.carrier // C ∈ finiteCover}, selected C ∈ family := by
      intro C
      exact (Classical.choose_spec (hCoverWitness C.1 C.2)).1
    have selected_set :
        ∀ C : {C : Set D.carrier // C ∈ finiteCover},
          (selected C).carrierSet = C.1 := by
      intro C
      exact (Classical.choose_spec (hCoverWitness C.1 C.2)).2
    let selectedFamily : Set (ScottOpenCarrier D) := Set.range selected
    letI : Finite {C : Set D.carrier // C ∈ finiteCover} :=
      Set.finite_coe_iff.mp hFinite
    have hSelectedFinite : selectedFamily.Finite := Set.finite_range selected
    have hSelectedSub : selectedFamily ⊆ family := by
      intro V hV
      rcases hV with ⟨C, rfl⟩
      exact selected_mem C
    rcases Chapter2.DirectedSet.exists_upper_finite
        hFamilyDirected hSelectedFinite hSelectedSub with
      ⟨V, hVFamily, hSelectedLe⟩
    refine ⟨V, hVFamily, Set.Subset.trans hOA ?_⟩
    intro x hxA
    rcases Set.mem_sUnion.mp (hFiniteCovers hxA) with ⟨C, hC, hxC⟩
    let C' : {B : Set D.carrier // B ∈ finiteCover} := ⟨C, hC⟩
    have hxSelected : x ∈ (selected C').carrierSet := by
      rw [selected_set C']
      exact hxC
    exact hSelectedLe (selected C') ⟨C', rfl⟩ hxSelected

/-- Proposition 4.2.15, PDF text: `κD` is continuous and way-below in `κD`
and `σD` is characterized by the stated open/compact-saturated witnesses.  The
PDF supplies the finite-upper-set proof.  The dcpo component is reused from
Proposition 4.2.14 and the set-level final clause is definitional; the remaining
formal proof obligations are classified as automation exhaustion. -/
theorem prop_4_2_15_scott_compactness_criteria
    (D : OrderedDomain.{u}) (hDcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) :
    (Chapter3.IsDcpo (CompactSaturatedCarrier D) ∧
      Chapter3.IsContinuousDomain (CompactSaturatedCarrier D)) ∧
      (∀ A B : CompactSaturatedCarrier D,
        CompactSaturatedWayBelow D A B ↔
          CompactSaturatedWayBelowByOpen D A B) ∧
        (∀ O U : ScottOpenCarrier D,
          ScottOpenWayBelow D O U ↔ ScottOpenWayBelowByCompactCarrier D O U) ∧
        ∀ O U : Set D.carrier,
          ScottOpenWayBelowByCompact D O U ↔
            Chapter2.ScottOpen O ∧ Chapter2.ScottOpen U ∧
              ∃ A : Set D.carrier, IsCompactSaturated D A ∧ O ⊆ A ∧ A ⊆ U := by
  have h14 := prop_4_2_14_compact_saturated_scott_open_filters D hDcpo hD
  refine ⟨⟨h14.1, ?_⟩, ?_, ?_, ?_⟩
  · exact compactSaturatedCarrier_isContinuous D hDcpo hD
  · exact compactSaturatedWayBelow_iff_open D hDcpo hD
  · exact scottOpenWayBelow_iff_compactCarrier D hD
  · intro O U
    rfl

/-- Coherence for continuous domains: compact saturated sets are closed under binary intersections. -/
def IsCoherentDomain (D : OrderedDomain.{u}) : Prop :=
  ∀ A B : Set D.carrier,
    IsCompactSaturated D A → IsCompactSaturated D B → IsCompactSaturated D (A ∩ B)

/-- Proposition 4.2.16's open-lattice condition, stated with the actual
way-below relation in `σD`. -/
def ScottOpenIntersectionWayBelowProperty (D : OrderedDomain.{u}) : Prop :=
  ∀ O U₁ U₂ : ScottOpenCarrier D,
    ScottOpenWayBelow D O U₁ →
      ScottOpenWayBelow D O U₂ →
        ScottOpenWayBelow D O (ScottOpenCarrier.inter D U₁ U₂)

/-- Proposition 4.2.16, PDF text: coherence of a continuous domain is
equivalent to binary-intersection stability for way-below Scott-open
approximations.  The proof is registered as local proof debt. -/
theorem prop_4_2_16_coherence_open_neighborhoods
    (D : OrderedDomain.{u}) (hDcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) :
    IsCoherentDomain D ↔ ScottOpenIntersectionWayBelowProperty D := by
  admit

/-- Proposition 4.2.17, PDF text: an algebraic domain is coherent iff its
compact basis is mub-complete and has finite minimal-upper-bound sets.  The
proof is registered as local proof debt. -/
theorem prop_4_2_17_algebraic_coherence_mub_complete
    (D : OrderedDomain.{u}) (hDcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsAlgebraicDomain D.carrier) :
    IsCoherentDomain D ↔
      IsMubComplete (CompactBasisDomain D) ∧
        HasFiniteMinimalUpperBounds (CompactBasisDomain D) := by
  admit

/-- Minimal upper bounds of a finite set are contained in its mub-closure. -/
theorem minimalUpperBounds_subset_mubClosure
    (D : OrderedDomain.{u}) {A : Set D.carrier} (hA : A.Finite) :
    MinimalUpperBounds D A ⊆ MubClosure D A := by
  intro m hm
  rw [MubClosure]
  intro C hC
  exact hC.2 A hA hC.1 hm

/-- Finite mub-closure gives the finite-minimal-upper-bound condition used in
the algebraic coherence characterization. -/
theorem hasFiniteMinimalUpperBounds_of_hasFiniteMubProperty
    (D : OrderedDomain.{u}) (hD : HasFiniteMubProperty D) :
    HasFiniteMinimalUpperBounds D := by
  intro A hA
  constructor
  · exact (hD.2 A hA).subset (minimalUpperBounds_subset_mubClosure D hA)
  · intro u hu
    exact hD.1 A hA u hu

/-- Compact-basis bifinite domains satisfy the coherence conclusion of
Theorem 4.2.18. -/
theorem coherent_of_hasBifiniteCompactBasis
    (D : OrderedDomain.{u}) (hDcpo : Chapter3.IsDcpo D.carrier)
    (hD : HasBifiniteCompactBasis D) :
    IsCoherentDomain D := by
  exact
    (prop_4_2_17_algebraic_coherence_mub_complete D hDcpo hD.1).2
      ⟨hD.2.1.1,
        hasFiniteMinimalUpperBounds_of_hasFiniteMubProperty
          (CompactBasisDomain D) hD.2.1⟩

/-- Theorem 4.2.18, PDF text: FS-domains and bifinite domains are coherent.
The FS-domain coherence proof remains registered as local proof debt; the
bifinite half is derived from Proposition 4.2.17 and the finite-mub support
lemmas above. -/
theorem theorem_4_2_18_fs_bifinite_coherent
    (D : OrderedDomain.{u}) :
    (IsFSObject D → IsCoherentDomain D) ∧
      (Chapter3.IsDcpo D.carrier → HasBifiniteCompactBasis D → IsCoherentDomain D) := by
  constructor
  · intro _hD
    admit
  · intro hDcpo hD
    exact coherent_of_hasBifiniteCompactBasis D hDcpo hD

/-- Principal upper set `↑x`. -/
def PrincipalUpperSet (D : OrderedDomain.{u}) (x : D.carrier) : Set D.carrier :=
  Chapter2.upperClosure ({x} : Set D.carrier)

/-- Definition 4.2.19 support: the Lawson subbasis, consisting of Scott opens
and complements of principal upper sets. -/
def LawsonSubbasis (D : OrderedDomain.{u}) : Set (Set D.carrier) :=
  {U : Set D.carrier | Chapter2.ScottOpen U} ∪
    {U : Set D.carrier | ∃ x : D.carrier, U = (PrincipalUpperSet D x)ᶜ}

/-- A collection of subsets satisfying the open-set axioms. -/
def IsTopologyOn {α : Type u} (T : Set (Set α)) : Prop :=
  Set.univ ∈ T ∧
    (∀ U V : Set α, U ∈ T → V ∈ T → U ∩ V ∈ T) ∧
      ∀ S : Set (Set α), S ⊆ T → ⋃₀ S ∈ T

/-- Definition 4.2.19: the Lawson topology generated by the Lawson subbasis. -/
def LawsonTopology (D : OrderedDomain.{u}) : Set (Set D.carrier) :=
  {U | ∀ T : Set (Set D.carrier), IsTopologyOn T → LawsonSubbasis D ⊆ T → U ∈ T}

/-- The generating subbasis is contained in the Lawson topology. -/
theorem lawsonSubbasis_subset_topology (D : OrderedDomain.{u}) :
    LawsonSubbasis D ⊆ LawsonTopology D := by
  intro U hU T _hT hsub
  exact hsub hU

/-- The generated Lawson collection is a topology. -/
theorem lawsonTopology_isTopology (D : OrderedDomain.{u}) :
    IsTopologyOn (LawsonTopology D) := by
  constructor
  · intro T hT _hsub
    exact hT.1
  constructor
  · intro U V hU hV T hT hsub
    exact hT.2.1 U V (hU T hT hsub) (hV T hT hsub)
  · intro S hS T hT hsub
    exact hT.2.2 S (by
      intro U hU
      exact hS hU T hT hsub)

/-- The Lawson topology is the least topology containing its subbasis. -/
theorem lawsonTopology_least
    (D : OrderedDomain.{u}) {T : Set (Set D.carrier)}
    (hT : IsTopologyOn T) (hsub : LawsonSubbasis D ⊆ T) :
    LawsonTopology D ⊆ T := by
  intro U hU
  exact hU T hT hsub

/-- Definition 4.2.19: Lawson topology generated by Scott opens and complements
of principal upper sets. -/
def def_4_2_19_lawson_topology (D : OrderedDomain.{u}) : Set (Set D.carrier) :=
  LawsonTopology D

/-- Hausdorff separation for the generated Lawson topology. -/
def IsLawsonHausdorff (D : OrderedDomain.{u}) : Prop :=
  ∀ x y : D.carrier, x ≠ y →
    ∃ U ∈ LawsonTopology D, ∃ V ∈ LawsonTopology D,
      x ∈ U ∧ y ∈ V ∧ Disjoint U V

/-- Lawson compactness for covers by generated Lawson-open sets. -/
def IsLawsonCompact (D : OrderedDomain.{u}) : Prop :=
  ∀ cover : Set (Set D.carrier),
    cover ⊆ LawsonTopology D →
      Set.univ ⊆ ⋃₀ cover →
        ∃ finiteCover : Set (Set D.carrier),
          finiteCover ⊆ cover ∧ finiteCover.Finite ∧ Set.univ ⊆ ⋃₀ finiteCover

/-- Every Lawson-open set has the PDF form `O \ A`, with `O` Scott-open and `A`
Scott-compact saturated. -/
def LawsonOpenHasScottMinusCompactSaturatedForm (D : OrderedDomain.{u}) : Prop :=
  ∀ W : Set D.carrier, W ∈ LawsonTopology D →
    ∃ O A : Set D.carrier,
      Chapter2.ScottOpen O ∧ IsCompactSaturated D A ∧ W = O \ A

/-- The converse useful closure property: all Scott-minus-compact-saturated sets
are Lawson-open. -/
def ScottMinusCompactSaturatedOpen (D : OrderedDomain.{u}) : Prop :=
  ∀ O A : Set D.carrier,
    Chapter2.ScottOpen O → IsCompactSaturated D A → O \ A ∈ LawsonTopology D

/-- Proposition 4.2.20(1-2), PDF text: Lawson topology on a continuous domain
is Hausdorff; Lawson opens have Scott-minus-compact-saturated form; and Lawson
compactness is equivalent to coherence.  The proof is registered as local proof
debt. -/
theorem prop_4_2_20_lawson_topology_properties
    (D : OrderedDomain.{u}) (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) :
    IsLawsonHausdorff D ∧
      LawsonOpenHasScottMinusCompactSaturatedForm D ∧
        ScottMinusCompactSaturatedOpen D ∧
          (IsLawsonCompact D ↔ IsCoherentDomain D) := by
  admit

/-- Proposition 4.2.20(3), PDF text: continuous retracts of Lawson-compact
continuous domains are Lawson-compact and continuous.  The proof is registered
as local proof debt. -/
theorem prop_4_2_20_lawson_compact_retract
    (D E : OrderedDomain.{u}) (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) (hCompact : IsLawsonCompact D)
    (hRetract : IsContinuousRetractOf E D) :
    IsLawsonCompact E ∧ Chapter3.IsDcpo E.carrier ∧
      Chapter3.IsContinuousDomain E.carrier := by
  admit

/-- Proposition 4.2.20, PDF text: Lawson-topology separation,
Scott-minus-compact-saturated opens, compactness/coherence, and retract
stability.  The combined statement is assembled directly from the D-only
Lawson-properties component and the retract-stability component. -/
theorem prop_4_2_20_lawson_topology_compactness
    (D E : OrderedDomain.{u}) (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) (hRetract : IsContinuousRetractOf E D) :
    IsLawsonHausdorff D ∧
      LawsonOpenHasScottMinusCompactSaturatedForm D ∧
      ScottMinusCompactSaturatedOpen D ∧
        (IsLawsonCompact D ↔ IsCoherentDomain D) ∧
          (IsLawsonCompact D →
            IsLawsonCompact E ∧ Chapter3.IsDcpo E.carrier ∧
              Chapter3.IsContinuousDomain E.carrier) := by
  rcases prop_4_2_20_lawson_topology_properties D hDdcpo hD with
    ⟨hHausdorff, hForm, hScottMinus, hCompactIff⟩
  refine ⟨hHausdorff, hForm, hScottMinus, hCompactIff, ?_⟩
  intro hCompact
  exact prop_4_2_20_lawson_compact_retract D E hDdcpo hD hCompact hRetract

end Chapter4
end AbramskyJung

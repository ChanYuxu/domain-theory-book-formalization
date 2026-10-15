import Practice.DomainTheory.Chapter07.Section72.Spectral

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.2: continuous and coherent algebraic domain dualities

This module follows a coherent dependency cluster inside the textbook section.
The stable public import remains `Practice.DomainTheory.Chapter07.Section72`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

/-- The approximation closure `↓↓A` used in the proof of Proposition 7.2.27:
the elements way below some member of `A`.  This is not the ordinary order
lower closure `↓A`. -/
def WayBelowLowerClosureOfSet
    {D : Type u} [Preorder D] (A : Set D) : Set D :=
  {x : D | ∃ a ∈ A, x ≪ a}

/-- Closed subsets of a Scott topology are Scott-closed in the order-theoretic
sense used in Chapter 2. -/
theorem scottClosed_of_isClosed_scottTopology
    {D : Type u} [Preorder D] {A : Set D}
    (hA : IsClosed (ScottTopologySpace D) A) :
    Chapter2.ScottClosed A := by
  change Chapter2.ScottOpen Aᶜ at hA
  simpa [Chapter2.ScottOpen] using hA

/-- For an irreducible Scott-closed set `A` in a continuous domain, `↓↓A` is
directed.  This formalizes the central directedness argument in the textbook
proof of Proposition 7.2.27. -/
theorem wayBelowLowerClosureOfSet_directed
    {D : Type u} [Preorder D]
    (hCont : Chapter2.IsContinuousDomain D) {A : Set D}
    (hA : IsIrreducibleClosed (ScottTopologySpace D) A) :
    Chapter2.DirectedSet (WayBelowLowerClosureOfSet A) := by
  constructor
  · rcases hA.2.1 with ⟨a, haA⟩
    rcases (Chapter2.continuous_wayBelowLower_directed hCont a).1 with
      ⟨b, hba⟩
    exact ⟨b, ⟨a, haA, hba⟩⟩
  · intro x hxB y hyB
    rcases hxB with ⟨a, haA, hxa⟩
    rcases hyB with ⟨a', ha'A, hya'⟩
    let U : Set D := Chapter2.wayBelowUpper x
    let V : Set D := Chapter2.wayBelowUpper y
    have hUOpen : Chapter2.ScottOpen U :=
      Chapter2.scottOpen_wayBelowUpper hCont x
    have hVOpen : Chapter2.ScottOpen V :=
      Chapter2.scottOpen_wayBelowUpper hCont y
    have hMeet : ∃ z : D, z ∈ A ∧ z ∈ U ∧ z ∈ V :=
      irreducibleClosed_exists_mem_open_inter
        (X := ScottTopologySpace D) hA hUOpen hVOpen
        ⟨a, haA, hxa⟩ ⟨a', ha'A, hya'⟩
    rcases hMeet with ⟨z, hzA, hzx, hzy⟩
    have hInterOpen : Chapter2.ScottOpen (U ∩ V) :=
      Chapter2.scottOpen_inter hUOpen hVOpen
    have hLowerDirected :=
      Chapter2.continuous_wayBelowLower_directed hCont z
    have hLowerSup := Chapter2.continuous_wayBelowLower_isSup hCont z
    have hExists : ∃ b ∈ Chapter2.wayBelowLower z, b ∈ U ∩ V := by
      by_contra hNone
      have hSub : Chapter2.wayBelowLower z ⊆ (U ∩ V)ᶜ := by
        intro b hb hbInter
        exact hNone ⟨b, hb, hbInter⟩
      have hzCompl : z ∈ (U ∩ V)ᶜ :=
        hInterOpen.2 hLowerDirected hSub hLowerSup
      exact hzCompl ⟨hzx, hzy⟩
    rcases hExists with ⟨b, hbz, hbx, hby⟩
    exact ⟨b, ⟨z, hzA, hbz⟩,
      Chapter2.prop_2_2_2_1 hbx, Chapter2.prop_2_2_2_1 hby⟩

/-- The supremum of `↓↓A` is a generic point for an irreducible Scott-closed
set `A`. -/
theorem irreducibleClosed_eq_pointClosure_of_wayBelowLowerClosure_isSup
    {D : Type u} [Preorder D]
    (hCont : Chapter2.IsContinuousDomain D) {A : Set D} {s : D}
    (hA : IsIrreducibleClosed (ScottTopologySpace D) A)
    (hBDirected : Chapter2.DirectedSet (WayBelowLowerClosureOfSet A))
    (hs : Chapter2.IsSup (WayBelowLowerClosureOfSet A) s) :
    A = PointClosure (ScottTopologySpace D) s := by
  have hAClosed : Chapter2.ScottClosed A :=
    scottClosed_of_isClosed_scottTopology hA.1
  apply Set.Subset.antisymm
  · intro a haA
    have has : a ≤ s :=
      (Chapter2.continuous_wayBelowLower_isSup hCont a).2 s (by
        intro b hba
        exact hs.1 ⟨a, haA, hba⟩)
    exact (scottTopologySpace_specialization_iff_order a s).2 has
  · intro x hxs
    have hxsOrder : x ≤ s :=
      (scottTopologySpace_specialization_iff_order x s).1 hxs
    have hBSubA : WayBelowLowerClosureOfSet A ⊆ A := by
      intro b hbB
      rcases hbB with ⟨a, haA, hba⟩
      exact hAClosed.1 haA (Chapter2.prop_2_2_2_1 hba)
    have hsA : s ∈ A := hAClosed.2 hBDirected hBSubA hs
    exact hAClosed.1 hsA hxsOrder

/-- Proof data for Proposition 7.2.27: irreducible Scott-closed sets have
directed lower closures and hence generic points. -/
structure ContinuousDomainScottSobrietyData (D : Type u) [PartialOrder D] : Prop where
  dcpo : Chapter2.IsDcpo D
  continuous : Chapter2.IsContinuousDomain D
  directed_lower_closure :
    ∀ A : Set D,
      IsIrreducibleClosed (ScottTopologySpace D) A →
        Chapter2.DirectedSet (WayBelowLowerClosureOfSet A)
  generic_point :
    ∀ A : Set D,
      IsIrreducibleClosed (ScottTopologySpace D) A →
        ∃ s : D,
          Chapter2.IsSup (WayBelowLowerClosureOfSet A) s ∧
            A = PointClosure (ScottTopologySpace D) s
  sober : IsSober (ScottTopologySpace D)

/-- The complete proof package behind Proposition 7.2.27. -/
theorem continuousDomainScottSobrietyData
    (D : Type u) [PartialOrder D]
    (hDcpo : Chapter2.IsDcpo D)
    (hCont : Chapter2.IsContinuousDomain D) :
    ContinuousDomainScottSobrietyData D := by
  have hGeneric :
      ∀ A : Set D,
        IsIrreducibleClosed (ScottTopologySpace D) A →
          ∃ s : D,
            Chapter2.IsSup (WayBelowLowerClosureOfSet A) s ∧
              A = PointClosure (ScottTopologySpace D) s := by
    intro A hA
    have hDirected := wayBelowLowerClosureOfSet_directed hCont hA
    rcases hDcpo (WayBelowLowerClosureOfSet A) hDirected with ⟨s, hs⟩
    exact ⟨s, hs,
      irreducibleClosed_eq_pointClosure_of_wayBelowLowerClosure_isSup
        hCont hA hDirected hs⟩
  refine
    { dcpo := hDcpo
      continuous := hCont
      directed_lower_closure := fun _A hA =>
        wayBelowLowerClosureOfSet_directed hCont hA
      generic_point := hGeneric
      sober := ?_ }
  refine ⟨scottTopologySpace_t0_of_antisymmetric (D := D)
    (fun {x y} hxy hyx => le_antisymm hxy hyx), ?_⟩
  change ∀ A : Set D, IsIrreducibleClosed (ScottTopologySpace D) A →
    ∃ x : D, A = PointClosure (ScottTopologySpace D) x
  intro A hA
  rcases hGeneric A hA with ⟨s, _hs, hEq⟩
  exact ⟨s, hEq⟩

/-- Proposition 7.2.27 PDF-facing statement. -/
theorem prop_7_2_27_continuous_domains_sober
    (D : Type u) [PartialOrder D] :
    Chapter2.IsDcpo D →
      Chapter2.IsContinuousDomain D →
      IsSober (ScottTopologySpace D) := by
  intro hDcpo hCont
  exact (continuousDomainScottSobrietyData D hDcpo hCont).sober

/-- The Scott-open lattice of a continuous dcpo is prime-continuous.  The
prime approximants used here are the basic opens `wayBelowUpper x` from the
proof printed before Theorem 7.2.28. -/
theorem scottOpenLattice_primeContinuous
    (D : ContinuousDcpoObject.{u}) :
    IsPrimeContinuousLattice
      (OpenSet (@ScottTopologySpace D.carrier D.preorder)) := by
  let X : Space.{u} := @ScottTopologySpace D.carrier D.preorder
  intro O
  apply le_antisymm
  · change ∀ x : D.carrier, x ∈ O.1 →
      x ∈ (sSup {W : OpenSet X | PrimeWayBelow W O}).1
    intro x hxO
    have hSupported :=
      Chapter2.prop_2_3_6_open_supported_by_wayBelow D.continuous O.2
    have hxUnion := (Set.ext_iff.mp hSupported x).mp hxO
    rcases Set.mem_iUnion.mp hxUnion with ⟨y, hyUnion⟩
    rcases Set.mem_iUnion.mp hyUnion with ⟨hyO, hxy⟩
    let V : OpenSet X :=
      ⟨@Chapter2.wayBelowUpper D.carrier D.preorder y,
        Chapter2.scottOpen_wayBelowUpper D.continuous y⟩
    have hPrime : PrimeWayBelow V O := by
      intro A hOA
      have hySup : y ∈ (sSup A : OpenSet X).1 := hOA hyO
      rcases (OpenSet.mem_sSup_iff X A y).1 hySup with ⟨U, hUA, hyU⟩
      refine ⟨U, hUA, ?_⟩
      intro z hyz
      exact Chapter2.scottOpen_upper U.2 hyU
        (Chapter2.prop_2_2_2_1 hyz)
    exact (show V ≤ sSup {W : OpenSet X | PrimeWayBelow W O} from
      le_sSup hPrime) hxy
  · exact sSup_le (by
      intro V hPrime
      rcases hPrime {O} (by simp) with ⟨W, hW, hVW⟩
      have hWO : W = O := by simpa using hW
      simpa [hWO] using hVW)

/-- The complete-distributivity law implies ordinary continuity by restriction
to directed families. -/
theorem continuousCompleteLattice_of_completeChoice
    (L : Type u) [CompleteLattice L]
    (hComplete : CompleteChoiceMeetJoinLaw.{u, u} L) :
    IsContinuousCompleteLattice L := by
  apply (theorem_7_1_1_complete_lattice_continuity_distributivity L).2
  intro ι A _hDirected
  exact hComplete ι A

/-- Prime-continuity implies the frame distributivity law. -/
theorem frameDistributive_of_primeContinuous
    (L : Type u) [CompleteLattice L]
    (hPrimeContinuous : IsPrimeContinuousLattice L) :
    IsFrameDistributive L := by
  intro x S
  apply le_antisymm
  · rw [hPrimeContinuous (x ⊓ sSup S)]
    apply sSup_le
    intro p hp
    have hpX : PrimeWayBelow p x := by
      intro A hxA
      exact hp A ((inf_le_left : x ⊓ sSup S ≤ x).trans hxA)
    have hpSup : PrimeWayBelow p (sSup S) := by
      intro A hSupA
      exact hp A ((inf_le_right : x ⊓ sSup S ≤ sSup S).trans hSupA)
    have hpx : p ≤ x := by
      rcases hpX {x} (by simp) with ⟨a, ha, hpa⟩
      have hax : a = x := by simpa using ha
      simpa [hax] using hpa
    rcases hpSup S le_rfl with ⟨s, hsS, hps⟩
    exact (le_inf hpx hps).trans (le_sSup ⟨s, hsS, rfl⟩)
  · exact sSup_le (by
      intro y hy
      rcases hy with ⟨s, hsS, rfl⟩
      exact inf_le_inf le_rfl (le_sSup hsS))

/-- Complete distributivity supplies the frame and spatiality properties used
by the lattice-side Stone unit. -/
theorem spatial_of_completeChoice
    (L : Type u) [CompleteLattice L]
    (hComplete : CompleteChoiceMeetJoinLaw.{u, u} L) :
    IsSpatialLattice L := by
  have hPrime : IsPrimeContinuousLattice L :=
    (theorem_7_1_3_prime_continuous_iff_completely_distributive L).2 hComplete
  have hContinuous := (continuousCompleteLattice_of_completeChoice L hComplete).2
  exact lemma_7_2_15_distributive_continuous_lattices_spatial
    L hContinuous (frameDistributive_of_primeContinuous L hPrime)

/-- Concrete `Omega` object map for Theorem 7.2.28. -/
def continuousDcpoOmega (D : ContinuousDcpoObject.{u}) :
    CompleteDistributiveLatticeObject.{u} where
  carrier := OpenSet (@ScottTopologySpace D.carrier D.preorder)
  lattice := OpenSet.completeLattice _
  complete_distributive :=
    (theorem_7_1_3_prime_continuous_iff_completely_distributive _).1
      (scottOpenLattice_primeContinuous D)

/-- The direct, fully proved half of the Scott-open basis assertion in the
proof of Theorem 7.2.28. -/
theorem scottOpenWayBelowUnionBasis_of_continuous
    (D : ContinuousDcpoObject.{u}) :
    ScottOpenWayBelowUnionBasis D := by
  intro O hO
  exact Chapter2.prop_2_3_6_open_supported_by_wayBelow D.continuous hO

/-- The point-dcpo part of Theorem 7.2.28.  This isolates precisely the source's
successive prime-interpolation construction: points ordered by filter inclusion
form a continuous dcpo, `F' << F` iff `inf F'` belongs to `F`, and the generated
point topology is exactly the Scott topology.

The surrounding object maps, complete-distributivity proof, Stone units, and
sobriety argument are formalized independently below. -/
structure CompleteDistributivePointDcpoData
    (L : CompleteDistributiveLatticeObject.{u}) : Prop where
  dcpo : @Chapter2.IsDcpo (@Point L.carrier L.lattice) (PointFilterPreorder L)
  continuous :
    @Chapter2.IsContinuousDomain (@Point L.carrier L.lattice) (PointFilterPreorder L)
  way_below_characterization : PointFilterWayBelowMembershipCharacterization L
  topology_recovered : PointScottTopologyRecovered L

/-- Source-proof boundary for the interpolating completely-prime-filter
construction in Theorem 7.2.28. -/
theorem completeDistributivePointDcpoData
    (L : CompleteDistributiveLatticeObject.{u}) :
    CompleteDistributivePointDcpoData L := by
  sorry

/-- Concrete `pt` object map for Theorem 7.2.28. -/
def completeDistributivePt
    (L : CompleteDistributiveLatticeObject.{u}) :
    ContinuousDcpoObject.{u} where
  carrier := Point L.carrier
  preorder := PointFilterPreorder L
  antisymm := by
    intro F G hFG hGF
    apply Subtype.ext
    exact Set.Subset.antisymm hFG hGF
  dcpo := (completeDistributivePointDcpoData L).dcpo
  continuous := (completeDistributivePointDcpoData L).continuous

/-- Point-filter inclusion is antisymmetric. -/
@[reducible]
def pointFilterPartialOrder
    (L : CompleteDistributiveLatticeObject.{u}) :
    PartialOrder (@Point L.carrier L.lattice) where
  le := (PointFilterPreorder L).le
  le_refl := (PointFilterPreorder L).le_refl
  le_trans := (PointFilterPreorder L).le_trans
  le_antisymm := by
    intro F G hFG hGF
    apply Subtype.ext
    exact Set.Subset.antisymm hFG hGF

/-- Dual-equivalence data for Theorem 7.2.28, with the restricted `Omega` and
`pt` functors and the proof obligations highlighted in the book proof. -/
structure ContCompletelyDistributiveDualityData : Type (u + 1) where
  duality :
    DualEquivalenceData
      ContinuousDcpoObject.{u}
      CompleteDistributiveLatticeObject.{u}
  omega :
    ContinuousDcpoObject.{u} → CompleteDistributiveLatticeObject.{u}
  pt :
    CompleteDistributiveLatticeObject.{u} → ContinuousDcpoObject.{u}
  omega_is_scott_opens :
    ∀ D : ContinuousDcpoObject.{u},
      ScottOpenCompleteDistributiveLatticePresentation D (omega D)
  pt_is_points :
    ∀ L : CompleteDistributiveLatticeObject.{u},
      PointContinuousDcpoPresentation L (pt L)
  omega_eq_left : ∀ D : ContinuousDcpoObject.{u}, omega D = duality.left D
  pt_eq_right : ∀ L : CompleteDistributiveLatticeObject.{u}, pt L = duality.right L
  omega_complete_distributive :
    ∀ D : ContinuousDcpoObject.{u},
      @CompleteChoiceMeetJoinLaw.{u, u} (omega D).carrier (omega D).lattice
  omega_scott_open_wayBelow_basis :
    ∀ D : ContinuousDcpoObject.{u}, ScottOpenWayBelowUnionBasis D
  pt_dcpo :
    ∀ L : CompleteDistributiveLatticeObject.{u},
      @Chapter2.IsDcpo (pt L).carrier (pt L).preorder
  pt_continuous_domain :
    ∀ L : CompleteDistributiveLatticeObject.{u},
      @Chapter2.IsContinuousDomain (pt L).carrier (pt L).preorder
  pt_scott_sober :
    ∀ L : CompleteDistributiveLatticeObject.{u},
      IsSober (@ScottTopologySpace (pt L).carrier (pt L).preorder)
  way_below_filter_membership_characterization :
    ∀ L : CompleteDistributiveLatticeObject.{u},
      PointFilterWayBelowMembershipCharacterization L
  scott_topology_recovered :
    ∀ L : CompleteDistributiveLatticeObject.{u},
      PointScottTopologyRecovered L

/-- Theorem 7.2.28 PDF-facing statement. -/
theorem theorem_7_2_28_cont_completely_distributive_duality :
    Nonempty (ContCompletelyDistributiveDualityData.{u}) := by
  refine ⟨{
    duality := {
      left := continuousDcpoOmega
      right := completeDistributivePt
      unit_isomorphism :=
        ∀ D : ContinuousDcpoObject.{u},
          Function.Bijective
            (stoneUnitPoint (@ScottTopologySpace D.carrier D.preorder))
      unit_isomorphism_holds := fun D =>
        stoneUnitPoint_bijective_of_sober _ (by
          letI : PartialOrder D.carrier := D.partialOrder
          exact prop_7_2_27_continuous_domains_sober
            D.carrier D.dcpo D.continuous)
      counit_isomorphism :=
        ∀ L : CompleteDistributiveLatticeObject.{u},
          Function.Bijective
            (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun
      counit_isomorphism_holds := fun L =>
        stoneEpsilon_bijective_of_spatial {
          carrier := L.carrier
          lattice := L.lattice
          spatial := spatial_of_completeChoice L.carrier L.complete_distributive } }
    omega := continuousDcpoOmega
    pt := completeDistributivePt
    omega_is_scott_opens := ?_
    pt_is_points := ?_
    omega_eq_left := fun _ => rfl
    pt_eq_right := fun _ => rfl
    omega_complete_distributive := fun D => (continuousDcpoOmega D).complete_distributive
    omega_scott_open_wayBelow_basis := scottOpenWayBelowUnionBasis_of_continuous
    pt_dcpo := fun L => (completeDistributivePointDcpoData L).dcpo
    pt_continuous_domain := fun L => (completeDistributivePointDcpoData L).continuous
    pt_scott_sober := ?_
    way_below_filter_membership_characterization := fun L =>
      (completeDistributivePointDcpoData L).way_below_characterization
    scott_topology_recovered := fun L =>
      (completeDistributivePointDcpoData L).topology_recovered }⟩
  · intro D
    exact {
      presentation := {
        carrier := OpenSet (@ScottTopologySpace D.carrier D.preorder)
        lattice := OpenSet.completeLattice _
        toOpen := fun U => U
        ofOpen := fun U => U
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        order_compatible := fun _ _ => Iff.rfl }
      carrier_equiv := Equiv.refl _
      order_agrees := fun _ _ => Iff.rfl }
  · intro L
    exact { carrier_equiv := Equiv.refl _, order_agrees := fun _ _ => Iff.rfl }
  · intro L
    letI : PartialOrder (@Point L.carrier L.lattice) := pointFilterPartialOrder L
    exact prop_7_2_27_continuous_domains_sober
      (@Point L.carrier L.lattice)
      (completeDistributivePointDcpoData L).dcpo
      (completeDistributivePointDcpoData L).continuous

/-- The compact-open lattice object in Theorem 7.2.29, identified with actual
compact-open subsets of the Scott space of the coherent algebraic domain. -/
structure CoherentAlgebraicCompactOpenLatticePresentation
    (D : CoherentAlgebraicDomainObject.{u})
    (L : FiniteJoinPrimeGeneratedLatticeObject.{u}) where
  representation : @CompactOpenLatticeRepresentation L.carrier L.lattice D.object
  order_agrees :
    ∀ a b : L.carrier,
      @LE.le L.carrier L.lattice.toPreorder.toLE a b ↔
        ((@CompactOpenLatticeRepresentation.toCompactOpen
          L.carrier L.lattice D.object representation) a).1 ⊆
          ((@CompactOpenLatticeRepresentation.toCompactOpen
            L.carrier L.lattice D.object representation) b).1

/-- The spectrum-domain object in Theorem 7.2.29, identified with prime filters
of the finite-join-prime-generated lattice. -/
structure FiniteJoinPrimeSpectrumDomainPresentation
    (L : FiniteJoinPrimeGeneratedLatticeObject.{u})
    (D : CoherentAlgebraicDomainObject.{u}) where
  carrier_equiv :
    D.object.carrier ≃
      {F : Set L.carrier // @IsPrimeFilterOfDistributiveLattice L.carrier L.lattice F}
  order_agrees :
    ∀ x y : D.object.carrier,
      @LE.le D.object.carrier D.object.preorder.toLE x y ↔
        (carrier_equiv x).1 ⊆ (carrier_equiv y).1

/-- Dual-equivalence data for Theorem 7.2.29: Theorem 7.2.26 restricts to
coherent algebraic domains and lattices generated by finite joins of
`∨`-prime elements. -/
structure CoherentAlgebraicFiniteJoinPrimeDualityData : Type (u + 1) where
  duality :
    DualEquivalenceData
      CoherentAlgebraicDomainObject.{u}
      FiniteJoinPrimeGeneratedLatticeObject.{u}
  compact_open_lattice :
    CoherentAlgebraicDomainObject.{u} → FiniteJoinPrimeGeneratedLatticeObject.{u}
  spectrum_domain :
    FiniteJoinPrimeGeneratedLatticeObject.{u} → CoherentAlgebraicDomainObject.{u}
  compact_open_lattice_presentation :
    ∀ D : CoherentAlgebraicDomainObject.{u},
      CoherentAlgebraicCompactOpenLatticePresentation D (compact_open_lattice D)
  spectrum_domain_presentation :
    ∀ L : FiniteJoinPrimeGeneratedLatticeObject.{u},
      FiniteJoinPrimeSpectrumDomainPresentation L (spectrum_domain L)
  compact_open_eq_left :
    ∀ D : CoherentAlgebraicDomainObject.{u}, compact_open_lattice D = duality.left D
  spectrum_eq_right :
    ∀ L : FiniteJoinPrimeGeneratedLatticeObject.{u}, spectrum_domain L = duality.right L
  cuts_down_theorem_7_2_26 : Prop
  ideal_completion_complete_distributive : Prop
  principal_join_prime_ideals_completely_prime : Prop

/-- Theorem 7.2.29 PDF-facing statement.

The PDF proves this by restricting the spectral/distributive-lattice duality of
Theorem 7.2.26 to coherent algebraic domains and lattices with finite joins of
join-primes.  The restriction and its compatibility with the bundled functors
have not yet been implemented.  This is therefore source-proved proof debt, not
a book-omission boundary. -/
theorem theorem_7_2_29_coherent_algebraic_domain_duality :
    Nonempty (CoherentAlgebraicFiniteJoinPrimeDualityData.{u}) := by
  sorry

/-- Theorem 7.2.30 PDF-facing statement. -/
theorem theorem_7_2_30_compact_open_lattices_fb_domains
    (V : Type u) [CompleteLattice V] :
    (IsCompactOpenLatticeOfFBDomain V ↔
      HasLeastElementCondition V ∧
        HasFiniteJoinOfJoinPrimes V ∧ HasUpsideDownFiniteMubProperty V) ∧
      (IsCompactOpenLatticeOfBifiniteDomain V ↔
        HasLeastElementCondition V ∧
          HasFiniteJoinOfJoinPrimes V ∧
            HasUpsideDownFiniteMubProperty V ∧ HasLargestElementJoinPrime V) := by
  admit

/-- Theorem 7.2.31 PDF-facing statement. -/
theorem theorem_7_2_31_compact_open_lattices_algebraic_bc
    (V : Type u) [CompleteLattice V] :
    IsCompactOpenLatticeOfAlgebraicBcDomain V ↔
      HasLeastElementCondition V ∧
        HasFiniteJoinOfJoinPrimes V ∧
          JoinPrimesWithBottomClosedUnderFiniteInfima V := by
  admit


end Chapter7
end AbramskyJung

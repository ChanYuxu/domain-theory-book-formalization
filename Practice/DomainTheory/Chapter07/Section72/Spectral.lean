import Practice.DomainTheory.Chapter07.Section72.Algebraic

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.2: spectral and distributive dualities

This module follows a coherent dependency cluster inside the textbook section.
The stable public import remains `Practice.DomainTheory.Chapter07.Section72`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

/-- An algebraic arithmetic lattice object identified with the open-set lattice
of a spectral space.  This records the restricted `Ω` object map in
Theorem 7.2.22. -/
structure OpenSetAlgebraicArithmeticLatticeObjectPresentation
    (X : Space.{u}) (L : AlgebraicArithmeticLatticeObject.{u}) where
  presentation : OpenSetLatticePresentation X
  carrier_equiv : L.carrier ≃ presentation.carrier
  order_agrees :
    ∀ a b : L.carrier,
      @LE.le L.carrier L.lattice.toPreorder.toLE a b ↔
        @LE.le presentation.carrier presentation.lattice.toPreorder.toLE
          (carrier_equiv a) (carrier_equiv b)

/-- Dual-equivalence data for spectral spaces and algebraic arithmetic
lattices. -/
structure SpectralAlgebraicArithmeticDualityData : Type (u + 1) where
  duality :
    DualEquivalenceData
      SpectralSpaceObject.{u}
      AlgebraicArithmeticLatticeObject.{u}
  left_is_opens :
    ∀ X : SpectralSpaceObject.{u},
      OpenSetAlgebraicArithmeticLatticeObjectPresentation X.space (duality.left X)
  right_is_points :
    ∀ L : AlgebraicArithmeticLatticeObject.{u},
      @PointSpacePresentation L.carrier L.lattice (duality.right L).space
  space_unit :
    ∀ X : SpectralSpaceObject.{u}, X.space.Point →
      (duality.right (duality.left X)).space.Point
  space_unit_continuous :
    ∀ X : SpectralSpaceObject.{u},
      StoneContinuousMap X.space (duality.right (duality.left X)).space
  space_unit_agrees :
    ∀ X : SpectralSpaceObject.{u}, ∀ x : X.space.Point,
      (space_unit_continuous X).toFun x = space_unit X x
  space_unit_bijective :
    ∀ X : SpectralSpaceObject.{u}, Function.Bijective (space_unit X)
  lattice_unit :
    ∀ L : AlgebraicArithmeticLatticeObject.{u}, L.carrier →
      (duality.left (duality.right L)).carrier
  lattice_unit_frame_hom :
    ∀ L : AlgebraicArithmeticLatticeObject.{u},
      @FrameHom L.carrier (duality.left (duality.right L)).carrier
        L.lattice (duality.left (duality.right L)).lattice
  lattice_unit_agrees :
    ∀ L : AlgebraicArithmeticLatticeObject.{u}, ∀ a : L.carrier,
      (@FrameHom.toFun L.carrier (duality.left (duality.right L)).carrier
        L.lattice (duality.left (duality.right L)).lattice
          (lattice_unit_frame_hom L)) a = lattice_unit L a
  lattice_unit_bijective :
    ∀ L : AlgebraicArithmeticLatticeObject.{u}, Function.Bijective (lattice_unit L)
  left_preserves_algebraic_arithmetic :
    ∀ X : SpectralSpaceObject.{u},
      @IsAlgebraicArithmeticLattice (duality.left X).carrier
        (duality.left X).lattice
  right_preserves_spectral :
    ∀ L : AlgebraicArithmeticLatticeObject.{u}, IsSpectralSpace (duality.right L).space
  combines_coherent_arithmetic_duality :
    Nonempty (CoherentArithmeticDualityData.{u})
  combines_compact_open_algebraic_distributive_duality :
    Nonempty (CompactOpenSoberAlgebraicDistributiveDualityData.{u})

/-- The restricted open-set object map for spectral spaces. -/
def spectralAlgebraicArithmeticLeft
    (X : SpectralSpaceObject.{u}) :
    AlgebraicArithmeticLatticeObject.{u} where
  carrier := OpenSet X.space
  lattice := OpenSet.completeLattice X.space
  algebraicArithmetic :=
    ⟨⟨⟨openSet_frameDistributive X.space,
      openSet_continuous_of_locallyCompact X.space X.spectral.1.2.1⟩,
      openSet_multiplicativeApproximation_of_coherent X.space X.spectral.1⟩,
      openSet_algebraic_of_compactOpenNeighborhoodBasis
        X.space X.spectral.2⟩

/-- The restricted point-space object map for algebraic arithmetic lattices. -/
def algebraicArithmeticPointRight
    (L : AlgebraicArithmeticLatticeObject.{u}) :
    SpectralSpaceObject.{u} where
  space := pointSpace L.carrier
  spectral :=
    ⟨pointSpace_coherent_of_arithmetic L.carrier L.algebraicArithmetic.1,
      pointSpace_compactOpenBasis_of_algebraicDistributive
        L.carrier L.algebraicArithmetic.2
          L.algebraicArithmetic.1.1.1⟩

/-- Forget the extra arithmetic law while retaining algebraicity and frame
distributivity. -/
def algebraicArithmeticToAlgebraicDistributive
    (L : AlgebraicArithmeticLatticeObject.{u}) :
    AlgebraicDistributiveLatticeObject.{u} where
  carrier := L.carrier
  lattice := L.lattice
  algebraic := L.algebraicArithmetic.2
  distributive := L.algebraicArithmetic.1.1.1

/-- Theorem 7.2.22 PDF-facing statement. -/
theorem theorem_7_2_22_spectral_algebraic_arithmetic_duality :
    Nonempty
      (SpectralAlgebraicArithmeticDualityData.{u}) := by
  refine ⟨{
    duality := {
      left := spectralAlgebraicArithmeticLeft
      right := algebraicArithmeticPointRight
      unit_isomorphism :=
        ∀ X : SpectralSpaceObject.{u},
          Function.Bijective (stoneUnitPoint X.space)
      unit_isomorphism_holds := fun X =>
        stoneUnitPoint_bijective_of_sober X.space X.spectral.1.1
      counit_isomorphism :=
        ∀ L : AlgebraicArithmeticLatticeObject.{u},
          Function.Bijective
            (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun
      counit_isomorphism_holds := fun L =>
        stoneEpsilon_bijective_of_distributiveContinuous
          (algebraicDistributiveToContinuous
            (algebraicArithmeticToAlgebraicDistributive L)) }
    left_is_opens := ?_
    right_is_points := ?_
    space_unit := fun X => stoneUnitPoint X.space
    space_unit_continuous := fun X => stoneUnitContinuous X.space
    space_unit_agrees := ?_
    space_unit_bijective := fun X =>
      stoneUnitPoint_bijective_of_sober X.space X.spectral.1.1
    lattice_unit := fun L =>
      (stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})).toFun
    lattice_unit_frame_hom := fun L =>
      stoneEpsilonFrameHom (⟨L.carrier, L.lattice⟩ : Frame.{u})
    lattice_unit_agrees := ?_
    lattice_unit_bijective := fun L =>
      stoneEpsilon_bijective_of_distributiveContinuous
        (algebraicDistributiveToContinuous
          (algebraicArithmeticToAlgebraicDistributive L))
    left_preserves_algebraic_arithmetic := ?_
    right_preserves_spectral := ?_
    combines_coherent_arithmetic_duality :=
      theorem_7_2_19_coherent_arithmetic_duality
    combines_compact_open_algebraic_distributive_duality :=
      theorem_7_2_20_algebraic_distributive_duality }⟩
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
    exact (spectralAlgebraicArithmeticLeft X).algebraicArithmetic
  · intro L
    exact (algebraicArithmeticPointRight L).spectral

/-- Finite joins of elements of `A`, including the empty join.  This directed
closure is the standard device for applying compactness to an arbitrary join. -/
def FiniteJoinClosure {L : Type u} [CompleteLattice L] (A : Set L) : Set L :=
  {s : L | exists M : Set L, M.Finite ∧ M ⊆ A ∧ s = sSup M}

theorem finiteJoinClosure_directed
    {L : Type u} [CompleteLattice L] (A : Set L) :
    Chapter2.DirectedSet (FiniteJoinClosure A) := by
  constructor
  · refine ⟨⊥, ∅, Set.finite_empty, Set.empty_subset A, ?_⟩
    simp
  · intro x hx y hy
    rcases hx with ⟨M, hMfinite, hMsub, rfl⟩
    rcases hy with ⟨N, hNfinite, hNsub, rfl⟩
    refine ⟨sSup (M ∪ N), ⟨M ∪ N, hMfinite.union hNfinite, ?_, rfl⟩, ?_, ?_⟩
    · intro z hz
      rcases hz with hz | hz
      · exact hMsub hz
      · exact hNsub hz
    · exact sSup_le (fun z hz => le_sSup (Or.inl hz))
    · exact sSup_le (fun z hz => le_sSup (Or.inr hz))

theorem finiteJoinClosure_isSup
    {L : Type u} [CompleteLattice L] (A : Set L) :
    Chapter2.IsSup (FiniteJoinClosure A) (sSup A) := by
  constructor
  · intro s hs
    rcases hs with ⟨M, _hMfinite, hMsub, rfl⟩
    exact sSup_le (fun x hx => le_sSup (hMsub hx))
  · intro y hy
    exact sSup_le (fun x hx => hy ⟨{x}, Set.finite_singleton x, by simpa, by simp⟩)

/-- Compact elements lying below some member of `A`. -/
def CompactBelowSet {L : Type u} [CompleteLattice L] (A : Set L) : Set L :=
  {k : L | IsCompactLatticeElement k ∧ ∃ a ∈ A, k ≤ a}

theorem sSup_compactBelowSet_eq
    {L : Type u} [CompleteLattice L]
    (hAlgebraic : Chapter2.IsAlgebraicDomain L) (A : Set L) :
    sSup (CompactBelowSet A) = sSup A := by
  apply le_antisymm
  · exact sSup_le (by
      intro k hk
      rcases hk.2 with ⟨a, haA, hka⟩
      exact hka.trans (le_sSup haA))
  · exact sSup_le (by
      intro a haA
      have hBasis := Chapter2.prop_2_2_4_1 hAlgebraic a
      exact hBasis.2.2 (sSup (CompactBelowSet A)) (by
        intro k hk
        exact le_sSup ⟨hk.1, a, haA, Chapter2.prop_2_2_2_1 hk.2⟩))

theorem compact_inf_of_multiplicativeApproximation
    {L : Type u} [CompleteLattice L]
    (hMultiplicative : MultiplicativeApproximation L)
    {k l : L} (hk : IsCompactLatticeElement k)
    (hl : IsCompactLatticeElement l) :
    IsCompactLatticeElement (k ⊓ l) := by
  apply hMultiplicative (k ⊓ l) k l
  · exact Chapter2.prop_2_2_2_2 inf_le_left hk le_rfl
  · exact Chapter2.prop_2_2_2_2 inf_le_right hl le_rfl

/-- Restrict a completely prime filter to the compact basis. -/
def compactRestriction {L : Type u} [CompleteLattice L]
    (F : Point L) : Set (CompactElement L) :=
  {k : CompactElement L | k.1 ∈ F.1}

theorem compactRestriction_isPrime
    {L : Type u} [CompleteLattice L]
    (hArithmetic : IsArithmeticLattice L)
    (hAlgebraic : Chapter2.IsAlgebraicDomain L)
    (F : Point L) :
    IsPrimeFilterOfCompactElements (compactRestriction F) := by
  have hBasisTop := Chapter2.prop_2_2_4_1 hAlgebraic (⊤ : L)
  have hSupTop :
      sSup (Chapter2.Approximants (Chapter2.CompactSet : Set L) (⊤ : L)) = ⊤ :=
    Chapter2.IsSup.unique
      (by
        constructor
        · intro x hx
          exact le_sSup hx
        · intro y hy
          exact sSup_le hy)
      hBasisTop.2
  refine {
    nonempty := ?_
    upward_closed := ?_
    binary_meet_closed := ?_
    finite_join_prime := ?_ }
  · have hJoinMem :
        sSup (Chapter2.Approximants (Chapter2.CompactSet : Set L) (⊤ : L)) ∈ F.1 := by
      simpa [hSupTop] using F.2.1.1
    rcases F.2.2 _ hJoinMem with ⟨k, hk, hkF⟩
    exact ⟨⟨k, hk.1⟩, hkF⟩
  · intro k l hkF hkl
    exact F.2.1.2.1 hkF hkl
  · intro k l hkF hlF
    let m : CompactElement L :=
      ⟨k.1 ⊓ l.1,
        compact_inf_of_multiplicativeApproximation hArithmetic.2 k.2 l.2⟩
    exact ⟨m, rfl, F.2.1.2.2 hkF hlF⟩
  · intro M _hMfinite hGenerated
    rcases hGenerated with ⟨k, hkF, hkSup⟩
    have hSupF : sSup ((fun c : CompactElement L => (c.1 : L)) '' M) ∈ F.1 :=
      F.2.1.2.1 hkF hkSup
    rcases F.2.2 _ hSupF with ⟨x, hx, hxF⟩
    rcases hx with ⟨k, hkM, rfl⟩
    exact ⟨k, hkM, hxF⟩

theorem generatedFilterOfCompacts_isCompletelyPrime
    {L : Type u} [CompleteLattice L]
    (hAlgebraic : Chapter2.IsAlgebraicDomain L)
    (G : Set (CompactElement L))
    (hG : IsPrimeFilterOfCompactElements G) :
    IsCompletelyPrimeFilter (GeneratedFilterOfCompacts G) := by
  constructor
  · constructor
    · rcases hG.nonempty with ⟨k, hkG⟩
      exact ⟨k, hkG, le_top⟩
    · constructor
      · intro x y hx hxy
        rcases hx with ⟨k, hkG, hkx⟩
        exact ⟨k, hkG, hkx.trans hxy⟩
      · intro x y hx hy
        rcases hx with ⟨k, hkG, hkx⟩
        rcases hy with ⟨l, hlG, hly⟩
        rcases hG.binary_meet_closed hkG hlG with ⟨m, hmEq, hmG⟩
        refine ⟨m, hmG, ?_⟩
        rw [hmEq]
        exact inf_le_inf hkx hly
  · intro A hJoinGenerated
    rcases hJoinGenerated with ⟨k, hkG, hkJoin⟩
    have hkCompactJoin : k.1 ≤ sSup (CompactBelowSet A) := by
      simpa [sSup_compactBelowSet_eq hAlgebraic A] using hkJoin
    rcases k.2 (finiteJoinClosure_directed (CompactBelowSet A))
        (finiteJoinClosure_isSup (CompactBelowSet A)) hkCompactJoin with
      ⟨s, hsClosure, hks⟩
    rcases hsClosure with ⟨M, hMfinite, hMsub, rfl⟩
    let K : Set (CompactElement L) :=
      {c : CompactElement L | c.1 ∈ M}
    have hKfinite : K.Finite := by
      apply Set.Finite.of_finite_image (f := Subtype.val)
      · exact hMfinite.subset (by
          intro x hx
          rcases hx with ⟨c, hcK, rfl⟩
          exact hcK)
      · exact Subtype.val_injective.injOn
    have hImageEq : ((fun c : CompactElement L => (c.1 : L)) '' K) = M := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hx with ⟨c, hcK, rfl⟩
        exact hcK
      · intro x hxM
        have hxCompact : IsCompactLatticeElement x := (hMsub hxM).1
        exact ⟨⟨x, hxCompact⟩, hxM, rfl⟩
    have hFiniteJoinGenerated :
        sSup ((fun c : CompactElement L => (c.1 : L)) '' K) ∈
          GeneratedFilterOfCompacts G := by
      rw [hImageEq]
      exact ⟨k, hkG, hks⟩
    rcases hG.finite_join_prime K hKfinite hFiniteJoinGenerated with
      ⟨c, hcK, hcG⟩
    rcases (hMsub hcK).2 with ⟨a, haA, hca⟩
    exact ⟨a, haA, c, hcG, hca⟩

theorem generated_compactRestriction_eq
    {L : Type u} [CompleteLattice L]
    (hAlgebraic : Chapter2.IsAlgebraicDomain L) (F : Point L) :
    GeneratedFilterOfCompacts (compactRestriction F) = F.1 := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨k, hkF, hkx⟩
    exact F.2.1.2.1 hkF hkx
  · intro x hxF
    have hBasis := Chapter2.prop_2_2_4_1 hAlgebraic x
    have hSupEq :
        sSup (Chapter2.Approximants (Chapter2.CompactSet : Set L) x) = x :=
      Chapter2.IsSup.unique
        (by
          constructor
          · intro y hy
            exact le_sSup hy
          · intro y hy
            exact sSup_le hy)
        hBasis.2
    have hJoinMem :
        sSup (Chapter2.Approximants (Chapter2.CompactSet : Set L) x) ∈ F.1 := by
      simpa [hSupEq] using hxF
    rcases F.2.2 _ hJoinMem with ⟨k, hk, hkF⟩
    exact ⟨⟨k, hk.1⟩, hkF, Chapter2.prop_2_2_2_1 hk.2⟩

theorem compactRestriction_generated_eq
    {L : Type u} [CompleteLattice L]
    (G : Set (CompactElement L))
    (hG : IsPrimeFilterOfCompactElements G) :
    {k : CompactElement L | k.1 ∈ GeneratedFilterOfCompacts G} = G := by
  apply Set.Subset.antisymm
  · intro k hk
    rcases hk with ⟨l, hlG, hlk⟩
    exact hG.upward_closed hlG hlk
  · intro k hkG
    exact ⟨k, hkG, le_rfl⟩

theorem pointOpen_iff_compactBasicOpenGenerated
    {L : Type u} [CompleteLattice L]
    (hAlgebraic : Chapter2.IsAlgebraicDomain L)
    (U : Set (Point L)) :
    PointOpen L U ↔ CompactBasicOpenGenerated U := by
  constructor
  · intro hU
    rcases epsilon_surjective L U hU with ⟨x, rfl⟩
    let S : Set (CompactElement L) := {k : CompactElement L | k.1 ≤ x}
    refine ⟨S, ?_⟩
    apply Set.Subset.antisymm
    · intro F hxF
      have hxGenerated : x ∈ GeneratedFilterOfCompacts (compactRestriction F) := by
        rw [generated_compactRestriction_eq hAlgebraic F]
        exact hxF
      rcases hxGenerated with ⟨k, hkF, hkx⟩
      exact ⟨pointBasicOpen k.1, ⟨k, hkx, rfl⟩, hkF⟩
    · intro F hF
      rcases hF with ⟨O, hO, hFO⟩
      rcases hO with ⟨k, hkx, rfl⟩
      exact F.2.1.2.1 hFO hkx
  · rintro ⟨S, rfl⟩
    exact PointOpen.sUnion _ (by
      intro U hU
      rcases hU with ⟨k, _hkS, rfl⟩
      exact PointOpen.basic k.1)

/-- Proposition 7.2.23 PDF-facing statement. -/
theorem prop_7_2_23_prime_filters_compacts_points
    (L : Type u) [CompleteLattice L] :
    IsAlgebraicArithmeticLattice L →
      Nonempty (CompactPrimeFilterCorrespondence L) := by
  intro hL
  let toCompact : Point L → Set (CompactElement L) := compactRestriction
  have hPrime :
      ∀ F : Point L, IsPrimeFilterOfCompactElements (toCompact F) :=
    fun F => compactRestriction_isPrime hL.1 hL.2 F
  let fromCompact :
      {G : Set (CompactElement L) // IsPrimeFilterOfCompactElements G} → Point L :=
    fun G => ⟨GeneratedFilterOfCompacts G.1,
      generatedFilterOfCompacts_isCompletelyPrime hL.2 G.1 G.2⟩
  refine ⟨{
    toCompactPrimeFilter := toCompact
    restriction_eq := fun _F _k => Iff.rfl
    restriction_is_prime := hPrime
    ofCompactPrimeFilter := fromCompact
    generated_filter_eq := fun _G => rfl
    restriction_generates_filter := generated_compactRestriction_eq hL.2
    left_inverse := ?_
    right_inverse := ?_
    topology_generated_by_compacts := pointOpen_iff_compactBasicOpenGenerated hL.2 }⟩
  · intro F
    apply Subtype.ext
    exact generated_compactRestriction_eq hL.2 F
  · intro G
    exact compactRestriction_generated_eq G.1 G.2

/-- Ideals of a distributive lattice object, used to identify the
ideal-completion object map in Proposition 7.2.25. -/
structure IsDistributiveLatticeIdeal
    {L : Type u} [CompleteLattice L] (I : Set L) : Prop where
  nonempty : I.Nonempty
  lower_closed : ∀ {x y : L}, y ∈ I → x ≤ y → x ∈ I
  finite_join_closed : ∀ M : Set L, M.Finite → M ⊆ I → sSup M ∈ I

/-- The compact-basis object map in Proposition 7.2.25, identified with
`K(L)`, the compact elements of the algebraic arithmetic lattice. -/
structure CompactBasisObjectPresentation
    (L : AlgebraicArithmeticLatticeObject.{u})
    (V : DistributiveLatticeRelationObject.{u}) where
  carrier_equiv : V.carrier ≃ @CompactElement L.carrier L.lattice
  order_agrees :
    ∀ a b : V.carrier,
      @LE.le V.carrier V.lattice.toPreorder.toLE a b ↔
        @LE.le L.carrier L.lattice.toPreorder.toLE
          (carrier_equiv a).1 (carrier_equiv b).1

/-- The ideal-completion object map in Proposition 7.2.25, identified with the
lattice of ideals of the distributive-lattice relation object. -/
structure IdealCompletionObjectPresentation
    (V : DistributiveLatticeRelationObject.{u})
    (L : AlgebraicArithmeticLatticeObject.{u}) where
  carrier_equiv :
    L.carrier ≃
      {I : Set V.carrier // @IsDistributiveLatticeIdeal V.carrier V.lattice I}
  order_agrees :
    ∀ a b : L.carrier,
      @LE.le L.carrier L.lattice.toPreorder.toLE a b ↔
        (carrier_equiv a).1 ⊆ (carrier_equiv b).1

/-- Equivalence data for algebraic arithmetic lattices and distributive lattices
with join-approximable relations. -/
structure AlgebraicArithmeticJoinApproximableEquivalenceData : Type (u + 2) where
  equivalence :
    EquivalenceData
      AlgebraicArithmeticLatticeObject.{u}
      DistributiveLatticeRelationObject.{u}
  compact_basis :
    AlgebraicArithmeticLatticeObject.{u} → DistributiveLatticeRelationObject.{u}
  ideal_completion :
    DistributiveLatticeRelationObject.{u} → AlgebraicArithmeticLatticeObject.{u}
  compact_basis_presentation :
    ∀ L : AlgebraicArithmeticLatticeObject.{u},
      CompactBasisObjectPresentation L (compact_basis L)
  ideal_completion_presentation :
    ∀ V : DistributiveLatticeRelationObject.{u},
      IdealCompletionObjectPresentation V (ideal_completion V)
  compact_basis_eq_left :
    ∀ L : AlgebraicArithmeticLatticeObject.{u}, compact_basis L = equivalence.left L
  ideal_completion_eq_right :
    ∀ V : DistributiveLatticeRelationObject.{u}, ideal_completion V = equivalence.right V
  frame_hom_to_relation :
    ∀ L M : AlgebraicArithmeticLatticeObject.{u},
      @FrameHom L.carrier M.carrier L.lattice M.lattice →
        JoinApproximableMorphism (compact_basis M) (compact_basis L)
  relation_to_frame_hom :
    ∀ V W : DistributiveLatticeRelationObject.{u},
      JoinApproximableMorphism V W →
        @FrameHom (ideal_completion W).carrier (ideal_completion V).carrier
          (ideal_completion W).lattice (ideal_completion V).lattice
  morphism_inverse_laws : Prop

/-- Proposition 7.2.25 PDF-facing statement. -/
theorem prop_7_2_25_algebraic_arithmetic_lattice_equivalence :
    Nonempty (AlgebraicArithmeticJoinApproximableEquivalenceData.{u}) := by
  admit

/-- Prime filters of a distributive lattice, used for the direct `spec`
presentation in Theorem 7.2.26. -/
structure IsPrimeFilterOfDistributiveLattice
    {L : Type u} [CompleteLattice L] (F : Set L) : Prop where
  nonempty : F.Nonempty
  proper : ⊥ ∉ F
  upward_closed : ∀ {x y : L}, x ∈ F → x ≤ y → y ∈ F
  binary_meet_closed : ∀ {x y : L}, x ∈ F → y ∈ F → x ⊓ y ∈ F
  finite_join_prime :
    ∀ M : Set L, M.Finite → sSup M ∈ F → ∃ m ∈ M, m ∈ F

/-- The `KΩ` object map in Theorem 7.2.26, identified with the compact-open
subsets of a spectral space. -/
structure CompactOpenFunctorPresentation
    (X : SpectralSpaceObject.{u})
    (V : DistributiveLatticeRelationObject.{u}) where
  toCompactOpen : V.carrier → {U : Set X.space.Point // IsCompactOpenSubset X.space U}
  ofCompactOpen : {U : Set X.space.Point // IsCompactOpenSubset X.space U} → V.carrier
  left_inv : ∀ a : V.carrier, ofCompactOpen (toCompactOpen a) = a
  right_inv :
    ∀ U : {U : Set X.space.Point // IsCompactOpenSubset X.space U},
      toCompactOpen (ofCompactOpen U) = U
  order_agrees :
    ∀ a b : V.carrier,
      @LE.le V.carrier V.lattice.toPreorder.toLE a b ↔
        (toCompactOpen a).1 ⊆ (toCompactOpen b).1

/-- The `spec` object map in Theorem 7.2.26, identified with the space of prime
filters of a distributive lattice. -/
structure SpectrumFunctorPresentation
    (V : DistributiveLatticeRelationObject.{u})
    (X : SpectralSpaceObject.{u}) where
  point_equiv :
    X.space.Point ≃
      {F : Set V.carrier // @IsPrimeFilterOfDistributiveLattice V.carrier V.lattice F}
  basic_open_open :
    ∀ a : V.carrier,
      X.space.IsOpen {x : X.space.Point | a ∈ (point_equiv x).1}
  topology_generated_by_basic_opens :
    ∀ U : Set X.space.Point,
      X.space.IsOpen U ↔
        ∃ S : Set V.carrier,
          U = ⋃₀ ((fun a : V.carrier =>
            {x : X.space.Point | a ∈ (point_equiv x).1}) '' S)

/-- Dual-equivalence data between spectral spaces and distributive lattices with
join-approximable relations, via the `KΩ` and `spec` functors. -/
structure SpectralDistributiveDualityData : Type (u + 2) where
  duality :
    DualEquivalenceData
      SpectralSpaceObject.{u}
      DistributiveLatticeRelationObject.{u}
  compact_open_functor :
    SpectralSpaceObject.{u} → DistributiveLatticeRelationObject.{u}
  spectrum_functor :
    DistributiveLatticeRelationObject.{u} → SpectralSpaceObject.{u}
  compact_open_presentation :
    ∀ X : SpectralSpaceObject.{u},
      CompactOpenFunctorPresentation X (compact_open_functor X)
  spectrum_presentation :
    ∀ V : DistributiveLatticeRelationObject.{u},
      SpectrumFunctorPresentation V (spectrum_functor V)
  compact_open_eq_left :
    ∀ X : SpectralSpaceObject.{u}, compact_open_functor X = duality.left X
  spectrum_eq_right :
    ∀ V : DistributiveLatticeRelationObject.{u}, spectrum_functor V = duality.right V
  continuous_map_to_relation :
    ∀ X Y : SpectralSpaceObject.{u},
      StoneContinuousMap X.space Y.space →
        JoinApproximableMorphism (compact_open_functor Y) (compact_open_functor X)
  relation_to_continuous_map :
    ∀ V W : DistributiveLatticeRelationObject.{u},
      JoinApproximableMorphism V W →
        StoneContinuousMap (spectrum_functor W).space (spectrum_functor V).space
  combines_algebraic_arithmetic_equivalence :
    Nonempty (AlgebraicArithmeticJoinApproximableEquivalenceData.{u})
  compact_prime_filter_points :
    ∀ V : DistributiveLatticeRelationObject.{u},
      Nonempty (@CompactPrimeFilterCorrespondence V.carrier V.lattice)

/-- Theorem 7.2.26 PDF-facing statement. -/
theorem theorem_7_2_26_spectral_distributive_duality :
    Nonempty (SpectralDistributiveDualityData.{u}) := by
  admit


end Chapter7
end AbramskyJung

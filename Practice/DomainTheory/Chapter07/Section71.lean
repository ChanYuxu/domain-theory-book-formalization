import Practice.DomainTheory.Chapter07.StoneCore

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.1

Stone duality: approximation/distributivity, points of complete lattices, and
the basic `Omega`/`pt` adjunction.  The statements deliberately reuse the
order-theoretic material from Chapter 2 and the topological interfaces from
`Chapter07.lean`.

Semantic audit note: the PDF-facing Stone/Raney theorem names below are visible
proof-debt declarations.  The auxiliary Stone lattice and Stone adjunction
packages remain only to record the intended data shape while proofs are being
translated.  The point-space topology clause is proved for the generated basic
opens.
-/

universe u v w

namespace AbramskyJung
namespace Chapter7

/-- Complete lattices are dcpos in the ambient order. -/
theorem completeLattice_isDcpo (L : Type u) [CompleteLattice L] :
    Chapter2.IsDcpo L := by
  intro A _hA
  refine ⟨sSup A, ?_⟩
  constructor
  · intro a ha
    exact le_sSup ha
  · intro y hy
    exact sSup_le (by intro a ha; exact hy ha)

/-- Continuity for a complete lattice, with the dcpo witness made explicit. -/
def IsContinuousCompleteLattice (L : Type u) [CompleteLattice L] : Prop :=
  Chapter2.IsDcpo L ∧ Chapter2.IsContinuousDomain L

/-- Algebraicity for a complete lattice, with the dcpo witness made explicit. -/
def IsAlgebraicCompleteLattice (L : Type u) [CompleteLattice L] : Prop :=
  Chapter2.IsDcpo L ∧ Chapter3.IsAlgebraicDomain L

/-- The choice-function distributivity law for directed families in Theorem 7.1.1. -/
def DirectedChoiceMeetJoinLaw (L : Type u) [CompleteLattice L] : Prop :=
  ∀ (ι : Type v) (A : ι → Set L),
    (∀ i : ι, Chapter2.DirectedSet (A i)) →
      sInf (Set.range (fun i : ι => sSup (A i))) =
        sSup {x : L |
          ∃ f : ∀ i : ι, {a : L // a ∈ A i},
            x = sInf (Set.range (fun i : ι => (f i).1))}

/-- The complete-distributivity law with arbitrary, rather than directed, families. -/
def CompleteChoiceMeetJoinLaw (L : Type u) [CompleteLattice L] : Prop :=
  ∀ (ι : Type v) (A : ι → Set L),
    sInf (Set.range (fun i : ι => sSup (A i))) =
      sSup {x : L |
        ∃ f : ∀ i : ι, {a : L // a ∈ A i},
          x = sInf (Set.range (fun i : ι => (f i).1))}

/-- Definition 7.1.2: Raney's prime-continuity relation on a complete lattice. -/
def PrimeWayBelow {L : Type u} [CompleteLattice L] (x y : L) : Prop :=
  ∀ A : Set L, y ≤ sSup A → ∃ a ∈ A, x ≤ a

/-- Definition 7.1.2: a complete lattice is prime-continuous if every element is the
join of its prime approximants. -/
def IsPrimeContinuousLattice (L : Type u) [CompleteLattice L] : Prop :=
  ∀ x : L, x = sSup {y : L | PrimeWayBelow y x}

/-- Definition 7.1.2, named book entry. -/
def def_7_1_2_prime_continuity_relation (L : Type u) [CompleteLattice L] : Prop :=
  IsPrimeContinuousLattice L

/-- Definition 7.1.4: meet-generation by a distinguished set of elements. -/
def MeetGeneratedBy {L : Type u} [CompleteLattice L] (G : Set L) : Prop :=
  ∀ x : L, x = sInf {g : L | g ∈ G ∧ x ≤ g}

/-- Definition 7.1.4, dual: join-generation by a distinguished set of elements. -/
def JoinGeneratedBy {L : Type u} [CompleteLattice L] (G : Set L) : Prop :=
  ∀ x : L, x = sSup {g : L | g ∈ G ∧ g ≤ x}

/-- Definition 7.1.4: the two generation notions introduced in the PDF. -/
structure MeetJoinGenerationNotions (L : Type u) [CompleteLattice L] where
  meet_generated_by : Set L → Prop
  join_generated_by : Set L → Prop

/-- Definition 7.1.4, named book entry. -/
def def_7_1_4_meet_generation (L : Type u) [CompleteLattice L] :
    MeetJoinGenerationNotions L where
  meet_generated_by := MeetGeneratedBy
  join_generated_by := JoinGeneratedBy

/-- Definition 7.1.5: finite meet-irreducibility. -/
def IsFiniteMeetIrreducible {L : Type u} [CompleteLattice L] (x : L) : Prop :=
  x ≠ ⊤ ∧
    ∀ M : Set L, M.Finite → x = sInf M → ∃ m ∈ M, x = m

/-- Definition 7.1.5: finite meet-primality. -/
def IsFiniteMeetPrime {L : Type u} [CompleteLattice L] (x : L) : Prop :=
  x ≠ ⊤ ∧
    ∀ M : Set L, M.Finite → sInf M ≤ x → ∃ m ∈ M, m ≤ x

/-- Definition 7.1.5: complete meet-irreducibility. -/
def IsCompletelyMeetIrreducible {L : Type u} [CompleteLattice L] (x : L) : Prop :=
  x ≠ ⊤ ∧
    ∀ M : Set L, x = sInf M → ∃ m ∈ M, x = m

/-- Definition 7.1.5: complete meet-primality. -/
def IsCompletelyMeetPrime {L : Type u} [CompleteLattice L] (x : L) : Prop :=
  x ≠ ⊤ ∧
    ∀ M : Set L, sInf M ≤ x → ∃ m ∈ M, m ≤ x

/-- Definition 7.1.5, dual: finite join-irreducibility. -/
def IsFiniteJoinIrreducible {L : Type u} [CompleteLattice L] (x : L) : Prop :=
  x ≠ ⊥ ∧
    ∀ M : Set L, M.Finite → x = sSup M → ∃ m ∈ M, x = m

/-- Definition 7.1.5, dual: finite join-primality. -/
def IsFiniteJoinPrime {L : Type u} [CompleteLattice L] (x : L) : Prop :=
  x ≠ ⊥ ∧
    ∀ M : Set L, M.Finite → x ≤ sSup M → ∃ m ∈ M, x ≤ m

/-- Definition 7.1.5, dual: complete join-irreducibility. -/
def IsCompletelyJoinIrreducible {L : Type u} [CompleteLattice L] (x : L) : Prop :=
  x ≠ ⊥ ∧
    ∀ M : Set L, x = sSup M → ∃ m ∈ M, x = m

/-- Definition 7.1.5, dual: complete join-primality. -/
def IsCompletelyJoinPrime {L : Type u} [CompleteLattice L] (x : L) : Prop :=
  x ≠ ⊥ ∧
    ∀ M : Set L, x ≤ sSup M → ∃ m ∈ M, x ≤ m

/-- Definition 7.1.5: the irreducible/prime predicates introduced in the PDF. -/
structure MeetIrreduciblePrimeNotions (L : Type u) [CompleteLattice L] where
  finite_meet_irreducible : L → Prop
  finite_meet_prime : L → Prop
  completely_meet_irreducible : L → Prop
  completely_meet_prime : L → Prop
  finite_join_irreducible : L → Prop
  finite_join_prime : L → Prop
  completely_join_irreducible : L → Prop
  completely_join_prime : L → Prop

/-- Definition 7.1.5, named book entry. -/
def def_7_1_5_meet_irreducible_prime (L : Type u) [CompleteLattice L] :
    MeetIrreduciblePrimeNotions L where
  finite_meet_irreducible := IsFiniteMeetIrreducible
  finite_meet_prime := IsFiniteMeetPrime
  completely_meet_irreducible := IsCompletelyMeetIrreducible
  completely_meet_prime := IsCompletelyMeetPrime
  finite_join_irreducible := IsFiniteJoinIrreducible
  finite_join_prime := IsFiniteJoinPrime
  completely_join_irreducible := IsCompletelyJoinIrreducible
  completely_join_prime := IsCompletelyJoinPrime

/-- The frame distributivity law. -/
def IsFrameDistributive (L : Type u) [CompleteLattice L] : Prop :=
  ∀ (x : L) (S : Set L), x ⊓ sSup S = sSup ((fun y : L => x ⊓ y) '' S)

/-- The order-dual frame distributivity law. -/
def IsCoframeDistributive (L : Type u) [CompleteLattice L] : Prop :=
  ∀ (x : L) (S : Set L), x ⊔ sInf S = sInf ((fun y : L => x ⊔ y) '' S)

/-- The first finite choice equation in Theorem 7.1.8:
finite meets distribute over arbitrary joins. -/
def FiniteMeetJoinChoiceLaw (L : Type u) [CompleteLattice L] : Prop :=
  ∀ (ι : Type v) (_hι : Finite ι) (A : ι → Set L),
    sInf (Set.range (fun i : ι => sSup (A i))) =
      sSup {x : L |
        ∃ f : ∀ i : ι, {a : L // a ∈ A i},
          x = sInf (Set.range (fun i : ι => (f i).1))}

/-- The second choice equation in Theorem 7.1.8:
arbitrary joins distribute over finite meets. -/
def JoinFiniteMeetChoiceLaw (L : Type u) [CompleteLattice L] : Prop :=
  ∀ (ι : Type v) (M : ι → Set L),
    (∀ i : ι, (M i).Finite) →
      sSup (Set.range (fun i : ι => sInf (M i))) =
        sInf {x : L |
        ∃ f : ∀ i : ι, {a : L // a ∈ M i},
          x = sSup (Set.range (fun i : ι => (f i).1))}

/-- The first dual choice equation in Theorem 7.1.8:
finite joins distribute over arbitrary meets. -/
def FiniteJoinMeetChoiceLaw (L : Type u) [CompleteLattice L] : Prop :=
  ∀ (ι : Type v) (_hι : Finite ι) (A : ι → Set L),
    sSup (Set.range (fun i : ι => sInf (A i))) =
      sInf {x : L |
        ∃ f : ∀ i : ι, {a : L // a ∈ A i},
          x = sSup (Set.range (fun i : ι => (f i).1))}

/-- The second dual choice equation in Theorem 7.1.8:
arbitrary meets distribute over finite joins. -/
def MeetFiniteJoinChoiceLaw (L : Type u) [CompleteLattice L] : Prop :=
  ∀ (ι : Type v) (M : ι → Set L),
    (∀ i : ι, (M i).Finite) →
      sInf (Set.range (fun i : ι => sSup (M i))) =
        sSup {x : L |
          ∃ f : ∀ i : ι, {a : L // a ∈ M i},
            x = sInf (Set.range (fun i : ι => (f i).1))}

/-- The finite choice distributivity laws generated by meet-prime elements in
Theorem 7.1.8. -/
def FinitePrimeChoiceDistributivity (L : Type u) [CompleteLattice L] : Prop :=
  IsFrameDistributive L ∧
    FiniteMeetJoinChoiceLaw.{u, v} L ∧
      JoinFiniteMeetChoiceLaw.{u, v} L

/-- The dual finite choice distributivity laws generated by join-prime elements
in Theorem 7.1.8. -/
def DualFinitePrimeChoiceDistributivity (L : Type u) [CompleteLattice L] : Prop :=
  IsCoframeDistributive L ∧
    FiniteJoinMeetChoiceLaw.{u, v} L ∧
      MeetFiniteJoinChoiceLaw.{u, v} L

/-- Definition 7.1.9: frame homomorphisms preserve arbitrary joins and finite meets. -/
structure FrameHom (K : Type u) (L : Type v) [CompleteLattice K] [CompleteLattice L] where
  toFun : K → L
  map_sSup : ∀ S : Set K, toFun (sSup S) = sSup (toFun '' S)
  map_top : toFun ⊤ = ⊤
  map_inf : ∀ x y : K, toFun (x ⊓ y) = toFun x ⊓ toFun y

/-- Definition 7.1.9, named book entry. -/
abbrev def_7_1_9_frame_homomorphism
    (K : Type u) (L : Type v) [CompleteLattice K] [CompleteLattice L] :=
  FrameHom K L

/-- Definition 7.1.10: lattice filters. -/
def IsLatticeFilter {L : Type u} [CompleteLattice L] (F : Set L) : Prop :=
  ⊤ ∈ F ∧
    (∀ ⦃x y : L⦄, x ∈ F → x ≤ y → y ∈ F) ∧
      ∀ ⦃x y : L⦄, x ∈ F → y ∈ F → x ⊓ y ∈ F

/-- Definition 7.1.10: prime filters. -/
def IsPrimeFilter {L : Type u} [CompleteLattice L] (F : Set L) : Prop :=
  IsLatticeFilter F ∧
    ∀ M : Set L, M.Finite → sSup M ∈ F → ∃ m ∈ M, m ∈ F

/-- Definition 7.1.10: completely prime filters. -/
def IsCompletelyPrimeFilter {L : Type u} [CompleteLattice L] (F : Set L) : Prop :=
  IsLatticeFilter F ∧
    ∀ M : Set L, sSup M ∈ F → ∃ m ∈ M, m ∈ F

/-- Definition 7.1.10, dual: lattice ideals. -/
def IsLatticeIdeal {L : Type u} [CompleteLattice L] (I : Set L) : Prop :=
  ⊥ ∈ I ∧
    (∀ ⦃x y : L⦄, y ∈ I → x ≤ y → x ∈ I) ∧
      ∀ ⦃x y : L⦄, x ∈ I → y ∈ I → x ⊔ y ∈ I

/-- Definition 7.1.10, dual: prime ideals. -/
def IsPrimeIdeal {L : Type u} [CompleteLattice L] (I : Set L) : Prop :=
  IsLatticeIdeal I ∧
    ∀ M : Set L, M.Finite → sInf M ∈ I → ∃ m ∈ M, m ∈ I

/-- Definition 7.1.10, dual: completely prime ideals. -/
def IsCompletelyPrimeIdeal {L : Type u} [CompleteLattice L] (I : Set L) : Prop :=
  IsLatticeIdeal I ∧
    ∀ M : Set L, sInf M ∈ I → ∃ m ∈ M, m ∈ I

/-- Definition 7.1.10: the filter and ideal predicates introduced in the PDF. -/
structure PrimeFilterIdealNotions (L : Type u) [CompleteLattice L] where
  lattice_filter : Set L → Prop
  prime_filter : Set L → Prop
  completely_prime_filter : Set L → Prop
  lattice_ideal : Set L → Prop
  prime_ideal : Set L → Prop
  completely_prime_ideal : Set L → Prop

/-- Definition 7.1.10, named book entry. -/
def def_7_1_10_prime_filters_ideals (L : Type u) [CompleteLattice L] :
    PrimeFilterIdealNotions L where
  lattice_filter := IsLatticeFilter
  prime_filter := IsPrimeFilter
  completely_prime_filter := IsCompletelyPrimeFilter
  lattice_ideal := IsLatticeIdeal
  prime_ideal := IsPrimeIdeal
  completely_prime_ideal := IsCompletelyPrimeIdeal

/-- A filter whose complement is a principal ideal. -/
def HasPrincipalIdealComplement {L : Type u} [CompleteLattice L] (F : Set L) : Prop :=
  ∃ x : L, Fᶜ = {y : L | y ≤ x}

/-- The characteristic map of a subset is a frame homomorphism into `Prop`. -/
def HasCharacteristicFrameHom {L : Type u} [CompleteLattice L] (F : Set L) : Prop :=
  ∃ h : FrameHom L Prop, ∀ x : L, h.toFun x = (x ∈ F)

/-- A lattice filter contains the infimum of any finite subset of its members. -/
theorem latticeFilter_sInf_mem_of_finite {L : Type u} [CompleteLattice L]
    {F M : Set L} (hF : IsLatticeFilter F) (hM : M.Finite)
    (hMem : ∀ x ∈ M, x ∈ F) :
    sInf M ∈ F := by
  refine Set.Finite.induction_on
    (motive := fun M _ => (∀ x ∈ M, x ∈ F) → sInf M ∈ F)
    M hM ?_ ?_ hMem
  · intro _hMem
    simpa using hF.1
  · intro x M _hxM _hM ih hMemInsert
    rw [sInf_insert]
    exact hF.2.2 (hMemInsert x (Set.mem_insert x M)) (ih (by
      intro y hy
      exact hMemInsert y (Set.mem_insert_of_mem x hy)))

/-- A completely prime filter has a principal-ideal complement, generated by
the join of all elements outside the filter. -/
theorem completelyPrimeFilter_principalIdealComplement
    {L : Type u} [CompleteLattice L] {F : Set L}
    (hF : IsCompletelyPrimeFilter F) :
    Fᶜ = {x : L | x ≤ sSup (Fᶜ : Set L)} := by
  let p : L := sSup (Fᶜ : Set L)
  have hp_not_mem : p ∉ F := by
    intro hpF
    rcases hF.2 (Fᶜ : Set L) hpF with ⟨x, hxComp, hxF⟩
    exact hxComp hxF
  ext x
  constructor
  · intro hx
    exact le_sSup hx
  · intro hxle hxF
    exact hp_not_mem (hF.1.2.1 hxF hxle)

/-- A lattice filter with principal-ideal complement is completely prime. -/
theorem completelyPrimeFilter_of_principalIdealComplement
    {L : Type u} [CompleteLattice L] {F : Set L}
    (hFilter : IsLatticeFilter F) (hPrincipal : HasPrincipalIdealComplement F) :
    IsCompletelyPrimeFilter F := by
  classical
  rcases hPrincipal with ⟨p, hp⟩
  constructor
  · exact hFilter
  · intro M hSupF
    by_contra hNo
    push Not at hNo
    have hSupLe : sSup M ≤ p := by
      refine sSup_le ?_
      intro x hxM
      have hxComp : x ∈ Fᶜ := hNo x hxM
      simpa [hp] using hxComp
    have hSupComp : sSup M ∈ Fᶜ := by
      simpa [hp] using hSupLe
    exact hSupComp hSupF

/-- The principal-ideal complement characterization of completely prime filters. -/
theorem completelyPrimeFilter_iff_principalIdealComplement
    {L : Type u} [CompleteLattice L] {F : Set L} :
    IsCompletelyPrimeFilter F ↔ IsLatticeFilter F ∧ HasPrincipalIdealComplement F := by
  constructor
  · intro hF
    exact ⟨hF.1, ⟨sSup (Fᶜ : Set L), completelyPrimeFilter_principalIdealComplement hF⟩⟩
  · intro h
    exact completelyPrimeFilter_of_principalIdealComplement h.1 h.2

/-- The complement generator of a completely prime filter is finite meet-prime. -/
theorem completelyPrimeFilter_complement_finiteMeetPrime
    {L : Type u} [CompleteLattice L] {F : Set L}
    (hF : IsCompletelyPrimeFilter F) :
    IsFiniteMeetPrime (sSup (Fᶜ : Set L)) ∧
      Fᶜ = {x : L | x ≤ sSup (Fᶜ : Set L)} := by
  classical
  let p : L := sSup (Fᶜ : Set L)
  have hpCompl : Fᶜ = {x : L | x ≤ p} :=
    completelyPrimeFilter_principalIdealComplement hF
  have hp_not_mem : p ∉ F := by
    intro hpF
    rcases hF.2 (Fᶜ : Set L) hpF with ⟨x, hxComp, hxF⟩
    exact hxComp hxF
  refine ⟨?_, hpCompl⟩
  constructor
  · intro hpTop
    have hpMem : p ∈ F := by
      change sSup (Fᶜ : Set L) ∈ F
      rw [hpTop]
      exact hF.1.1
    exact hp_not_mem hpMem
  · intro M hM hInfLe
    by_contra hNo
    push Not at hNo
    have hAllMem : ∀ x ∈ M, x ∈ F := by
      intro x hxM
      by_contra hxF
      have hxComp : x ∈ Fᶜ := hxF
      have hxLe : x ≤ p := by
        simpa [hpCompl] using hxComp
      exact hNo x hxM hxLe
    have hInfMem : sInf M ∈ F :=
      latticeFilter_sInf_mem_of_finite hF.1 hM hAllMem
    exact hp_not_mem (hF.1.2.1 hInfMem hInfLe)

/-- A finite meet-prime principal complement determines a completely prime filter. -/
theorem completelyPrimeFilter_of_finiteMeetPrime_complement
    {L : Type u} [CompleteLattice L] {F : Set L} {p : L}
    (hpPrime : IsFiniteMeetPrime p) (hpCompl : Fᶜ = {x : L | x ≤ p}) :
    IsCompletelyPrimeFilter F := by
  classical
  have hFilter : IsLatticeFilter F := by
    constructor
    · by_contra hTop
      have hTopLe : ⊤ ≤ p := by
        have hTopSet : ⊤ ∈ ({x : L | x ≤ p} : Set L) := by
          rw [← hpCompl]
          exact hTop
        exact hTopSet
      exact hpPrime.1 (le_antisymm le_top hTopLe)
    · constructor
      · intro x y hxF hxy
        by_contra hyF
        have hyLe : y ≤ p := by
          have hySet : y ∈ ({z : L | z ≤ p} : Set L) := by
            rw [← hpCompl]
            exact hyF
          exact hySet
        have hxComp : x ∈ Fᶜ := by
          rw [hpCompl]
          exact le_trans hxy hyLe
        exact hxComp hxF
      · intro x y hxF hyF
        by_contra hInfF
        have hInfLe : x ⊓ y ≤ p := by
          have hInfSet : x ⊓ y ∈ ({z : L | z ≤ p} : Set L) := by
            rw [← hpCompl]
            exact hInfF
          exact hInfSet
        have hPairFinite : ({x, y} : Set L).Finite :=
          (Set.finite_singleton y).insert x
        have hPairInf : sInf ({x, y} : Set L) ≤ p := by
          simpa [sInf_pair] using hInfLe
        rcases hpPrime.2 ({x, y} : Set L) hPairFinite hPairInf with
          ⟨z, hzPair, hzLe⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzPair
        have hzComp : z ∈ Fᶜ := by
          rw [hpCompl]
          exact hzLe
        rcases hzPair with hzEq | hzEq
        · have hzF : z ∈ F := by
            rw [hzEq]
            exact hxF
          exact hzComp hzF
        · have hzF : z ∈ F := by
            rw [hzEq]
            exact hyF
          exact hzComp hzF
  constructor
  · exact hFilter
  · intro M hSupF
    by_contra hNo
    push Not at hNo
    have hSupLe : sSup M ≤ p := by
      refine sSup_le ?_
      intro x hxM
      have hxComp : x ∈ Fᶜ := hNo x hxM
      simpa [hpCompl] using hxComp
    have hSupComp : sSup M ∈ Fᶜ := by
      simpa [hpCompl] using hSupLe
    exact hSupComp hSupF

/-- The finite-meet-prime complement characterization of completely prime filters. -/
theorem completelyPrimeFilter_iff_finiteMeetPrime_complement
    {L : Type u} [CompleteLattice L] {F : Set L} :
    IsCompletelyPrimeFilter F ↔
      ∃ p : L, IsFiniteMeetPrime p ∧ Fᶜ = {x : L | x ≤ p} := by
  constructor
  · intro hF
    exact ⟨sSup (Fᶜ : Set L), completelyPrimeFilter_complement_finiteMeetPrime hF⟩
  · intro h
    rcases h with ⟨p, hpPrime, hpCompl⟩
    exact completelyPrimeFilter_of_finiteMeetPrime_complement hpPrime hpCompl

/-- The characteristic map of a completely prime filter is a frame
homomorphism into `Prop`. -/
theorem characteristicFrameHom_of_completelyPrimeFilter
    {L : Type u} [CompleteLattice L] {F : Set L}
    (hF : IsCompletelyPrimeFilter F) :
    HasCharacteristicFrameHom F := by
  let χ : FrameHom L Prop :=
    { toFun := fun x : L => x ∈ F
      map_sSup := by
        intro S
        apply propext
        rw [sSup_Prop_eq]
        constructor
        · intro hSup
          rcases hF.2 S hSup with ⟨x, hxS, hxF⟩
          exact ⟨x ∈ F, ⟨x, hxS, rfl⟩, hxF⟩
        · intro h
          rcases h with ⟨p, hpImage, hp⟩
          rcases hpImage with ⟨x, hxS, rfl⟩
          exact hF.1.2.1 hp (le_sSup hxS)
      map_top := propext (iff_true_intro hF.1.1)
      map_inf := by
        intro x y
        apply propext
        constructor
        · intro hxy
          exact ⟨hF.1.2.1 hxy inf_le_left, hF.1.2.1 hxy inf_le_right⟩
        · intro hxy
          exact hF.1.2.2 hxy.1 hxy.2 }
  exact ⟨χ, fun _ => rfl⟩

/-- A characteristic frame homomorphism into `Prop` determines a completely
prime filter. -/
theorem completelyPrimeFilter_of_characteristicFrameHom
    {L : Type u} [CompleteLattice L] {F : Set L}
    (hChar : HasCharacteristicFrameHom F) :
    IsCompletelyPrimeFilter F := by
  classical
  rcases hChar with ⟨χ, hχ⟩
  have hFilter : IsLatticeFilter F := by
    constructor
    · have hTop : χ.toFun ⊤ := by
        rw [χ.map_top]
        trivial
      simpa [hχ ⊤] using hTop
    · constructor
      · intro x y hxF hxy
        have hxχ : χ.toFun x := by
          simpa [hχ x] using hxF
        have hSupχ : sSup (χ.toFun '' ({x, y} : Set L)) := by
          rw [sSup_Prop_eq]
          exact ⟨χ.toFun x, ⟨x, by simp, rfl⟩, hxχ⟩
        have hsSupPair : sSup ({x, y} : Set L) = y := by
          rw [sSup_pair]
          exact sup_eq_right.mpr hxy
        have hyχ : χ.toFun y := by
          rw [← hsSupPair, χ.map_sSup ({x, y} : Set L)]
          exact hSupχ
        simpa [hχ y] using hyχ
      · intro x y hxF hyF
        have hxχ : χ.toFun x := by
          simpa [hχ x] using hxF
        have hyχ : χ.toFun y := by
          simpa [hχ y] using hyF
        have hInfχ : χ.toFun (x ⊓ y) := by
          rw [χ.map_inf x y]
          exact ⟨hxχ, hyχ⟩
        simpa [hχ (x ⊓ y)] using hInfχ
  constructor
  · exact hFilter
  · intro M hSupF
    have hSupχ : χ.toFun (sSup M) := by
      simpa [hχ (sSup M)] using hSupF
    have hImageSup : sSup (χ.toFun '' M) := by
      rw [← χ.map_sSup M]
      exact hSupχ
    rw [sSup_Prop_eq] at hImageSup
    rcases hImageSup with ⟨p, hpImage, hp⟩
    rcases hpImage with ⟨x, hxM, rfl⟩
    exact ⟨x, hxM, by simpa [hχ x] using hp⟩

/-- The characteristic-frame-homomorphism characterization of completely prime
filters. -/
theorem completelyPrimeFilter_iff_characteristicFrameHom
    {L : Type u} [CompleteLattice L] {F : Set L} :
    IsCompletelyPrimeFilter F ↔ HasCharacteristicFrameHom F := by
  constructor
  · exact characteristicFrameHom_of_completelyPrimeFilter
  · exact completelyPrimeFilter_of_characteristicFrameHom

/-- The frame law specializes to binary distributivity over joins. -/
theorem frameDistributive_inf_sup_pair
    {L : Type u} [CompleteLattice L] (hFrame : IsFrameDistributive L)
    (a b c : L) :
    a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  have hImage :
      ((fun y : L => a ⊓ y) '' ({b, c} : Set L)) =
        ({a ⊓ b, a ⊓ c} : Set L) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨y, hyPair, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hyPair ⊢
      rcases hyPair with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨b, by simp, rfl⟩
      · exact ⟨c, by simp, rfl⟩
  calc
    a ⊓ (b ⊔ c) = sSup ((fun y : L => a ⊓ y) '' ({b, c} : Set L)) := by
      rw [← sSup_pair]
      exact hFrame a ({b, c} : Set L)
    _ = sSup ({a ⊓ b, a ⊓ c} : Set L) := by
      rw [hImage]
    _ = a ⊓ b ⊔ a ⊓ c := sSup_pair

/-- The coframe law specializes to binary distributivity over meets. -/
theorem coframeDistributive_sup_inf_pair
    {L : Type u} [CompleteLattice L] (hCoframe : IsCoframeDistributive L)
    (a b c : L) :
    a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  have hImage :
      ((fun y : L => a ⊔ y) '' ({b, c} : Set L)) =
        ({a ⊔ b, a ⊔ c} : Set L) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨y, hyPair, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hyPair ⊢
      rcases hyPair with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨b, by simp, rfl⟩
      · exact ⟨c, by simp, rfl⟩
  calc
    a ⊔ (b ⊓ c) = sInf ((fun y : L => a ⊔ y) '' ({b, c} : Set L)) := by
      rw [← sInf_pair]
      exact hCoframe a ({b, c} : Set L)
    _ = sInf ({a ⊔ b, a ⊔ c} : Set L) := by
      rw [hImage]
    _ = (a ⊔ b) ⊓ (a ⊔ c) := sInf_pair

/-- Finite meet-primality implies finite meet-irreducibility. -/
theorem finiteMeetPrime_isFiniteMeetIrreducible
    {L : Type u} [CompleteLattice L] {p : L}
    (hp : IsFiniteMeetPrime p) :
    IsFiniteMeetIrreducible p := by
  constructor
  · exact hp.1
  · intro M hM hEq
    rcases hp.2 M hM (by rw [← hEq]) with ⟨m, hmM, hmp⟩
    exact ⟨m, hmM, le_antisymm (by
      rw [hEq]
      exact sInf_le hmM) hmp⟩

/-- Finite join-primality implies finite join-irreducibility. -/
theorem finiteJoinPrime_isFiniteJoinIrreducible
    {L : Type u} [CompleteLattice L] {p : L}
    (hp : IsFiniteJoinPrime p) :
    IsFiniteJoinIrreducible p := by
  constructor
  · exact hp.1
  · intro M hM hEq
    rcases hp.2 M hM (by rw [← hEq]) with ⟨m, hmM, hpm⟩
    exact ⟨m, hmM, le_antisymm hpm (by
      rw [hEq]
      exact le_sSup hmM)⟩

/-- Under coframe distributivity, finite join-irreducibility gives the binary
join-prime implication. -/
theorem finiteJoinIrreducible_binary_joinPrime_of_coframe
    {L : Type u} [CompleteLattice L] (hCoframe : IsCoframeDistributive L)
    {p a b : L} (hp : IsFiniteJoinIrreducible p) (hab : p ≤ a ⊔ b) :
    p ≤ a ∨ p ≤ b := by
  have hPairFinite : ({p ⊓ a, p ⊓ b} : Set L).Finite :=
    (Set.finite_singleton (p ⊓ b)).insert (p ⊓ a)
  have hEq : p = sSup ({p ⊓ a, p ⊓ b} : Set L) := by
    rw [sSup_pair]
    have hSupEq :
        (p ⊓ a) ⊔ (p ⊓ b) = p ⊓ ((p ⊓ a) ⊔ b) := by
      calc
        (p ⊓ a) ⊔ (p ⊓ b) =
            ((p ⊓ a) ⊔ p) ⊓ ((p ⊓ a) ⊔ b) := by
          exact coframeDistributive_sup_inf_pair hCoframe (p ⊓ a) p b
        _ = p ⊓ ((p ⊓ a) ⊔ b) := by
          rw [sup_eq_right.mpr inf_le_left]
    have hpLeRest : p ≤ (p ⊓ a) ⊔ b := by
      calc
        p ≤ (b ⊔ p) ⊓ (b ⊔ a) := by
          refine le_inf ?_ ?_
          · exact le_sup_right
          · simpa [sup_comm, sup_left_comm, sup_assoc] using hab
        _ = b ⊔ (p ⊓ a) := by
          exact (coframeDistributive_sup_inf_pair hCoframe b p a).symm
        _ = (p ⊓ a) ⊔ b := sup_comm _ _
    apply le_antisymm
    · rw [hSupEq]
      exact le_inf le_rfl hpLeRest
    · exact sup_le inf_le_left inf_le_left
  rcases hp.2 ({p ⊓ a, p ⊓ b} : Set L) hPairFinite hEq with
    ⟨m, hmPair, hpm⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmPair
  rcases hmPair with hm | hm
  · left
    have hpEq : p = p ⊓ a := by
      simpa [hm] using hpm
    rw [hpEq]
    exact inf_le_right
  · right
    have hpEq : p = p ⊓ b := by
      simpa [hm] using hpm
    rw [hpEq]
    exact inf_le_right

/-- Under coframe distributivity, finite join-irreducibility and finite
join-primality coincide in the dual direction to Proposition 7.1.6. -/
theorem finiteJoinPrime_of_finiteJoinIrreducible_of_coframe
    {L : Type u} [CompleteLattice L] (hCoframe : IsCoframeDistributive L)
    {p : L} (hp : IsFiniteJoinIrreducible p) :
    IsFiniteJoinPrime p := by
  classical
  constructor
  · exact hp.1
  · intro M hM
    refine Set.Finite.induction_on
      (motive := fun M _ => p ≤ sSup M → ∃ m ∈ M, p ≤ m)
      M hM ?_ ?_
    · intro hSupLe
      have hpBot : p = ⊥ := by
        apply le_antisymm
        · simpa using hSupLe
        exact bot_le
      exact False.elim (hp.1 hpBot)
    · intro x M _hxM _hM ih hSupLe
      have hJoinLe : p ≤ x ⊔ sSup M := by
        simpa [sSup_insert] using hSupLe
      rcases finiteJoinIrreducible_binary_joinPrime_of_coframe hCoframe hp hJoinLe with
        hx | hRest
      · exact ⟨x, Set.mem_insert x M, hx⟩
      · rcases ih hRest with ⟨m, hmM, hmp⟩
        exact ⟨m, Set.mem_insert_of_mem x hmM, hmp⟩

/-- Under frame distributivity, finite meet-irreducibility gives the binary
meet-prime implication. -/
theorem finiteMeetIrreducible_binary_meetPrime_of_frame
    {L : Type u} [CompleteLattice L] (hFrame : IsFrameDistributive L)
    {p a b : L} (hp : IsFiniteMeetIrreducible p) (hab : a ⊓ b ≤ p) :
    a ≤ p ∨ b ≤ p := by
  have hPairFinite : ({p ⊔ a, p ⊔ b} : Set L).Finite :=
    (Set.finite_singleton (p ⊔ b)).insert (p ⊔ a)
  have hEq : p = sInf ({p ⊔ a, p ⊔ b} : Set L) := by
    rw [sInf_pair]
    apply le_antisymm
    · exact le_inf le_sup_left le_sup_left
    · calc
        (p ⊔ a) ⊓ (p ⊔ b) =
            (p ⊔ a) ⊓ p ⊔ (p ⊔ a) ⊓ b := by
          exact frameDistributive_inf_sup_pair hFrame (p ⊔ a) p b
        _ ≤ p := by
          refine sup_le ?_ ?_
          · exact inf_le_right
          · calc
              (p ⊔ a) ⊓ b = b ⊓ (p ⊔ a) := inf_comm _ _
              _ = b ⊓ p ⊔ b ⊓ a := frameDistributive_inf_sup_pair hFrame b p a
              _ ≤ p := by
                refine sup_le ?_ ?_
                · exact inf_le_right
                · simpa [inf_comm] using hab
  rcases hp.2 ({p ⊔ a, p ⊔ b} : Set L) hPairFinite hEq with
    ⟨m, hmPair, hpm⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmPair
  rcases hmPair with hm | hm
  · left
    have ha : a ≤ p ⊔ a := le_sup_right
    rw [← hm, ← hpm] at ha
    exact ha
  · right
    have hb : b ≤ p ⊔ b := le_sup_right
    rw [← hm, ← hpm] at hb
    exact hb

/-- Under frame distributivity, finite meet-irreducibility and finite
meet-primality coincide in the direction needed for Proposition 7.1.6. -/
theorem finiteMeetPrime_of_finiteMeetIrreducible_of_frame
    {L : Type u} [CompleteLattice L] (hFrame : IsFrameDistributive L)
    {p : L} (hp : IsFiniteMeetIrreducible p) :
    IsFiniteMeetPrime p := by
  classical
  constructor
  · exact hp.1
  · intro M hM
    refine Set.Finite.induction_on
      (motive := fun M _ => sInf M ≤ p → ∃ m ∈ M, m ≤ p)
      M hM ?_ ?_
    · intro hInfLe
      have hpTop : p = ⊤ := by
        apply le_antisymm le_top
        simpa using hInfLe
      exact False.elim (hp.1 hpTop)
    · intro x M _hxM _hM ih hInfLe
      have hMeetLe : x ⊓ sInf M ≤ p := by
        simpa [sInf_insert] using hInfLe
      rcases finiteMeetIrreducible_binary_meetPrime_of_frame hFrame hp hMeetLe with hx | hRest
      · exact ⟨x, Set.mem_insert x M, hx⟩
      · rcases ih hRest with ⟨m, hmM, hmp⟩
        exact ⟨m, Set.mem_insert_of_mem x hmM, hmp⟩

/-- Meet-generation by finite meet-primes lets inequalities into an element be
checked against all finite meet-prime upper bounds of that element. -/
theorem le_of_forall_finiteMeetPrime_above_of_meetGenerated
    {L : Type u} [CompleteLattice L]
    (hGen : MeetGeneratedBy ({p : L | IsFiniteMeetPrime p}))
    {a b : L}
    (h : ∀ p : L, IsFiniteMeetPrime p → a ≤ p → b ≤ p) :
    b ≤ a := by
  rw [hGen a]
  exact le_sInf (by
    intro p hp
    exact h p hp.1 hp.2)

/-- If a supremum is not below `p`, then some member is not below `p`. -/
theorem exists_mem_not_le_of_not_sSup_le
    {L : Type u} [CompleteLattice L] {A : Set L} {p : L}
    (h : ¬ sSup A ≤ p) :
    ∃ a ∈ A, ¬ a ≤ p := by
  classical
  by_contra hnone
  apply h
  refine sSup_le ?_
  intro a ha
  by_contra hap
  exact hnone ⟨a, ha, hap⟩

/-- Meet-generation by finite meet-primes implies frame distributivity. -/
theorem frameDistributive_of_meetGeneratedBy_finiteMeetPrime
    {L : Type u} [CompleteLattice L]
    (hGen : MeetGeneratedBy ({p : L | IsFiniteMeetPrime p})) :
    IsFrameDistributive L := by
  classical
  intro x S
  have hImageLe :
      sSup ((fun y : L => x ⊓ y) '' S) ≤ x ⊓ sSup S := by
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨y, hyS, rfl⟩
    exact le_inf inf_le_left (inf_le_right.trans (le_sSup hyS))
  have hLeftLe :
      x ⊓ sSup S ≤ sSup ((fun y : L => x ⊓ y) '' S) := by
    refine le_of_forall_finiteMeetPrime_above_of_meetGenerated
      hGen (a := sSup ((fun y : L => x ⊓ y) '' S)) (b := x ⊓ sSup S) ?_
    intro p hp hImageP
    by_cases hx : x ≤ p
    · exact inf_le_left.trans hx
    · have hSle : sSup S ≤ p := by
        refine sSup_le ?_
        intro y hyS
        have hxyLeP : x ⊓ y ≤ p := by
          exact (le_sSup (show x ⊓ y ∈ (fun y : L => x ⊓ y) '' S from
            ⟨y, hyS, rfl⟩)).trans hImageP
        have hInfLeP : sInf ({x, y} : Set L) ≤ p := by
          simpa [sInf_pair] using hxyLeP
        have hPairFinite : ({x, y} : Set L).Finite :=
          (Set.finite_singleton y).insert x
        rcases hp.2 ({x, y} : Set L) hPairFinite hInfLeP with
          ⟨m, hmPair, hmp⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmPair
        rcases hmPair with rfl | rfl
        · exact False.elim (hx hmp)
        · exact hmp
      exact inf_le_right.trans hSle
  exact le_antisymm hLeftLe hImageLe

/-- Meet-generation by finite meet-primes gives the finite-meet/arbitrary-join
choice distributivity law. -/
theorem finiteMeetJoinChoiceLaw_of_meetGeneratedBy_finiteMeetPrime
    {L : Type u} [CompleteLattice L]
    (hGen : MeetGeneratedBy ({p : L | IsFiniteMeetPrime p})) :
    FiniteMeetJoinChoiceLaw.{u, v} L := by
  classical
  intro ι hι A
  let choices : Set L :=
    {x : L |
      ∃ f : ∀ i : ι, {a : L // a ∈ A i},
        x = sInf (Set.range (fun i : ι => (f i).1))}
  have hChoicesLe :
      sSup choices ≤ sInf (Set.range (fun i : ι => sSup (A i))) := by
    refine sSup_le ?_
    intro x hx
    rcases hx with ⟨f, rfl⟩
    refine le_sInf ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact (sInf_le (show (f i).1 ∈ Set.range (fun i : ι => (f i).1) from
      ⟨i, rfl⟩)).trans (le_sSup (f i).2)
  have hInfLeChoices :
      sInf (Set.range (fun i : ι => sSup (A i))) ≤ sSup choices := by
    refine le_of_forall_finiteMeetPrime_above_of_meetGenerated
      hGen (a := sSup choices)
        (b := sInf (Set.range (fun i : ι => sSup (A i)))) ?_
    intro p hp hChoicesP
    by_contra hInfNotLe
    letI : Fintype ι := Fintype.ofFinite ι
    have hNoSup : ∀ i : ι, ¬ sSup (A i) ≤ p := by
      intro i hSupLe
      exact hInfNotLe ((sInf_le
        (show sSup (A i) ∈ Set.range (fun i : ι => sSup (A i)) from
          ⟨i, rfl⟩)).trans hSupLe)
    have hExists : ∀ i : ι, ∃ a ∈ A i, ¬ a ≤ p := by
      intro i
      exact exists_mem_not_le_of_not_sSup_le (hNoSup i)
    let f : ∀ i : ι, {a : L // a ∈ A i} := fun i =>
      ⟨Classical.choose (hExists i), (Classical.choose_spec (hExists i)).1⟩
    have hfNot : ∀ i : ι, ¬ (f i).1 ≤ p := by
      intro i
      exact (Classical.choose_spec (hExists i)).2
    have hChoiceMem :
        sInf (Set.range (fun i : ι => (f i).1)) ∈ choices := by
      exact ⟨f, rfl⟩
    have hChoiceLeP : sInf (Set.range (fun i : ι => (f i).1)) ≤ p := by
      exact (le_sSup hChoiceMem).trans hChoicesP
    have hChoiceFinite : (Set.range (fun i : ι => (f i).1)).Finite :=
      Set.finite_range (fun i : ι => (f i).1)
    rcases hp.2 (Set.range (fun i : ι => (f i).1)) hChoiceFinite hChoiceLeP with
      ⟨m, hmRange, hmp⟩
    rcases hmRange with ⟨i, rfl⟩
    exact (hfNot i) hmp
  exact le_antisymm hInfLeChoices hChoicesLe

/-- Meet-generation by finite meet-primes gives the arbitrary-join/finite-meet
choice distributivity law. -/
theorem joinFiniteMeetChoiceLaw_of_meetGeneratedBy_finiteMeetPrime
    {L : Type u} [CompleteLattice L]
    (hGen : MeetGeneratedBy ({p : L | IsFiniteMeetPrime p})) :
    JoinFiniteMeetChoiceLaw.{u, v} L := by
  classical
  intro ι M hM
  let choices : Set L :=
    {x : L |
      ∃ f : ∀ i : ι, {a : L // a ∈ M i},
        x = sSup (Set.range (fun i : ι => (f i).1))}
  have hSupLeChoices :
      sSup (Set.range (fun i : ι => sInf (M i))) ≤ sInf choices := by
    refine le_sInf ?_
    intro x hx
    rcases hx with ⟨f, rfl⟩
    refine sSup_le ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact (sInf_le (f i).2).trans
      (le_sSup (show (f i).1 ∈ Set.range (fun i : ι => (f i).1) from
        ⟨i, rfl⟩))
  have hChoicesLeSup :
      sInf choices ≤ sSup (Set.range (fun i : ι => sInf (M i))) := by
    refine le_of_forall_finiteMeetPrime_above_of_meetGenerated
      hGen (a := sSup (Set.range (fun i : ι => sInf (M i)))) (b := sInf choices) ?_
    intro p hp hSupP
    have hInfLeP : ∀ i : ι, sInf (M i) ≤ p := by
      intro i
      exact (le_sSup
        (show sInf (M i) ∈ Set.range (fun i : ι => sInf (M i)) from
          ⟨i, rfl⟩)).trans hSupP
    have hExists : ∀ i : ι, ∃ m ∈ M i, m ≤ p := by
      intro i
      exact hp.2 (M i) (hM i) (hInfLeP i)
    let f : ∀ i : ι, {a : L // a ∈ M i} := fun i =>
      ⟨Classical.choose (hExists i), (Classical.choose_spec (hExists i)).1⟩
    have hfLe : ∀ i : ι, (f i).1 ≤ p := by
      intro i
      exact (Classical.choose_spec (hExists i)).2
    have hChoiceMem :
        sSup (Set.range (fun i : ι => (f i).1)) ∈ choices := by
      exact ⟨f, rfl⟩
    have hChoiceLeP : sSup (Set.range (fun i : ι => (f i).1)) ≤ p := by
      refine sSup_le ?_
      intro y hy
      rcases hy with ⟨i, rfl⟩
      exact hfLe i
    exact (sInf_le hChoiceMem).trans hChoiceLeP
  exact le_antisymm hSupLeChoices hChoicesLeSup

/-- Join-generation by finite join-primes lets inequalities out of an element be
checked against all finite join-prime lower bounds of that element. -/
theorem le_of_forall_finiteJoinPrime_below_of_joinGenerated
    {L : Type u} [CompleteLattice L]
    (hGen : JoinGeneratedBy ({p : L | IsFiniteJoinPrime p}))
    {a b : L}
    (h : ∀ p : L, IsFiniteJoinPrime p → p ≤ a → p ≤ b) :
    a ≤ b := by
  rw [hGen a]
  exact sSup_le (by
    intro p hp
    exact h p hp.1 hp.2)

/-- If `p` is not below an infimum, then it is not below some member. -/
theorem exists_mem_not_le_of_not_le_sInf
    {L : Type u} [CompleteLattice L] {A : Set L} {p : L}
    (h : ¬ p ≤ sInf A) :
    ∃ a ∈ A, ¬ p ≤ a := by
  classical
  by_contra hnone
  apply h
  refine le_sInf ?_
  intro a ha
  by_contra hpa
  exact hnone ⟨a, ha, hpa⟩

/-- Join-generation by finite join-primes implies coframe distributivity. -/
theorem coframeDistributive_of_joinGeneratedBy_finiteJoinPrime
    {L : Type u} [CompleteLattice L]
    (hGen : JoinGeneratedBy ({p : L | IsFiniteJoinPrime p})) :
    IsCoframeDistributive L := by
  classical
  intro x S
  have hLeftLe :
      x ⊔ sInf S ≤ sInf ((fun y : L => x ⊔ y) '' S) := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨y, hyS, rfl⟩
    exact sup_le_sup_left (sInf_le hyS) x
  have hImageLe :
      sInf ((fun y : L => x ⊔ y) '' S) ≤ x ⊔ sInf S := by
    refine le_of_forall_finiteJoinPrime_below_of_joinGenerated
      hGen (a := sInf ((fun y : L => x ⊔ y) '' S)) (b := x ⊔ sInf S) ?_
    intro p hp hPImage
    by_cases hx : p ≤ x
    · exact hx.trans le_sup_left
    · have hPleS : p ≤ sInf S := by
        refine le_sInf ?_
        intro y hyS
        have hpLeXY : p ≤ x ⊔ y := by
          exact hPImage.trans (sInf_le
            (show x ⊔ y ∈ (fun y : L => x ⊔ y) '' S from ⟨y, hyS, rfl⟩))
        have hpLeSup : p ≤ sSup ({x, y} : Set L) := by
          simpa [sSup_pair] using hpLeXY
        have hPairFinite : ({x, y} : Set L).Finite :=
          (Set.finite_singleton y).insert x
        rcases hp.2 ({x, y} : Set L) hPairFinite hpLeSup with
          ⟨m, hmPair, hpm⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmPair
        rcases hmPair with rfl | rfl
        · exact False.elim (hx hpm)
        · exact hpm
      exact hPleS.trans le_sup_right
  exact le_antisymm hLeftLe hImageLe

/-- Join-generation by finite join-primes gives the finite-join/arbitrary-meet
choice distributivity law. -/
theorem finiteJoinMeetChoiceLaw_of_joinGeneratedBy_finiteJoinPrime
    {L : Type u} [CompleteLattice L]
    (hGen : JoinGeneratedBy ({p : L | IsFiniteJoinPrime p})) :
    FiniteJoinMeetChoiceLaw.{u, v} L := by
  classical
  intro ι hι A
  let choices : Set L :=
    {x : L |
      ∃ f : ∀ i : ι, {a : L // a ∈ A i},
        x = sSup (Set.range (fun i : ι => (f i).1))}
  have hLeftLeChoices :
      sSup (Set.range (fun i : ι => sInf (A i))) ≤ sInf choices := by
    refine le_sInf ?_
    intro x hx
    rcases hx with ⟨f, rfl⟩
    refine sSup_le ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact (sInf_le (f i).2).trans
      (le_sSup (show (f i).1 ∈ Set.range (fun i : ι => (f i).1) from
        ⟨i, rfl⟩))
  have hChoicesLeLeft :
      sInf choices ≤ sSup (Set.range (fun i : ι => sInf (A i))) := by
    refine le_of_forall_finiteJoinPrime_below_of_joinGenerated
      hGen (a := sInf choices)
        (b := sSup (Set.range (fun i : ι => sInf (A i)))) ?_
    intro p hp hPChoices
    by_contra hpNotLeft
    letI : Fintype ι := Fintype.ofFinite ι
    have hNoInf : ∀ i : ι, ¬ p ≤ sInf (A i) := by
      intro i hPInf
      exact hpNotLeft (hPInf.trans (le_sSup
        (show sInf (A i) ∈ Set.range (fun i : ι => sInf (A i)) from
          ⟨i, rfl⟩)))
    have hExists : ∀ i : ι, ∃ a ∈ A i, ¬ p ≤ a := by
      intro i
      exact exists_mem_not_le_of_not_le_sInf (hNoInf i)
    let f : ∀ i : ι, {a : L // a ∈ A i} := fun i =>
      ⟨Classical.choose (hExists i), (Classical.choose_spec (hExists i)).1⟩
    have hfNot : ∀ i : ι, ¬ p ≤ (f i).1 := by
      intro i
      exact (Classical.choose_spec (hExists i)).2
    have hChoiceMem :
        sSup (Set.range (fun i : ι => (f i).1)) ∈ choices := by
      exact ⟨f, rfl⟩
    have hpLeChoice : p ≤ sSup (Set.range (fun i : ι => (f i).1)) := by
      exact hPChoices.trans (sInf_le hChoiceMem)
    have hChoiceFinite : (Set.range (fun i : ι => (f i).1)).Finite :=
      Set.finite_range (fun i : ι => (f i).1)
    rcases hp.2 (Set.range (fun i : ι => (f i).1)) hChoiceFinite hpLeChoice with
      ⟨m, hmRange, hpm⟩
    rcases hmRange with ⟨i, rfl⟩
    exact (hfNot i) hpm
  exact le_antisymm hLeftLeChoices hChoicesLeLeft

/-- Join-generation by finite join-primes gives the arbitrary-meet/finite-join
choice distributivity law. -/
theorem meetFiniteJoinChoiceLaw_of_joinGeneratedBy_finiteJoinPrime
    {L : Type u} [CompleteLattice L]
    (hGen : JoinGeneratedBy ({p : L | IsFiniteJoinPrime p})) :
    MeetFiniteJoinChoiceLaw.{u, v} L := by
  classical
  intro ι M hM
  let choices : Set L :=
    {x : L |
      ∃ f : ∀ i : ι, {a : L // a ∈ M i},
        x = sInf (Set.range (fun i : ι => (f i).1))}
  have hChoicesLeLeft :
      sSup choices ≤ sInf (Set.range (fun i : ι => sSup (M i))) := by
    refine sSup_le ?_
    intro x hx
    rcases hx with ⟨f, rfl⟩
    refine le_sInf ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact (sInf_le (show (f i).1 ∈ Set.range (fun i : ι => (f i).1) from
      ⟨i, rfl⟩)).trans (le_sSup (f i).2)
  have hLeftLeChoices :
      sInf (Set.range (fun i : ι => sSup (M i))) ≤ sSup choices := by
    refine le_of_forall_finiteJoinPrime_below_of_joinGenerated
      hGen (a := sInf (Set.range (fun i : ι => sSup (M i)))) (b := sSup choices) ?_
    intro p hp hPLeft
    have hPJoin : ∀ i : ι, p ≤ sSup (M i) := by
      intro i
      exact hPLeft.trans (sInf_le
        (show sSup (M i) ∈ Set.range (fun i : ι => sSup (M i)) from
          ⟨i, rfl⟩))
    have hExists : ∀ i : ι, ∃ m ∈ M i, p ≤ m := by
      intro i
      exact hp.2 (M i) (hM i) (hPJoin i)
    let f : ∀ i : ι, {a : L // a ∈ M i} := fun i =>
      ⟨Classical.choose (hExists i), (Classical.choose_spec (hExists i)).1⟩
    have hPLeF : ∀ i : ι, p ≤ (f i).1 := by
      intro i
      exact (Classical.choose_spec (hExists i)).2
    have hChoiceMem :
        sInf (Set.range (fun i : ι => (f i).1)) ∈ choices := by
      exact ⟨f, rfl⟩
    have hPInf : p ≤ sInf (Set.range (fun i : ι => (f i).1)) := by
      refine le_sInf ?_
      intro y hy
      rcases hy with ⟨i, rfl⟩
      exact hPLeF i
    exact hPInf.trans (le_sSup hChoiceMem)
  exact le_antisymm hLeftLeChoices hChoicesLeLeft

/-- Proposition 7.1.11: the three alternative characterizations of completely
prime filters. -/
structure CompletePrimeFilterCharacterizations
    (L : Type u) [CompleteLattice L] (F : Set L) : Prop where
  principal_complement :
    IsCompletelyPrimeFilter F ↔ IsLatticeFilter F ∧ HasPrincipalIdealComplement F
  meet_prime_complement :
    IsCompletelyPrimeFilter F ↔
      ∃ x : L, IsFiniteMeetPrime x ∧ Fᶜ = {y : L | y ≤ x}
  characteristic_hom :
    IsCompletelyPrimeFilter F ↔ HasCharacteristicFrameHom F

/-- Definition 7.1.12: points of a complete lattice are completely prime filters. -/
def Point (L : Type u) [CompleteLattice L] : Type u :=
  {F : Set L // IsCompletelyPrimeFilter F}

/-- Definition 7.1.12: the basic open `O_x` of the point space. -/
def pointBasicOpen {L : Type u} [CompleteLattice L] (x : L) : Set (Point L) :=
  {F : Point L | x ∈ F.1}

/-- Definition 7.1.12: generated opens of the point space. -/
inductive PointOpen (L : Type u) [CompleteLattice L] : Set (Point L) → Prop where
  | basic (x : L) : PointOpen L (pointBasicOpen x)
  | univ : PointOpen L Set.univ
  | inter {U V : Set (Point L)} :
      PointOpen L U → PointOpen L V → PointOpen L (U ∩ V)
  | sUnion (S : Set (Set (Point L))) :
      (∀ U ∈ S, PointOpen L U) → PointOpen L (⋃₀ S)

/-- Definition 7.1.12: the topological space of points of a complete lattice. -/
def pointSpace (L : Type u) [CompleteLattice L] : Space.{u} where
  Point := Point L
  IsOpen := PointOpen L
  univ_open := PointOpen.univ
  inter_open := by
    intro U V hU hV
    exact PointOpen.inter hU hV
  sUnion_open := by
    intro S hS
    exact PointOpen.sUnion S hS

/-- Proposition 7.1.13 data: the basic opens `O_x` themselves satisfy the
topological closure laws from the proof in the PDF. -/
structure PointBasicOpenTopologyLaws (L : Type u) [CompleteLattice L] where
  top_eq_univ : pointBasicOpen (⊤ : L) = Set.univ
  inter_eq : ∀ x y : L,
    pointBasicOpen (x ⊓ y) = pointBasicOpen x ∩ pointBasicOpen y
  sUnion_eq : ∀ S : Set L,
    pointBasicOpen (sSup S) = ⋃₀ (pointBasicOpen '' S)
  basic_open : ∀ x : L, (pointSpace L).IsOpen (pointBasicOpen x)

/-- Definition 7.1.12, named book entry. -/
abbrev def_7_1_12_points_of_lattice (L : Type u) [CompleteLattice L] :=
  pointSpace L

/-- Continuous maps between the lightweight spaces used in Chapter 7. -/
structure StoneContinuousMap (X Y : Space.{u}) where
  toFun : X.Point → Y.Point
  preimage_open :
    ∀ U : Set Y.Point, Y.IsOpen U → X.IsOpen {x : X.Point | toFun x ∈ U}

namespace FrameHom

/-- A frame homomorphism is monotone. -/
theorem monotone {K : Type u} {L : Type v} [CompleteLattice K] [CompleteLattice L]
    (h : FrameHom K L) : Monotone h.toFun := by
  intro x y hxy
  have hInf : x ⊓ y = x := inf_eq_left.2 hxy
  calc
    h.toFun x = h.toFun (x ⊓ y) := congrArg h.toFun hInf.symm
    _ = h.toFun x ⊓ h.toFun y := h.map_inf x y
    _ ≤ h.toFun y := inf_le_right

end FrameHom

/-- The inverse-image frame homomorphism induced by a continuous map. -/
def openSetPreimageFrameHom {X Y : Space.{u}} (f : StoneContinuousMap X Y) :
    FrameHom (OpenSet Y) (OpenSet X) where
  toFun U := ⟨{ x : X.Point | f.toFun x ∈ U.1 }, f.preimage_open U.1 U.2⟩
  map_sSup := by
    intro S
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      rcases (OpenSet.mem_sSup_iff Y S (f.toFun x)).1 hx with ⟨U, hUS, hxU⟩
      exact (OpenSet.mem_sSup_iff X
        ((fun U : OpenSet Y =>
          (⟨{ x : X.Point | f.toFun x ∈ U.1 }, f.preimage_open U.1 U.2⟩ : OpenSet X)) '' S) x).2
            ⟨⟨{ x : X.Point | f.toFun x ∈ U.1 }, f.preimage_open U.1 U.2⟩,
              ⟨U, hUS, rfl⟩, hxU⟩
    · intro hx
      rcases (OpenSet.mem_sSup_iff X
        ((fun U : OpenSet Y =>
          (⟨{ x : X.Point | f.toFun x ∈ U.1 }, f.preimage_open U.1 U.2⟩ : OpenSet X)) '' S) x).1 hx with
        ⟨V, ⟨U, hUS, hUV⟩, hxV⟩
      subst V
      exact (OpenSet.mem_sSup_iff Y S (f.toFun x)).2 ⟨U, hUS, hxV⟩
  map_top := by
    apply Subtype.ext
    ext x
    change f.toFun x ∈ (⊤ : OpenSet Y).1 ↔ x ∈ (⊤ : OpenSet X).1
    rw [OpenSet.top_eq_univ Y, OpenSet.top_eq_univ X]
    simp
  map_inf := by
    intro U V
    apply Subtype.ext
    ext x
    change f.toFun x ∈ (U ⊓ V).1 ↔
      x ∈
        ((⟨{x : X.Point | f.toFun x ∈ U.1}, f.preimage_open U.1 U.2⟩ : OpenSet X) ⊓
          ⟨{x : X.Point | f.toFun x ∈ V.1}, f.preimage_open V.1 V.2⟩).1
    rw [OpenSet.inf_eq_inter Y U V]
    rw [OpenSet.inf_eq_inter X]
    rfl

/-- The inverse image of a completely prime filter under a frame homomorphism. -/
def frameHomPointPreimage {K L : Type u} [CompleteLattice K] [CompleteLattice L]
    (h : FrameHom K L) (F : Point L) : Point K := by
  refine ⟨{x : K | h.toFun x ∈ F.1}, ?_⟩
  constructor
  · constructor
    · change h.toFun ⊤ ∈ F.1
      rw [h.map_top]
      exact F.2.1.1
    · constructor
      · intro x y hx hxy
        exact F.2.1.2.1 hx (h.monotone hxy)
      · intro x y hx hy
        change h.toFun (x ⊓ y) ∈ F.1
        rw [h.map_inf]
        exact F.2.1.2.2 hx hy
  · intro S hSup
    have hImageSup : sSup (h.toFun '' S) ∈ F.1 := by
      rw [← h.map_sSup S]
      exact hSup
    rcases F.2.2 (h.toFun '' S) hImageSup with ⟨y, ⟨x, hxS, rfl⟩, hxF⟩
    exact ⟨x, hxS, hxF⟩

/-- The contravariant point-space action of a frame homomorphism. -/
def spectrumMapOfFrameHom {K L : Frame.{u}}
    (h : FrameHom K.carrier L.carrier) :
    StoneContinuousMap (pointSpace L.carrier) (pointSpace K.carrier) where
  toFun := frameHomPointPreimage h
  preimage_open := by
    intro U hU
    induction hU with
    | basic x =>
        simpa [frameHomPointPreimage, pointBasicOpen] using
          (PointOpen.basic (h.toFun x) :
            PointOpen L.carrier (pointBasicOpen (h.toFun x)))
    | univ =>
        simpa using (PointOpen.univ : PointOpen L.carrier Set.univ)
    | inter _hU _hV ihU ihV =>
        exact PointOpen.inter ihU ihV
    | sUnion S _hS ihS =>
        let T : Set (Set (Point L.carrier)) :=
          (fun V : Set (Point K.carrier) =>
            {F : Point L.carrier | frameHomPointPreimage h F ∈ V}) '' S
        have hT : ∀ V ∈ T, PointOpen L.carrier V := by
          intro V hVT
          rcases hVT with ⟨W, hWS, rfl⟩
          exact ihS W hWS
        have hOpen : PointOpen L.carrier (⋃₀ T) := PointOpen.sUnion T hT
        convert hOpen using 1
        ext F
        constructor
        · intro hF
          rcases hF with ⟨V, hVS, hFV⟩
          exact ⟨{G : Point L.carrier | frameHomPointPreimage h G ∈ V},
            ⟨V, hVS, rfl⟩, hFV⟩
        · intro hF
          rcases hF with ⟨V, ⟨W, hWS, hVW⟩, hFV⟩
          subst V
          exact ⟨W, hWS, hFV⟩

/-- The neighborhood filter of a point in the concrete lattice of opens. -/
def pointNeighborhoodFilter (X : Space.{u}) (x : X.Point) : Set (OpenSet X) :=
  {U : OpenSet X | x ∈ U.1}

theorem pointNeighborhoodFilter_completelyPrime
    (X : Space.{u}) (x : X.Point) :
    IsCompletelyPrimeFilter (pointNeighborhoodFilter X x) := by
  constructor
  · constructor
    · unfold pointNeighborhoodFilter
      change x ∈ (⊤ : OpenSet X).1
      rw [OpenSet.top_eq_univ X]
      exact Set.mem_univ x
    · constructor
      · intro U V hU hUV
        exact hUV hU
      · intro U V hU hV
        unfold pointNeighborhoodFilter at hU hV
        unfold pointNeighborhoodFilter
        change x ∈ (U ⊓ V).1
        rw [OpenSet.inf_eq_inter X U V]
        exact ⟨hU, hV⟩
  · intro S hSup
    unfold pointNeighborhoodFilter at hSup
    rcases (OpenSet.mem_sSup_iff X S x).1 hSup with ⟨U, hUS, hxU⟩
    exact ⟨U, hUS, hxU⟩

/-- A point of `pt(Omega(X))` represented by the neighborhoods of `x`. -/
def stoneUnitPoint (X : Space.{u}) (x : X.Point) : Point (OpenSet X) :=
  ⟨pointNeighborhoodFilter X x, pointNeighborhoodFilter_completelyPrime X x⟩

/-- The space-side unit `eta_X`, sending a point to its neighborhood filter. -/
def stoneUnitContinuous (X : Space.{u}) :
    StoneContinuousMap X (pointSpace (OpenSet X)) where
  toFun := stoneUnitPoint X
  preimage_open := by
    intro U hU
    induction hU with
    | basic V =>
        simpa [pointNeighborhoodFilter, pointBasicOpen] using V.2
    | univ =>
        simpa using X.univ_open
    | inter _hU _hV ihU ihV =>
        exact X.inter_open _ _ ihU ihV
    | sUnion S _hS ihS =>
        let T : Set (Set X.Point) :=
          (fun V : Set (Point (OpenSet X)) =>
            {x : X.Point | stoneUnitPoint X x ∈ V}) '' S
        have hT : ∀ V ∈ T, X.IsOpen V := by
          intro V hVT
          rcases hVT with ⟨W, hWS, rfl⟩
          exact ihS W hWS
        have hOpen : X.IsOpen (⋃₀ T) := X.sUnion_open T hT
        convert hOpen using 1
        ext x
        constructor
        · intro hx
          rcases hx with ⟨V, hVS, hxV⟩
          exact ⟨{x : X.Point | stoneUnitPoint X x ∈ V}, ⟨V, hVS, rfl⟩, hxV⟩
        · intro hx
          rcases hx with ⟨V, ⟨W, hWS, hVW⟩, hxV⟩
          subst V
          exact ⟨W, hWS, hxV⟩

/-- The lattice-side unit `epsilon_L`, sending `a` to its basic open `O_a`. -/
def stoneEpsilonFrameHom (L : Frame.{u}) :
    FrameHom L.carrier (OpenSet (pointSpace L.carrier)) where
  toFun a := ⟨pointBasicOpen a, PointOpen.basic a⟩
  map_sSup := by
    intro S
    apply Subtype.ext
    ext F
    constructor
    · intro hSup
      rcases F.2.2 S hSup with ⟨a, haS, haF⟩
      exact (OpenSet.mem_sSup_iff (pointSpace L.carrier)
        ((fun a : L.carrier =>
          (⟨pointBasicOpen a, PointOpen.basic a⟩ : OpenSet (pointSpace L.carrier))) '' S) F).2
            ⟨⟨pointBasicOpen a, PointOpen.basic a⟩, ⟨a, haS, rfl⟩, haF⟩
    · intro hUnion
      rcases (OpenSet.mem_sSup_iff (pointSpace L.carrier)
        ((fun a : L.carrier =>
          (⟨pointBasicOpen a, PointOpen.basic a⟩ : OpenSet (pointSpace L.carrier))) '' S) F).1
          hUnion with ⟨U, ⟨a, haS, hUa⟩, hFU⟩
      subst U
      exact F.2.1.2.1 hFU (le_sSup haS)
  map_top := by
    apply Subtype.ext
    ext F
    rw [OpenSet.top_eq_univ (pointSpace L.carrier)]
    constructor
    · intro _h
      exact Set.mem_univ F
    · intro _h
      exact F.2.1.1
  map_inf := by
    intro a b
    apply Subtype.ext
    ext F
    rw [OpenSet.inf_eq_inter (pointSpace L.carrier)]
    constructor
    · intro hab
      exact ⟨F.2.1.2.1 hab inf_le_left, F.2.1.2.1 hab inf_le_right⟩
    · intro hab
      exact F.2.1.2.2 hab.1 hab.2

/-- The concrete `Omega`/`pt` object maps and units. -/
def concreteStoneAdjunction : StoneAdjunction.{u} where
  opens X := ⟨OpenSet X, OpenSet.completeLattice X⟩
  spectrum L := @pointSpace L.carrier L.lattice
  unit X := (stoneUnitContinuous X).toFun
  epsilon L := (stoneEpsilonFrameHom L).toFun

/-- Data for the dual adjunction in Theorem 7.1.14.  The fields spell out the
contravariant action on maps, the unit `eta`, the lattice-side unit `epsilon`,
and the naturality/triangle equations described in the PDF. -/
structure StoneDualAdjunctionData where
  adjunction : StoneAdjunction.{u}
  opensMap :
    ∀ {X Y : Space.{u}}, StoneContinuousMap X Y →
      FrameHom (adjunction.opens Y).carrier (adjunction.opens X).carrier
  spectrumMap :
    ∀ {K L : Frame.{u}}, FrameHom K.carrier L.carrier →
      StoneContinuousMap (adjunction.spectrum L) (adjunction.spectrum K)
  unit_continuous :
    ∀ X : Space.{u}, StoneContinuousMap X (adjunction.spectrum (adjunction.opens X))
  unit_agrees :
    ∀ X : Space.{u}, ∀ x : X.Point, (unit_continuous X).toFun x = adjunction.unit X x
  epsilon_frame_hom :
    ∀ L : Frame.{u}, FrameHom L.carrier (adjunction.opens (adjunction.spectrum L)).carrier
  epsilon_agrees :
    ∀ L : Frame.{u}, ∀ a : L.carrier,
      (epsilon_frame_hom L).toFun a = adjunction.epsilon L a
  unit_naturality :
    ∀ {X Y : Space.{u}}, ∀ f : StoneContinuousMap X Y, ∀ x : X.Point,
      (spectrumMap (opensMap f)).toFun (adjunction.unit X x) =
        adjunction.unit Y (f.toFun x)
  epsilon_naturality :
    ∀ {K L : Frame.{u}}, ∀ h : FrameHom K.carrier L.carrier, ∀ a : K.carrier,
      (opensMap (spectrumMap h)).toFun (adjunction.epsilon K a) =
        adjunction.epsilon L (h.toFun a)
  left_triangle :
    ∀ X : Space.{u}, ∀ U : (adjunction.opens X).carrier,
      (opensMap (unit_continuous X)).toFun
          (adjunction.epsilon (adjunction.opens X) U) = U
  right_triangle :
    ∀ L : Frame.{u}, ∀ F : (adjunction.spectrum L).Point,
      (spectrumMap (epsilon_frame_hom L)).toFun
          ((unit_continuous (adjunction.spectrum L)).toFun F) = F

/-- The canonical supremum in a complete lattice satisfies the local `IsSup`
interface used by Chapter 2. -/
private theorem completeLattice_sSup_isSup
    (L : Type u) [CompleteLattice L] (A : Set L) :
    Chapter2.IsSup A (sSup A) := by
  constructor
  · intro a ha
    exact le_sSup ha
  · intro y hy
    exact sSup_le hy

/-- Theorem 7.1.1.  Complete-lattice continuity is equivalent to the directed
choice distributivity law.  The index type is quantified in the universe of
`L`, which is required by the converse's family of all directed subsets. -/
theorem theorem_7_1_1_complete_lattice_continuity_distributivity
    (L : Type u) [CompleteLattice L] :
    IsContinuousCompleteLattice L ↔ DirectedChoiceMeetJoinLaw.{u, u} L := by
  constructor
  · intro hContinuous ι A hDirected
    apply le_antisymm
    · rcases hContinuous.2 with ⟨B, hB⟩
      rcases hB (sInf (Set.range (fun i : ι => sSup (A i)))) with
        ⟨C, hCsub, _hCdirected, hCsup⟩
      apply hCsup.2
      intro c hcC
      have hcWayBelow :
          Chapter2.WayBelow c (sInf (Set.range (fun i : ι => sSup (A i)))) :=
        (hCsub hcC).2
      have hChoice : ∀ i : ι, ∃ a ∈ A i, c ≤ a := by
        intro i
        exact hcWayBelow (hDirected i)
          (completeLattice_sSup_isSup L (A i))
          (sInf_le ⟨i, rfl⟩)
      let f : ∀ i : ι, {a : L // a ∈ A i} := fun i =>
        ⟨Classical.choose (hChoice i), (Classical.choose_spec (hChoice i)).1⟩
      have hcf : c ≤ sInf (Set.range (fun i : ι => (f i).1)) := by
        apply le_sInf
        intro a ha
        rcases ha with ⟨i, rfl⟩
        exact (Classical.choose_spec (hChoice i)).2
      exact hcf.trans (le_sSup ⟨f, rfl⟩)
    · apply sSup_le
      intro y hy
      rcases hy with ⟨f, rfl⟩
      apply le_sInf
      intro z hz
      rcases hz with ⟨i, rfl⟩
      have hMeetLe :
          sInf (Set.range (fun j : ι => (f j).1)) ≤ (f i).1 :=
        sInf_le ⟨i, rfl⟩
      exact hMeetLe.trans (le_sSup (f i).2)
  · intro hLaw
    refine ⟨completeLattice_isDcpo L, ⟨Set.univ, ?_⟩⟩
    intro x
    let I := {A : Set L // Chapter2.DirectedSet A ∧ x ≤ sSup A}
    let family : I → Set L := fun i => i.1
    let choices : Set L :=
      {y : L |
        ∃ f : ∀ i : I, {a : L // a ∈ family i},
          y = sInf (Set.range (fun i : I => (f i).1))}
    have hFamilyDirected : ∀ i : I, Chapter2.DirectedSet (family i) :=
      fun i => i.2.1
    have hLeft :
        sInf (Set.range (fun i : I => sSup (family i))) = x := by
      apply le_antisymm
      · let ix : I := ⟨{x}, Chapter2.directed_singleton x, by simp⟩
        have hle :
            sInf (Set.range (fun i : I => sSup (family i))) ≤
              sSup (family ix) := sInf_le ⟨ix, rfl⟩
        simpa [family, ix] using hle
      · apply le_sInf
        intro y hy
        rcases hy with ⟨i, rfl⟩
        exact i.2.2
    have hMain : x = sSup choices := by
      calc
        x = sInf (Set.range (fun i : I => sSup (family i))) := hLeft.symm
        _ = sSup choices := by
          simpa [choices] using hLaw I family hFamilyDirected
    have hChoicesWayBelow : ∀ y ∈ choices, Chapter2.WayBelow y x := by
      intro y hy
      rcases hy with ⟨f, rfl⟩
      intro A s hAdirected hAsup hxs
      have hsSup : Chapter2.IsSup A (sSup A) :=
        completeLattice_sSup_isSup L A
      have hSupEq : sSup A = s := Chapter2.IsSup.unique hsSup hAsup
      let i : I := ⟨A, hAdirected, by simpa [hSupEq] using hxs⟩
      refine ⟨(f i).1, (f i).2, ?_⟩
      exact sInf_le ⟨i, rfl⟩
    refine ⟨choices, ?_, ?_, ?_⟩
    · intro y hy
      exact ⟨Set.mem_univ y, hChoicesWayBelow y hy⟩
    · constructor
      · have hMember : ∀ i : I, ∃ a : L, a ∈ family i :=
          fun i => i.2.1.1
        let f : ∀ i : I, {a : L // a ∈ family i} := fun i =>
          ⟨Classical.choose (hMember i), Classical.choose_spec (hMember i)⟩
        exact ⟨sInf (Set.range (fun i : I => (f i).1)), ⟨f, rfl⟩⟩
      · intro y hy z hz
        rcases hy with ⟨f, rfl⟩
        rcases hz with ⟨g, rfl⟩
        have hUpper : ∀ i : I,
            ∃ a ∈ family i, (f i).1 ≤ a ∧ (g i).1 ≤ a := by
          intro i
          exact i.2.1.2 (f i).2 (g i).2
        let k : ∀ i : I, {a : L // a ∈ family i} := fun i =>
          ⟨Classical.choose (hUpper i), (Classical.choose_spec (hUpper i)).1⟩
        refine ⟨sInf (Set.range (fun i : I => (k i).1)), ⟨k, rfl⟩, ?_, ?_⟩
        · apply le_sInf
          intro a ha
          rcases ha with ⟨i, rfl⟩
          have hMeetLe :
              sInf (Set.range (fun j : I => (f j).1)) ≤ (f i).1 :=
            sInf_le ⟨i, rfl⟩
          exact hMeetLe.trans (Classical.choose_spec (hUpper i)).2.1
        · apply le_sInf
          intro a ha
          rcases ha with ⟨i, rfl⟩
          have hMeetLe :
              sInf (Set.range (fun j : I => (g j).1)) ≤ (g i).1 :=
            sInf_le ⟨i, rfl⟩
          exact hMeetLe.trans (Classical.choose_spec (hUpper i)).2.2
    · constructor
      · intro y hy
        exact Chapter2.prop_2_2_2_1 (hChoicesWayBelow y hy)
      · intro z hz
        rw [hMain]
        exact sSup_le hz

/-- Theorem 7.1.3.  PDF text: prime-continuity is equivalent to complete
distributivity.

This Stone/Raney lattice theorem is registered as local proof debt. -/
theorem theorem_7_1_3_prime_continuous_iff_completely_distributive
    (L : Type u) [CompleteLattice L] :
    IsPrimeContinuousLattice L ↔ CompleteChoiceMeetJoinLaw.{u, v} L := by
  admit

/-- Proposition 7.1.6.  PDF text: meet-prime elements are meet-irreducible, and
the converse holds under the distributivity hypothesis.

This proposition is proved from the finite meet-prime and frame-distributivity
lemmas above. -/
theorem prop_7_1_6_meet_prime_irreducible
    (L : Type u) [CompleteLattice L] :
    (∀ x : L, IsFiniteMeetPrime x → IsFiniteMeetIrreducible x) ∧
      (IsFrameDistributive L →
        ∀ x : L, IsFiniteMeetIrreducible x → IsFiniteMeetPrime x) := by
  constructor
  · intro x hx
    exact finiteMeetPrime_isFiniteMeetIrreducible hx
  · intro hFrame x hx
    exact finiteMeetPrime_of_finiteMeetIrreducible_of_frame hFrame hx

/-- A finite subset of an order filter has a common lower bound in that filter. -/
private theorem filter_finite_lower_bound
    {L : Type u} [Preorder L] {F M : Set L}
    (hF : Chapter2.IsFilter F) (hM : M.Finite) (hMF : M ⊆ F) :
    ∃ z ∈ F, ∀ m ∈ M, z ≤ m := by
  induction M, hM using Set.Finite.induction_on with
  | empty =>
      rcases hF.2.1 with ⟨z, hzF⟩
      exact ⟨z, hzF, by intro m hm; cases hm⟩
  | @insert a M haM hM ih =>
      have hMF' : M ⊆ F := by
        intro m hm
        exact hMF (Set.mem_insert_of_mem a hm)
      rcases ih hMF' with ⟨z, hzF, hzLower⟩
      have haF : a ∈ F := hMF (Set.mem_insert a M)
      rcases hF.2.2 haF hzF with ⟨w, hwF, hwa, hwz⟩
      refine ⟨w, hwF, ?_⟩
      intro m hm
      rcases Set.mem_insert_iff.mp hm with rfl | hm
      · exact hwa
      · exact hwz.trans (hzLower m hm)

/-- Lemma 2.3.8 separates a failed order relation by a Scott-open order filter. -/
private theorem exists_scottOpen_filter_separating
    {L : Type u} [CompleteLattice L]
    (hContinuous : Chapter2.IsContinuousDomain L)
    {x y : L} (hxy : ¬ x ≤ y) :
    ∃ F : Set L,
      Chapter2.ScottOpen F ∧ Chapter2.IsFilter F ∧ x ∈ F ∧ y ∉ F := by
  let O : Set L := (Chapter2.lowerClosure ({y} : Set L))ᶜ
  have hO : Chapter2.ScottOpen O := by
    simpa [O, Chapter2.ScottOpen] using Chapter2.scottClosed_principal_ideal y
  have hxO : x ∈ O := by
    intro hxLower
    rcases hxLower with ⟨z, hz, hxz⟩
    have hzy : z = y := by simpa using hz
    exact hxy (by simpa [hzy] using hxz)
  have hyO : y ∉ O := by
    intro hy
    exact hy ⟨y, by simp, le_rfl⟩
  rcases Chapter2.lemma_2_3_8_scott_open_union_filters hContinuous hO with
    ⟨family, hFamily, hUnion⟩
  have hxUnion : x ∈ ⋃₀ family := by
    rw [← hUnion]
    exact hxO
  rcases hxUnion with ⟨F, hFfamily, hxF⟩
  have hF := hFamily F hFfamily
  refine ⟨F, hF.1, hF.2, hxF, ?_⟩
  intro hyF
  apply hyO
  rw [hUnion]
  exact ⟨F, hFfamily, hyF⟩

/-- Zorn's lemma supplies a maximal element of `up y` outside a Scott-open
filter.  Scott-openness keeps directed chain suprema outside the filter. -/
private theorem exists_maximal_outside_filter
    {L : Type u} [CompleteLattice L] {F : Set L}
    (hFopen : Chapter2.ScottOpen F) (hFfilter : Chapter2.IsFilter F)
    {x y : L} (hxF : x ∈ F) (hyF : y ∉ F) :
    ∃ m : L,
      y ≤ m ∧ m ∉ F ∧ ¬ x ≤ m ∧
        ∀ z : L, y ≤ z → z ∉ F → m ≤ z → z ≤ m := by
  let P := {z : L // y ≤ z ∧ z ∉ F}
  letI : Nonempty P := ⟨⟨y, le_rfl, hyF⟩⟩
  have hChainBound :
      ∀ c : Set P, IsChain (· ≤ ·) c → c.Nonempty → BddAbove c := by
    intro c hc hcNonempty
    let values : Set L := Subtype.val '' c
    have hValuesDirected : Chapter2.DirectedSet values := by
      constructor
      · rcases hcNonempty with ⟨a, ha⟩
        exact ⟨a.1, ⟨a, ha, rfl⟩⟩
      · intro a ha b hb
        rcases ha with ⟨a', ha', rfl⟩
        rcases hb with ⟨b', hb', rfl⟩
        rcases hc.total ha' hb' with hab | hba
        · exact ⟨b'.1, ⟨b', hb', rfl⟩, hab, le_rfl⟩
        · exact ⟨a'.1, ⟨a', ha', rfl⟩, le_rfl, hba⟩
    have hySup : y ≤ sSup values := by
      rcases hcNonempty with ⟨a, ha⟩
      exact a.2.1.trans (le_sSup ⟨a, ha, rfl⟩)
    have hSupNotF : sSup values ∉ F := by
      intro hSupF
      have hSupComp : sSup values ∈ Fᶜ :=
        hFopen.2 hValuesDirected
          (by
            intro z hz
            rcases hz with ⟨a, ha, rfl⟩
            exact a.2.2)
          (completeLattice_sSup_isSup L values)
      exact hSupComp hSupF
    let upper : P := ⟨sSup values, hySup, hSupNotF⟩
    refine ⟨upper, ?_⟩
    intro a ha
    exact le_sSup ⟨a, ha, rfl⟩
  rcases zorn_le_nonempty hChainBound with ⟨m, hm⟩
  refine ⟨m.1, m.2.1, m.2.2, ?_, ?_⟩
  · intro hxm
    exact m.2.2 (hFfilter.1 hxF hxm)
  · intro z hyz hzF hmz
    let zP : P := ⟨z, hyz, hzF⟩
    exact hm (show m ≤ zP from hmz)

/-- A failed order relation in a continuous complete lattice is separated by a
finite meet-irreducible upper bound. -/
private theorem exists_finiteMeetIrreducible_separator
    {L : Type u} [CompleteLattice L]
    (hContinuous : Chapter2.IsContinuousDomain L)
    {x y : L} (hxy : ¬ x ≤ y) :
    ∃ p : L, y ≤ p ∧ ¬ x ≤ p ∧ IsFiniteMeetIrreducible p := by
  rcases exists_scottOpen_filter_separating hContinuous hxy with
    ⟨F, hFopen, hFfilter, hxF, hyF⟩
  rcases exists_maximal_outside_filter hFopen hFfilter hxF hyF with
    ⟨m, hym, hmF, hxm, hmMax⟩
  refine ⟨m, hym, hxm, ?_⟩
  constructor
  · intro hmTop
    rcases hFfilter.2.1 with ⟨z, hzF⟩
    have hTopF : (⊤ : L) ∈ F := hFfilter.1 hzF le_top
    exact hmF (by simpa [hmTop] using hTopF)
  · intro M hM hmInf
    by_contra hNoMember
    have hAllF : M ⊆ F := by
      intro a haM
      by_contra haF
      have hma : m ≤ a := by
        rw [hmInf]
        exact sInf_le haM
      have ham : a ≤ m := hmMax a (hym.trans hma) haF hma
      have hamEq : a = m := le_antisymm ham hma
      exact hNoMember ⟨a, haM, hamEq.symm⟩
    rcases filter_finite_lower_bound hFfilter hM hAllF with
      ⟨z, hzF, hzLower⟩
    have hzm : z ≤ m := by
      rw [hmInf]
      exact le_sInf hzLower
    exact hmF (hFfilter.1 hzF hzm)

/-- In an algebraic complete lattice the separating filter can be chosen
principal at a compact element, so the maximal separator is completely
meet-irreducible. -/
private theorem exists_completelyMeetIrreducible_separator
    {L : Type u} [CompleteLattice L]
    (hAlgebraic : Chapter2.IsAlgebraicDomain L)
    {x y : L} (hxy : ¬ x ≤ y) :
    ∃ p : L, y ≤ p ∧ ¬ x ≤ p ∧ IsCompletelyMeetIrreducible p := by
  rcases hAlgebraic x with ⟨A, hAsub, _hAdirected, hAsup⟩
  have hCompactNotBelow : ∃ k ∈ A, ¬ k ≤ y := by
    by_contra hNone
    have hAll : ∀ k ∈ A, k ≤ y := by
      intro k hk
      by_contra hky
      exact hNone ⟨k, hk, hky⟩
    exact hxy (hAsup.2 y hAll)
  rcases hCompactNotBelow with ⟨k, hkA, hky⟩
  have hkData := hAsub hkA
  have hkCompact : Chapter2.Compact k := hkData.1
  have hkx : k ≤ x := Chapter2.prop_2_2_2_1 hkData.2
  let F : Set L := {z : L | k ≤ z}
  have hFfilter : Chapter2.IsFilter F := by
    constructor
    · intro a b ha hab
      exact ha.trans hab
    · constructor
      · exact ⟨k, le_rfl⟩
      · intro a ha b hb
        exact ⟨k, le_rfl, ha, hb⟩
  have hFopen : Chapter2.ScottOpen F := by
    have hEq : F = Chapter2.wayBelowUpper k := by
      ext z
      constructor
      · intro hkz
        exact Chapter2.prop_2_2_2_2 le_rfl hkCompact hkz
      · intro hkz
        exact Chapter2.prop_2_2_2_1 hkz
    rw [hEq]
    exact Chapter2.scottOpen_wayBelowUpper ⟨Chapter2.CompactSet, hAlgebraic⟩ k
  have hxF : x ∈ F := hkx
  have hyF : y ∉ F := hky
  rcases exists_maximal_outside_filter hFopen hFfilter hxF hyF with
    ⟨m, hym, hmF, hxm, hmMax⟩
  refine ⟨m, hym, hxm, ?_⟩
  constructor
  · intro hmTop
    exact hmF (by simpa [F, hmTop])
  · intro M hmInf
    by_contra hNoMember
    have hAllF : M ⊆ F := by
      intro a haM
      by_contra haF
      have hma : m ≤ a := by
        rw [hmInf]
        exact sInf_le haM
      have ham : a ≤ m := hmMax a (hym.trans hma) haF hma
      have hamEq : a = m := le_antisymm ham hma
      exact hNoMember ⟨a, haM, hamEq.symm⟩
    have hkm : k ≤ m := by
      rw [hmInf]
      exact le_sInf (by
        intro a haM
        exact hAllF haM)
    exact hmF hkm

/-- Theorem 7.1.7: continuous lattices are meet-generated by meet-irreducible
elements. -/
theorem theorem_7_1_7_continuous_lattice_meet_generated
    (L : Type u) [CompleteLattice L] :
    IsContinuousCompleteLattice L →
      MeetGeneratedBy ({x : L | IsFiniteMeetIrreducible x}) := by
  intro hContinuous x
  apply le_antisymm
  · apply le_sInf
    intro p hp
    exact hp.2
  · by_contra hNotLe
    rcases exists_finiteMeetIrreducible_separator hContinuous.2 hNotLe with
      ⟨p, hxp, hNotInfP, hpIrred⟩
    apply hNotInfP
    exact sInf_le ⟨hpIrred, hxp⟩

/-- The algebraic half of Theorem 7.1.7: algebraic complete lattices are
meet-generated by completely meet-irreducible elements. -/
theorem theorem_7_1_7_algebraic_lattice_completely_meet_generated
    (L : Type u) [CompleteLattice L] :
    IsAlgebraicCompleteLattice L →
      MeetGeneratedBy ({x : L | IsCompletelyMeetIrreducible x}) := by
  intro hAlgebraic x
  apply le_antisymm
  · apply le_sInf
    intro p hp
    exact hp.2
  · by_contra hNotLe
    have hAlgebraicRaw : Chapter2.IsAlgebraicDomain L :=
      Chapter2.basis_to_raw hAlgebraic.2
    rcases exists_completelyMeetIrreducible_separator hAlgebraicRaw hNotLe with
      ⟨p, hxp, hNotInfP, hpIrred⟩
    apply hNotInfP
    exact sInf_le ⟨hpIrred, hxp⟩

/-- Theorem 7.1.8.  PDF text: meet-prime generation implies the finite-prime
distributive equations.

This theorem is registered as local proof debt. -/
theorem theorem_7_1_8_meet_prime_generation_distributive_equations
    (L : Type u) [CompleteLattice L] :
    MeetGeneratedBy ({x : L | IsFiniteMeetPrime x}) →
      FinitePrimeChoiceDistributivity.{u, v} L := by
  intro hGen
  exact ⟨frameDistributive_of_meetGeneratedBy_finiteMeetPrime hGen,
    finiteMeetJoinChoiceLaw_of_meetGeneratedBy_finiteMeetPrime hGen,
    joinFiniteMeetChoiceLaw_of_meetGeneratedBy_finiteMeetPrime hGen⟩

/-- Theorem 7.1.8, dual form.  PDF text: join-prime generation implies the dual
finite-prime distributive equations.

This theorem is registered as local proof debt. -/
theorem theorem_7_1_8_join_prime_generation_dual_distributive_equations
    (L : Type u) [CompleteLattice L] :
    JoinGeneratedBy ({x : L | IsFiniteJoinPrime x}) →
      DualFinitePrimeChoiceDistributivity.{u, v} L := by
  intro hGen
  exact ⟨coframeDistributive_of_joinGeneratedBy_finiteJoinPrime hGen,
    finiteJoinMeetChoiceLaw_of_joinGeneratedBy_finiteJoinPrime hGen,
    meetFiniteJoinChoiceLaw_of_joinGeneratedBy_finiteJoinPrime hGen⟩

/-- Proposition 7.1.11.  PDF text: the listed characterizations of complete
prime filters are equivalent.

This proposition is proved by the three characterization lemmas above. -/
theorem prop_7_1_11_complete_prime_filter_characterizations
    (L : Type u) [CompleteLattice L] (F : Set L) :
    CompletePrimeFilterCharacterizations L F := by
  constructor
  · exact completelyPrimeFilter_iff_principalIdealComplement
  · exact completelyPrimeFilter_iff_finiteMeetPrime_complement
  · exact completelyPrimeFilter_iff_characteristicFrameHom

/-- Proposition 7.1.13: the basic opens `O_x` form a topology on `pt(L)`.
The equalities below are the finite-intersection and arbitrary-union clauses
from the PDF proof. -/
theorem prop_7_1_13_point_topology (L : Type u) [CompleteLattice L] :
    PointBasicOpenTopologyLaws L := by
  constructor
  · ext F
    constructor
    · intro _h
      trivial
    · intro _h
      exact F.2.1.1
  · intro x y
    ext F
    constructor
    · intro hxy
      exact ⟨F.2.1.2.1 hxy inf_le_left, F.2.1.2.1 hxy inf_le_right⟩
    · intro h
      exact F.2.1.2.2 h.1 h.2
  · intro S
    ext F
    constructor
    · intro hSup
      rcases F.2.2 S hSup with ⟨s, hsS, hsF⟩
      exact ⟨pointBasicOpen s, ⟨s, hsS, rfl⟩, hsF⟩
    · intro hUnion
      rcases hUnion with ⟨U, hU, hFU⟩
      rcases hU with ⟨s, hsS, rfl⟩
      exact F.2.1.2.1 hFU (le_sSup hsS)
  · intro x
    exact PointOpen.basic x

/-- Theorem 7.1.14.  PDF text: the open-set and point functors form a dual
adjunction with units `eta` and `epsilon`.

The two final fields are the triangle identities displayed in the textbook. -/
theorem theorem_7_1_14_stone_dual_adjunction :
    Nonempty (StoneDualAdjunctionData.{u}) := by
  refine ⟨{
    adjunction := concreteStoneAdjunction
    opensMap := fun f => openSetPreimageFrameHom f
    spectrumMap := fun h => spectrumMapOfFrameHom h
    unit_continuous := stoneUnitContinuous
    unit_agrees := ?_
    epsilon_frame_hom := stoneEpsilonFrameHom
    epsilon_agrees := ?_
    unit_naturality := ?_
    epsilon_naturality := ?_
    left_triangle := ?_
    right_triangle := ?_ }⟩
  · intro X x
    rfl
  · intro L a
    rfl
  · intro X Y f x
    apply Subtype.ext
    rfl
  · intro K L h a
    apply Subtype.ext
    rfl
  · intro X U
    apply Subtype.ext
    rfl
  · intro L F
    apply Subtype.ext
    rfl

end Chapter7
end AbramskyJung

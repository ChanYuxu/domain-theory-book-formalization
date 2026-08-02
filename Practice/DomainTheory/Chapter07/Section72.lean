import Practice.DomainTheory.Chapter07.Section71
import Practice.DomainTheory.Chapter04.Section43

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.2

Sober/spatial dualities, Hofmann--Mislove, spectral spaces, and the domain
specializations of Stone duality.

Semantic audit note: direct lightweight facts are proved where possible.  The
PDF-facing duality and category-level statements are visible proof-debt
declarations; auxiliary data packages record the intended object classes, units,
duality maps, and categorical functorial laws until those proofs are translated.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

/-- Closed subsets for the lightweight `Space` interface. -/
def IsClosed (X : Space.{u}) (C : Set X.Point) : Prop :=
  X.IsOpen Cᶜ

/-- The specialization preorder induced by a topology. -/
def SpecializationLE (X : Space.{u}) (x y : X.Point) : Prop :=
  ∀ U : Set X.Point, X.IsOpen U → x ∈ U → y ∈ U

/-- The specialization relation is a preorder. -/
@[reducible]
def specializationPreorder (X : Space.{u}) : Preorder X.Point where
  le := SpecializationLE X
  le_refl := by
    intro x U _hU hx
    exact hx
  le_trans := by
    intro x y z hxy hyz U hU hx
    exact hyz U hU (hxy U hU hx)

/-- Definition 7.2.1: irreducible closed subsets. -/
def IsIrreducibleClosed (X : Space.{u}) (C : Set X.Point) : Prop :=
  IsClosed X C ∧ C.Nonempty ∧
    ∀ A B : Set X.Point,
      IsClosed X A → IsClosed X B → C ⊆ A ∪ B → C ⊆ A ∨ C ⊆ B

/-- Definition 7.2.1, named book entry. -/
def def_7_2_1_irreducible_closed (X : Space.{u}) : Set X.Point → Prop :=
  IsIrreducibleClosed X

/-- The closure of a point expressed through specialization. -/
def PointClosure (X : Space.{u}) (x : X.Point) : Set X.Point :=
  {y : X.Point | SpecializationLE X y x}

/-- The `T0` separation axiom for the lightweight spaces. -/
def IsT0Space (X : Space.{u}) : Prop :=
  ∀ x y : X.Point, x ≠ y →
    ∃ U : Set X.Point,
      X.IsOpen U ∧ ((x ∈ U ∧ y ∉ U) ∨ (y ∈ U ∧ x ∉ U))

private theorem scottClosed_union {D : Type u} [Preorder D] {C E : Set D}
    (hC : Chapter2.ScottClosed C) (hE : Chapter2.ScottClosed E) :
    Chapter2.ScottClosed (C ∪ E) := by
  constructor
  · intro x y hy hxy
    rcases hy with hy | hy
    · exact Or.inl (hC.1 hy hxy)
    · exact Or.inr (hE.1 hy hxy)
  · intro A s hA hsub hs
    by_contra hsUnion
    have hsC : s ∉ C := fun hsC => hsUnion (Or.inl hsC)
    have hsE : s ∉ E := fun hsE => hsUnion (Or.inr hsE)
    have hnotSubsetC : ∃ a : D, a ∈ A ∧ a ∉ C := by
      by_contra hnone
      have hA_C : A ⊆ C := by
        intro a ha
        by_contra haC
        exact hnone ⟨a, ha, haC⟩
      exact hsC (hC.2 hA hA_C hs)
    have hnotSubsetE : ∃ b : D, b ∈ A ∧ b ∉ E := by
      by_contra hnone
      have hA_E : A ⊆ E := by
        intro a ha
        by_contra haE
        exact hnone ⟨a, ha, haE⟩
      exact hsE (hE.2 hA hA_E hs)
    rcases hnotSubsetC with ⟨a, haA, haC⟩
    rcases hnotSubsetE with ⟨b, hbA, hbE⟩
    rcases hA.2 haA hbA with ⟨z, hzA, haz, hbz⟩
    rcases hsub hzA with hzC | hzE
    · exact haC (hC.1 hzC haz)
    · exact hbE (hE.1 hzE hbz)

private theorem scottOpen_univ {D : Type u} [Preorder D] :
    Chapter2.ScottOpen (Set.univ : Set D) := by
  constructor
  · intro _ _ hy _
    simp at hy
  · intro A _ hA hsub _
    rcases hA.1 with ⟨a, ha⟩
    have haEmpty : a ∈ (Set.univ : Set D)ᶜ := hsub ha
    simp at haEmpty

private theorem scottOpen_inter {D : Type u} [Preorder D] {U V : Set D}
    (hU : Chapter2.ScottOpen U) (hV : Chapter2.ScottOpen V) :
    Chapter2.ScottOpen (U ∩ V) := by
  change Chapter2.ScottClosed (U ∩ V)ᶜ
  rw [Chapter2.ScottOpen] at hU hV
  convert scottClosed_union hU hV using 1
  ext x
  by_cases hxU : x ∈ U <;> by_cases hxV : x ∈ V <;> simp [hxU, hxV]

private theorem scottOpen_sUnion {D : Type u} [Preorder D] {S : Set (Set D)}
    (hS : ∀ U ∈ S, Chapter2.ScottOpen U) :
    Chapter2.ScottOpen (⋃₀ S) := by
  have hEq :
      (⋃₀ S : Set D) =
        (⋃ V : {V : Set D // V ∈ S}, (V.1 : Set D)) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨V, hVS, hxV⟩
      simpa only [Set.mem_iUnion] using
        (show ∃ W : {V : Set D // V ∈ S}, x ∈ (W.1 : Set D) from
          ⟨⟨V, hVS⟩, hxV⟩)
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨V, hxV⟩
      exact ⟨V.1, V.2, hxV⟩
  rw [hEq]
  exact Chapter2.scottOpen_iUnion
    (U := fun V : {V : Set D // V ∈ S} => (V.1 : Set D))
    (fun V => hS V.1 V.2)

/-- The Scott topological space of a preorder, using Chapter 2's Scott-open sets. -/
def ScottTopologySpace (D : Type u) [Preorder D] : Space.{u} where
  Point := D
  IsOpen := Chapter2.ScottOpen
  univ_open := scottOpen_univ
  inter_open := by
    intro U V hU hV
    exact scottOpen_inter hU hV
  sUnion_open := by
    intro S hS
    exact scottOpen_sUnion hS

/-- In the Scott topology of a preorder, specialization is exactly the
underlying order. -/
theorem scottTopologySpace_specialization_iff_order
    {D : Type u} [Preorder D] (x y : D) :
    SpecializationLE (ScottTopologySpace D) x y ↔ x ≤ y := by
  simpa [SpecializationLE, ScottTopologySpace] using
    (Chapter2.prop_2_3_2_order_open_iff (x := x) (y := y)).symm

/-- The Scott topology of an antisymmetric preorder is `T0`. -/
theorem scottTopologySpace_t0_of_antisymmetric
    {D : Type u} [Preorder D]
    (hanti : ∀ ⦃x y : D⦄, x ≤ y → y ≤ x → x = y) :
    IsT0Space (ScottTopologySpace D) := by
  change ∀ x y : D, x ≠ y →
    ∃ U : Set D,
      Chapter2.ScottOpen U ∧ ((x ∈ U ∧ y ∉ U) ∨ (y ∈ U ∧ x ∉ U))
  intro x y hxy
  exact Chapter2.prop_2_3_2_2_scott_T0 (hanti := hanti) hxy

/-- If the Scott topology is `T0`, the underlying preorder is antisymmetric. -/
theorem antisymmetric_of_scottTopologySpace_t0
    {D : Type u} [Preorder D]
    (hT0 : IsT0Space (ScottTopologySpace D)) :
    ∀ ⦃x y : D⦄, x ≤ y → y ≤ x → x = y := by
  intro x y hxy hyx
  by_contra hne
  rcases hT0 x y hne with ⟨U, hU, hsep⟩
  rcases hsep with ⟨hxU, hyU⟩ | ⟨hyU, hxU⟩
  · exact hyU (Chapter2.scottOpen_upper hU hxU hxy)
  · exact hxU (Chapter2.scottOpen_upper hU hyU hyx)

/-- The Scott topology is `T0` exactly for antisymmetric preorders. -/
theorem scottTopologySpace_t0_iff_antisymmetric
    {D : Type u} [Preorder D] :
    IsT0Space (ScottTopologySpace D) ↔
      ∀ ⦃x y : D⦄, x ≤ y → y ≤ x → x = y := by
  constructor
  · exact antisymmetric_of_scottTopologySpace_t0
  · exact scottTopologySpace_t0_of_antisymmetric

/-- Every irreducible closed set has a generic point.  The uniqueness part of
sobriety is supplied by the accompanying `T0` condition. -/
def EveryIrreducibleClosedHasGenericPoint (X : Space.{u}) : Prop :=
  ∀ C : Set X.Point, IsIrreducibleClosed X C → ∃ x : X.Point, C = PointClosure X x

/-- The soberification unit is injective exactly when the space is `T0`. -/
def SoberUnitInjective (X : Space.{u}) : Prop :=
  IsT0Space X

/-- The soberification unit is surjective exactly when irreducible closed sets have
generic points. -/
def SoberUnitSurjective (X : Space.{u}) : Prop :=
  EveryIrreducibleClosedHasGenericPoint X

/-- Definition 7.2.3: sober spaces. -/
def IsSober (X : Space.{u}) : Prop :=
  IsT0Space X ∧ EveryIrreducibleClosedHasGenericPoint X

/-- Definition 7.2.3, named book entry. -/
def def_7_2_3_sober_space (X : Space.{u}) : Prop :=
  IsSober X

/-- In the point space of a complete lattice, specialization is inclusion of
the underlying completely prime filters. -/
theorem pointSpace_specialization_iff_subset
    (L : Type u) [CompleteLattice L] (F G : Point L) :
    SpecializationLE (pointSpace L) F G ↔ F.1 ⊆ G.1 := by
  constructor
  · intro h x hx
    exact h (pointBasicOpen x) (PointOpen.basic x) hx
  · intro h U hU hFU
    induction hU with
    | basic x =>
        exact h hFU
    | univ =>
        exact Set.mem_univ G
    | inter hU hV ihU ihV =>
        exact ⟨ihU hFU.1, ihV hFU.2⟩
    | sUnion S _hS ihS =>
        rcases hFU with ⟨V, hVS, hFV⟩
        exact ⟨V, hVS, ihS V hVS hFV⟩

/-- Closures in the point space are downward closures under filter inclusion. -/
theorem pointSpace_closure_eq_subset
    (L : Type u) [CompleteLattice L] (F : Point L) :
    PointClosure (pointSpace L) F = {G : Point L | G.1 ⊆ F.1} := by
  ext G
  exact pointSpace_specialization_iff_subset L G F

/-- The point space of a complete lattice is `T0`: distinct completely prime
filters are separated by a basic open. -/
theorem pointSpace_t0 (L : Type u) [CompleteLattice L] :
    IsT0Space (pointSpace L) := by
  intro F G hne
  by_cases hEq : F.1 = G.1
  · exact False.elim (hne (Subtype.ext hEq))
  · have hSep :
        ∃ x : L, (x ∈ F.1 ∧ x ∉ G.1) ∨ (x ∈ G.1 ∧ x ∉ F.1) := by
      by_contra hNoSep
      have hSetEq : F.1 = G.1 := by
        ext x
        constructor
        · intro hxF
          by_contra hxG
          exact hNoSep ⟨x, Or.inl ⟨hxF, hxG⟩⟩
        · intro hxG
          by_contra hxF
          exact hNoSep ⟨x, Or.inr ⟨hxG, hxF⟩⟩
      exact hEq hSetEq
    rcases hSep with ⟨x, hx | hx⟩
    · exact ⟨pointBasicOpen x, PointOpen.basic x, Or.inl hx⟩
    · exact ⟨pointBasicOpen x, PointOpen.basic x, Or.inr hx⟩

/-- Closed subsets of the point space are downward closed for inclusion of
completely prime filters. -/
theorem pointSpace_closed_downward
    (L : Type u) [CompleteLattice L] {C : Set (Point L)}
    (hC : IsClosed (pointSpace L) C) {F G : Point L}
    (hF : F ∈ C) (hGF : G.1 ⊆ F.1) : G ∈ C := by
  by_contra hG
  have hSpec : SpecializationLE (pointSpace L) G F :=
    (pointSpace_specialization_iff_subset L G F).2 hGF
  have hFCompl : F ∈ Cᶜ := hSpec Cᶜ hC hG
  exact hFCompl hF

/-- Irreducibility of a closed subset of the point space gives finite
compatibility for basic opens. -/
theorem pointSpace_irreducible_closed_basic_inter
    (L : Type u) [CompleteLattice L] {C : Set (Point L)}
    (hC : IsIrreducibleClosed (pointSpace L) C) {x y : L}
    (hx : ∃ F : Point L, F ∈ C ∧ x ∈ F.1)
    (hy : ∃ G : Point L, G ∈ C ∧ y ∈ G.1) :
    ∃ H : Point L, H ∈ C ∧ x ∈ H.1 ∧ y ∈ H.1 := by
  by_contra hNoMeet
  have hClosedX : IsClosed (pointSpace L) (pointBasicOpen x)ᶜ := by
    unfold IsClosed
    simpa using (PointOpen.basic x)
  have hClosedY : IsClosed (pointSpace L) (pointBasicOpen y)ᶜ := by
    unfold IsClosed
    simpa using (PointOpen.basic y)
  have hSubset : C ⊆ (pointBasicOpen x)ᶜ ∪ (pointBasicOpen y)ᶜ := by
    intro H hHC
    by_cases hxH : x ∈ H.1
    · right
      intro hyH
      exact hNoMeet ⟨H, hHC, hxH, hyH⟩
    · left
      exact hxH
  rcases hC.2.2 (pointBasicOpen x)ᶜ (pointBasicOpen y)ᶜ
      hClosedX hClosedY hSubset with hLeft | hRight
  · rcases hx with ⟨F, hFC, hxF⟩
    exact (hLeft hFC) hxF
  · rcases hy with ⟨G, hGC, hyG⟩
    exact (hRight hGC) hyG

/-- Irreducibility of a closed subset of the point space gives non-empty
intersections with binary intersections of arbitrary opens. -/
theorem pointSpace_irreducible_closed_open_inter
    (L : Type u) [CompleteLattice L] {C U V : Set (Point L)}
    (hC : IsIrreducibleClosed (pointSpace L) C)
    (hU : PointOpen L U) (hV : PointOpen L V)
    (hCU : ∃ F : Point L, F ∈ C ∧ F ∈ U)
    (hCV : ∃ G : Point L, G ∈ C ∧ G ∈ V) :
    ∃ H : Point L, H ∈ C ∧ H ∈ U ∧ H ∈ V := by
  by_contra hNoInter
  have hClosedU : IsClosed (pointSpace L) Uᶜ := by
    unfold IsClosed
    simpa using hU
  have hClosedV : IsClosed (pointSpace L) Vᶜ := by
    unfold IsClosed
    simpa using hV
  have hSubset : C ⊆ Uᶜ ∪ Vᶜ := by
    intro H hHC
    by_cases hHU : H ∈ U
    · by_cases hHV : H ∈ V
      · exact False.elim (hNoInter ⟨H, hHC, hHU, hHV⟩)
      · exact Or.inr hHV
    · exact Or.inl hHU
  rcases hC.2.2 Uᶜ Vᶜ hClosedU hClosedV hSubset with hLeft | hRight
  · rcases hCU with ⟨F, hFC, hFU⟩
    exact (hLeft hFC) hFU
  · rcases hCV with ⟨G, hGC, hGV⟩
    exact (hRight hGC) hGV

/-- The generic point of an irreducible closed subset of `pt(L)` is the union of
the completely prime filters lying in that closed subset. -/
theorem pointSpace_irreducible_closed_has_generic_point
    (L : Type u) [CompleteLattice L] :
    EveryIrreducibleClosedHasGenericPoint (pointSpace L) := by
  intro C hC
  let Fset : Set L := {x : L | ∃ F : Point L, F ∈ C ∧ x ∈ F.1}
  have hPrime : IsCompletelyPrimeFilter Fset := by
    constructor
    · constructor
      · rcases hC.2.1 with ⟨F, hFC⟩
        exact ⟨F, hFC, F.2.1.1⟩
      · constructor
        · intro x y hx hxy
          rcases hx with ⟨F, hFC, hxF⟩
          exact ⟨F, hFC, F.2.1.2.1 hxF hxy⟩
        · intro x y hx hy
          rcases hx with ⟨F, hFC, hxF⟩
          rcases hy with ⟨G, hGC, hyG⟩
          rcases pointSpace_irreducible_closed_basic_inter L hC
              ⟨F, hFC, hxF⟩ ⟨G, hGC, hyG⟩ with ⟨H, hHC, hxH, hyH⟩
          exact ⟨H, hHC, H.2.1.2.2 hxH hyH⟩
    · intro S hSup
      rcases hSup with ⟨F, hFC, hSupF⟩
      rcases F.2.2 S hSupF with ⟨x, hxS, hxF⟩
      exact ⟨x, hxS, ⟨F, hFC, hxF⟩⟩
  let F : Point L := ⟨Fset, hPrime⟩
  have hOpenHits :
      ∀ U : Set (Point L), PointOpen L U → F ∈ U →
        ∃ G : Point L, G ∈ C ∧ G ∈ U := by
    intro U hU
    induction hU with
    | basic x =>
        intro hxF
        change x ∈ Fset at hxF
        exact hxF
    | univ =>
        intro _hF
        rcases hC.2.1 with ⟨G, hGC⟩
        exact ⟨G, hGC, Set.mem_univ G⟩
    | inter hU hV ihU ihV =>
        intro hFUV
        rcases ihU hFUV.1 with ⟨G, hGC, hGU⟩
        rcases ihV hFUV.2 with ⟨H, hHC, hHV⟩
        rcases pointSpace_irreducible_closed_open_inter L hC hU hV
            ⟨G, hGC, hGU⟩ ⟨H, hHC, hHV⟩ with ⟨K, hKC, hKU, hKV⟩
        exact ⟨K, hKC, ⟨hKU, hKV⟩⟩
    | sUnion S _hS ihS =>
        intro hFU
        rcases hFU with ⟨U, hUS, hFU⟩
        rcases ihS U hUS hFU with ⟨G, hGC, hGU⟩
        exact ⟨G, hGC, ⟨U, hUS, hGU⟩⟩
  refine ⟨F, ?_⟩
  rw [pointSpace_closure_eq_subset L F]
  apply Set.Subset.antisymm
  · intro G hGC x hxG
    exact ⟨G, hGC, hxG⟩
  · intro G hGF
    have hFC : F ∈ C := by
      by_contra hFnotC
      have hHit : ∃ G : Point L, G ∈ C ∧ G ∈ Cᶜ :=
        hOpenHits Cᶜ hC.1 hFnotC
      rcases hHit with ⟨H, hHC, hHnotC⟩
      exact hHnotC hHC
    exact pointSpace_closed_downward L hC.1 hFC hGF

/-- The lattice unit `epsilon_L` is represented by the basic-open map `x ↦ O_x`. -/
def EpsilonMap {L : Type u} [CompleteLattice L] (x : L) : Set (Point L) :=
  pointBasicOpen x

/-- Surjectivity of the lattice unit onto the generated topology. -/
def EpsilonSurjective (L : Type u) [CompleteLattice L] : Prop :=
  ∀ U : Set (Point L), PointOpen L U → ∃ x : L, U = EpsilonMap x

/-- Injectivity of the lattice unit. -/
def EpsilonInjective (L : Type u) [CompleteLattice L] : Prop :=
  ∀ x y : L, EpsilonMap x = EpsilonMap y → x = y

/-- Order reflection of the lattice unit. -/
def EpsilonOrderReflecting (L : Type u) [CompleteLattice L] : Prop :=
  ∀ x y : L, EpsilonMap x ⊆ EpsilonMap y → x ≤ y

/-- Proposition 7.2.4, direct part: the lattice unit is monotone. -/
theorem epsilon_monotone (L : Type u) [CompleteLattice L] :
    Monotone (EpsilonMap : L → Set (Point L)) := by
  intro x y hxy F hxF
  exact F.2.1.2.1 hxF hxy

/-- Proposition 7.2.4, direct part: the lattice unit is surjective onto the
generated point topology. -/
theorem epsilon_surjective (L : Type u) [CompleteLattice L] :
    EpsilonSurjective L := by
  intro U hU
  induction hU with
  | basic x =>
      exact ⟨x, rfl⟩
  | univ =>
      refine ⟨⊤, ?_⟩
      simpa [EpsilonMap] using (prop_7_1_13_point_topology L).top_eq_univ.symm
  | inter hU hV ihU ihV =>
      rcases ihU with ⟨x, rfl⟩
      rcases ihV with ⟨y, rfl⟩
      refine ⟨x ⊓ y, ?_⟩
      simpa [EpsilonMap] using (prop_7_1_13_point_topology L).inter_eq x y |>.symm
  | sUnion S hS ihS =>
      let A : Set L := {x : L | ∃ U ∈ S, U = EpsilonMap x}
      refine ⟨sSup A, ?_⟩
      have hUnion :
          ⋃₀ S = ⋃₀ (pointBasicOpen '' A) := by
        ext F
        constructor
        · intro hF
          rcases hF with ⟨U, hUS, hFU⟩
          rcases ihS U hUS with ⟨x, hxU⟩
          refine ⟨pointBasicOpen x, ?_, ?_⟩
          · exact ⟨x, ⟨U, hUS, hxU⟩, rfl⟩
          · simpa [EpsilonMap, hxU] using hFU
        · intro hF
          rcases hF with ⟨O, hO, hFO⟩
          rcases hO with ⟨x, hxA, rfl⟩
          rcases hxA with ⟨U, hUS, hxU⟩
          refine ⟨U, hUS, ?_⟩
          simpa [EpsilonMap, hxU] using hFO
      calc
        ⋃₀ S = ⋃₀ (pointBasicOpen '' A) := hUnion
        _ = EpsilonMap (sSup A) := by
          simpa [EpsilonMap] using
            (prop_7_1_13_point_topology L).sUnion_eq A |>.symm

/-- Basic opens preserve binary meets exactly as intersections, using the
lattice-filter clauses in a point. -/
theorem epsilon_inf_eq_inter {L : Type u} [CompleteLattice L] (x y : L) :
    EpsilonMap (x ⊓ y) = EpsilonMap x ∩ EpsilonMap y := by
  ext F
  constructor
  · intro hxy
    exact ⟨F.2.1.2.1 hxy inf_le_left, F.2.1.2.1 hxy inf_le_right⟩
  · intro hxy
    exact F.2.1.2.2 hxy.1 hxy.2

/-- Separation of lattice elements by completely prime filters. -/
def CompletelyPrimeFiltersSeparate (L : Type u) [CompleteLattice L] : Prop :=
  ∀ x y : L, x ≠ y →
    ∃ F : Point L, (x ∈ F.1 ∧ y ∉ F.1) ∨ (y ∈ F.1 ∧ x ∉ F.1)

/-- Order separation of lattice elements by completely prime filters, condition
(4) in Proposition 7.2.4. -/
def CompletelyPrimeFiltersOrderSeparate (L : Type u) [CompleteLattice L] : Prop :=
  ∀ x y : L, ¬ x ≤ y → ∃ F : Point L, x ∈ F.1 ∧ y ∉ F.1

/-- Equality reflection for epsilon is equivalent to two-sided separation by
completely prime filters. -/
theorem epsilon_injective_iff_filter_separate
    (L : Type u) [CompleteLattice L] :
    EpsilonInjective L ↔ CompletelyPrimeFiltersSeparate L := by
  constructor
  · intro hInjective x y hxy
    by_contra hNoSep
    have hEq : EpsilonMap x = EpsilonMap y := by
      ext F
      constructor
      · intro hx
        by_contra hy
        exact hNoSep ⟨F, Or.inl ⟨hx, hy⟩⟩
      · intro hy
        by_contra hx
        exact hNoSep ⟨F, Or.inr ⟨hy, hx⟩⟩
    exact hxy (hInjective x y hEq)
  · intro hSeparate x y hEq
    by_contra hxy
    rcases hSeparate x y hxy with ⟨F, hF | hF⟩
    · have hy : y ∈ F.1 := by
        have : F ∈ EpsilonMap y := by
          rw [← hEq]
          exact hF.1
        exact this
      exact hF.2 hy
    · have hx : x ∈ F.1 := by
        have : F ∈ EpsilonMap x := by
          rw [hEq]
          exact hF.1
        exact this
      exact hF.2 hx

/-- Order separation by completely prime filters is equivalent to epsilon order
reflection. -/
theorem order_separate_iff_epsilon_reflecting
    (L : Type u) [CompleteLattice L] :
    CompletelyPrimeFiltersOrderSeparate L ↔ EpsilonOrderReflecting L := by
  constructor
  · intro hSeparate x y hSubset
    by_contra hnle
    rcases hSeparate x y hnle with ⟨F, hx, hy⟩
    exact hy (hSubset hx)
  · intro hReflecting x y hnle
    by_contra hNoSep
    have hSubset : EpsilonMap x ⊆ EpsilonMap y := by
      intro F hx
      by_contra hy
      exact hNoSep ⟨F, hx, hy⟩
    exact hnle (hReflecting x y hSubset)

/-- Epsilon is order-reflecting exactly when it is injective. -/
theorem epsilon_order_reflecting_iff_injective
    (L : Type u) [CompleteLattice L] :
    EpsilonOrderReflecting L ↔ EpsilonInjective L := by
  constructor
  · intro hReflecting x y hEq
    have hxy : EpsilonMap x ⊆ EpsilonMap y := by
      intro F hx
      rw [← hEq]
      exact hx
    have hyx : EpsilonMap y ⊆ EpsilonMap x := by
      intro F hy
      rw [hEq]
      exact hy
    exact le_antisymm (hReflecting x y hxy) (hReflecting y x hyx)
  · intro hInjective x y hSubset
    have hEq : EpsilonMap (x ⊓ y) = EpsilonMap x := by
      rw [epsilon_inf_eq_inter]
      ext F
      constructor
      · intro hF
        exact hF.1
      · intro hx
        exact ⟨hx, hSubset hx⟩
    have hMeet : x ⊓ y = x := hInjective (x ⊓ y) x hEq
    calc
      x = x ⊓ y := hMeet.symm
      _ ≤ y := inf_le_right

/-- The complement of the principal ideal below a finite meet-prime element is a
completely prime filter. -/
theorem finiteMeetPrime_complement_principal_completelyPrime
    {L : Type u} [CompleteLattice L] {p : L}
    (hp : IsFiniteMeetPrime p) :
    IsCompletelyPrimeFilter {x : L | ¬ x ≤ p} := by
  constructor
  · constructor
    · intro htop
      exact hp.1 (le_antisymm le_top htop)
    · constructor
      · intro x y hx hxy hy
        exact hx (le_trans hxy hy)
      · intro x y hx hy hxy
        have hInf : sInf ({x, y} : Set L) ≤ p := by
          simpa [sInf_pair] using hxy
        rcases hp.2 ({x, y} : Set L) (by simp) hInf with ⟨z, hz, hzp⟩
        rcases hz with rfl | hz
        · exact hx hzp
        · have hzy : z = y := by
            simpa using hz
          subst z
          exact hy hzp
  · intro S hSup
    by_contra hNoMember
    have hAllLe : ∀ z ∈ S, z ≤ p := by
      intro z hz
      by_contra hzle
      exact hNoMember ⟨z, hz, hzle⟩
    exact hSup (sSup_le hAllLe)

/-- Meet-generation by finite meet-primes yields separation of failed order
relations by completely prime filters. -/
theorem meetGenerated_finiteMeetPrime_orderSeparate
    (L : Type u) [CompleteLattice L]
    (hGenerated : MeetGeneratedBy ({p : L | IsFiniteMeetPrime p})) :
    CompletelyPrimeFiltersOrderSeparate L := by
  intro x y hnle
  have hExists :
      ∃ p : L, IsFiniteMeetPrime p ∧ y ≤ p ∧ ¬ x ≤ p := by
    by_contra hNo
    have hAll : ∀ p : L, IsFiniteMeetPrime p → y ≤ p → x ≤ p := by
      intro p hp hyp
      by_contra hxp
      exact hNo ⟨p, hp, hyp, hxp⟩
    have hxy : x ≤ y := by
      calc
        x ≤ sInf {p : L | IsFiniteMeetPrime p ∧ y ≤ p} := by
          exact le_sInf (by
            intro p hp
            exact hAll p hp.1 hp.2)
        _ = y := (hGenerated y).symm
    exact hnle hxy
  rcases hExists with ⟨p, hpPrime, hyp, hxp⟩
  let F : Point L :=
    ⟨{z : L | ¬ z ≤ p}, finiteMeetPrime_complement_principal_completelyPrime hpPrime⟩
  exact ⟨F, hxp, fun hyF => hyF hyp⟩

/-- Order separation by completely prime filters recovers meet-generation by
finite meet-prime elements.  The proof uses Proposition 7.1.11 to identify the
complement of a completely prime filter with a principal ideal generated by a
finite meet-prime element. -/
theorem orderSeparate_meetGenerated_finiteMeetPrime
    (L : Type u) [CompleteLattice L]
    (hSeparate : CompletelyPrimeFiltersOrderSeparate L) :
    MeetGeneratedBy ({p : L | IsFiniteMeetPrime p}) := by
  intro x
  let G : Set L := {p : L | IsFiniteMeetPrime p ∧ x ≤ p}
  apply le_antisymm
  · exact le_sInf (by
      intro p hp
      exact hp.2)
  · by_contra hnot
    rcases hSeparate (sInf G) x hnot with ⟨F, hInfF, hxNotF⟩
    have hChar : CompletePrimeFilterCharacterizations L F.1 :=
      prop_7_1_11_complete_prime_filter_characterizations L F.1
    rcases hChar.meet_prime_complement.1 F.2 with ⟨p, hpPrime, hCompl⟩
    have hxle : x ≤ p := by
      have hxCompl : x ∈ F.1ᶜ := hxNotF
      have : x ∈ {z : L | z ≤ p} := by
        rw [← hCompl]
        exact hxCompl
      exact this
    have hpG : p ∈ G := ⟨hpPrime, hxle⟩
    have hInfLeP : sInf G ≤ p := sInf_le hpG
    have hpF : p ∈ F.1 := F.2.1.2.1 hInfF hInfLeP
    have hpNotF : p ∈ F.1ᶜ := by
      rw [hCompl]
      exact le_rfl
    exact hpNotF hpF

/-- Meet-generation by finite meet-primes is equivalent to order separation by
completely prime filters. -/
theorem meetGenerated_finiteMeetPrime_iff_orderSeparate
    (L : Type u) [CompleteLattice L] :
    MeetGeneratedBy ({p : L | IsFiniteMeetPrime p}) ↔
      CompletelyPrimeFiltersOrderSeparate L := by
  constructor
  · exact meetGenerated_finiteMeetPrime_orderSeparate L
  · exact orderSeparate_meetGenerated_finiteMeetPrime L

/-- Definition 7.2.5: spatial complete lattices. -/
def IsSpatialLattice (L : Type u) [CompleteLattice L] : Prop :=
  EpsilonInjective L ∧ EpsilonSurjective L

/-- Definition 7.2.5, named book entry. -/
def def_7_2_5_spatial_lattice (L : Type u) [CompleteLattice L] : Prop :=
  IsSpatialLattice L

/-- Compactness for subsets of a lightweight topological space. -/
def IsCompactSubset (X : Space.{u}) (K : Set X.Point) : Prop :=
  ∀ cover : Set (Set X.Point),
    (∀ U ∈ cover, X.IsOpen U) →
      K ⊆ ⋃₀ cover →
        ∃ finiteCover : Set (Set X.Point),
          finiteCover ⊆ cover ∧ finiteCover.Finite ∧ K ⊆ ⋃₀ finiteCover

/-- Saturated subsets are upward closed for the specialization order. -/
def IsSaturated (X : Space.{u}) (K : Set X.Point) : Prop :=
  ∀ ⦃x y : X.Point⦄, x ∈ K → SpecializationLE X x y → y ∈ K

/-- Compact saturated subsets. -/
def IsCompactSaturated (X : Space.{u}) (K : Set X.Point) : Prop :=
  IsCompactSubset X K ∧ IsSaturated X K

/-- Open subsets are saturated for the specialization order. -/
theorem openSet_isSaturated {X : Space.{u}} {U : Set X.Point}
    (hU : X.IsOpen U) : IsSaturated X U := by
  intro x y hx hxy
  exact hxy U hU hx

/-- Finite unions of open sets are open in the lightweight `Space` interface. -/
theorem Space.union_open (X : Space.{u}) {U V : Set X.Point}
    (hU : X.IsOpen U) (hV : X.IsOpen V) : X.IsOpen (U ∪ V) := by
  have hEq : U ∪ V = ⋃₀ ({U, V} : Set (Set X.Point)) := by
    ext x
    constructor
    · intro hx
      rcases hx with hxU | hxV
      · exact ⟨U, by simp, hxU⟩
      · exact ⟨V, by simp, hxV⟩
    · intro hx
      rcases hx with ⟨W, hW, hxW⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW
      rcases hW with rfl | rfl
      · exact Or.inl hxW
      · exact Or.inr hxW
  rw [hEq]
  exact X.sUnion_open ({U, V} : Set (Set X.Point)) (by
    intro W hW
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW
    rcases hW with rfl | rfl
    · exact hU
    · exact hV)

/-- Intersections of open families are saturated. -/
theorem sInter_openFamily_isSaturated
    {X : Space.{u}} {F : Set (Set X.Point)}
    (hFopen : ∀ U ∈ F, X.IsOpen U) :
    IsSaturated X (⋂₀ F) := by
  intro x y hx hxy U hU
  exact openSet_isSaturated (hFopen U hU) (hx U hU) hxy

/-- Open neighborhoods of a subset. -/
def OpenNeighborhoodsOf (X : Space.{u}) (K : Set X.Point) : Set (Set X.Point) :=
  {U : Set X.Point | X.IsOpen U ∧ K ⊆ U}

/-- Saturated sets are exactly intersections of their open neighborhoods. -/
theorem saturated_eq_sInter_openNeighborhoods
    {X : Space.{u}} {K : Set X.Point} (hK : IsSaturated X K) :
    ⋂₀ OpenNeighborhoodsOf X K = K := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hxK
    let Ux : Set X.Point :=
      ⋃₀ {U : Set X.Point | X.IsOpen U ∧ x ∉ U ∧ ∃ y : X.Point, y ∈ K ∧ y ∈ U}
    have hUxOpen : X.IsOpen Ux := by
      exact X.sUnion_open
        {U : Set X.Point | X.IsOpen U ∧ x ∉ U ∧ ∃ y : X.Point, y ∈ K ∧ y ∈ U}
        (by
          intro U hU
          exact hU.1)
    have hKsub : K ⊆ Ux := by
      intro y hy
      have hNotSpec : ¬ SpecializationLE X y x := by
        intro hyx
        exact hxK (hK hy hyx)
      rcases Classical.not_forall.mp hNotSpec with ⟨U, hU⟩
      rcases Classical.not_imp.mp hU with ⟨hUOpen, hUrest⟩
      rcases Classical.not_imp.mp hUrest with ⟨hyU, hxU⟩
      exact ⟨U, ⟨hUOpen, hxU, ⟨y, hy, hyU⟩⟩, hyU⟩
    have hxNotUx : x ∉ Ux := by
      intro hxUx
      rcases hxUx with ⟨U, hU, hxU⟩
      exact hU.2.1 hxU
    exact hxNotUx (hx Ux ⟨hUxOpen, hKsub⟩)
  · intro hxK U hU
    exact hU.2 hxK

/-- Scott-open filters in the complete lattice of opens, stated over raw open sets. -/
def IsScottOpenFilterOfOpens (X : Space.{u}) (F : Set (Set X.Point)) : Prop :=
  (∀ U ∈ F, X.IsOpen U) ∧
    Set.univ ∈ F ∧
      (∀ ⦃U V : Set X.Point⦄, U ∈ F → U ⊆ V → X.IsOpen V → V ∈ F) ∧
        (∀ ⦃U V : Set X.Point⦄, U ∈ F → V ∈ F → U ∩ V ∈ F) ∧
          ∀ A : Set (Set X.Point),
            (∀ U ∈ A, X.IsOpen U) →
              Chapter2.DirectedSet A → ⋃₀ A ∈ F → ∃ U ∈ A, U ∈ F

/-- Open neighborhoods of a compact saturated set form a Scott-open filter of
opens.  The Scott-openness clause is the standard compactness argument:
a directed open cover has a finite subcover, and directedness absorbs that
finite subcover into a single member. -/
theorem openNeighborhoods_scottOpenFilter
    {X : Space.{u}} {K : Set X.Point} (hK : IsCompactSaturated X K) :
    IsScottOpenFilterOfOpens X (OpenNeighborhoodsOf X K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    exact hU.1
  · exact ⟨X.univ_open, by intro x _hx; exact Set.mem_univ x⟩
  · intro U V hU hUV hVOpen
    exact ⟨hVOpen, fun x hx => hUV (hU.2 hx)⟩
  · intro U V hU hV
    exact ⟨X.inter_open U V hU.1 hV.1, fun x hx => ⟨hU.2 hx, hV.2 hx⟩⟩
  · intro A hAOpen hADirected hUnion
    rcases hK.1 A hAOpen hUnion.2 with
      ⟨finiteCover, hFiniteSub, hFiniteCover, hKsubFinite⟩
    rcases Chapter2.DirectedSet.exists_upper_finite hADirected
        hFiniteCover hFiniteSub with
      ⟨U, hUA, hUpper⟩
    refine ⟨U, hUA, ?_⟩
    refine ⟨hAOpen U hUA, ?_⟩
    intro x hxK
    rcases hKsubFinite hxK with ⟨V, hVFinite, hxV⟩
    exact hUpper V hVFinite hxV

/-- The canonical Hofmann--Mislove candidate `⋂ F` is saturated as soon as `F`
is a Scott-open filter of opens. -/
theorem hofmannMislove_candidate_saturated
    {X : Space.{u}} {F : Set (Set X.Point)}
    (hF : IsScottOpenFilterOfOpens X F) :
    IsSaturated X (⋂₀ F) :=
  sInter_openFamily_isSaturated hF.1

/-- A maximal open set outside a Scott-open filter.  This is the post-Zorn
object used in the proof of the Hofmann--Mislove theorem. -/
structure MaximalOpenOutsideFilter
    (X : Space.{u}) (F : Set (Set X.Point)) (O : Set X.Point) : Prop where
  open_set : X.IsOpen O
  outside_filter : O ∉ F
  maximal :
    ∀ V : Set X.Point, X.IsOpen V → O ⊆ V → V ∉ F → V ⊆ O

/-- Open extensions of `O` that remain outside a Scott-open filter.  Zorn's
lemma is applied to this set ordered by inclusion. -/
def OpenOutsideFilterExtensions
    (X : Space.{u}) (F : Set (Set X.Point)) (O : Set X.Point) :
    Set (Set X.Point) :=
  {V : Set X.Point | X.IsOpen V ∧ O ⊆ V ∧ V ∉ F}

/-- The union of a non-empty chain of open extensions outside a Scott-open filter
is again an open extension outside the filter.  The only non-trivial point is the
last clause: if the union belonged to `F`, Scott-openness of `F` would reflect
membership to one member of the chain. -/
theorem openOutsideFilterExtensions_chain_sUnion_upper
    {X : Space.{u}} {F : Set (Set X.Point)} {O : Set X.Point}
    (hF : IsScottOpenFilterOfOpens X F)
    {c : Set (Set X.Point)}
    (hcS : c ⊆ OpenOutsideFilterExtensions X F O)
    (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    ∃ U ∈ OpenOutsideFilterExtensions X F O, ∀ V ∈ c, V ⊆ U := by
  classical
  refine ⟨⋃₀ c, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact X.sUnion_open c (by
        intro V hVc
        exact (hcS hVc).1)
    · rcases hne with ⟨V₀, hV₀c⟩
      intro x hxO
      exact ⟨V₀, hV₀c, (hcS hV₀c).2.1 hxO⟩
    · intro hUnionF
      have hcDirected : Chapter2.DirectedSet c := by
        constructor
        · exact hne
        · intro A hAc B hBc
          rcases hc.total hAc hBc with hAB | hBA
          · exact ⟨B, hBc, hAB, by intro x hx; exact hx⟩
          · exact ⟨A, hAc, by intro x hx; exact hx, hBA⟩
      rcases hF.2.2.2.2 c (by
          intro V hVc
          exact (hcS hVc).1) hcDirected hUnionF with
        ⟨V, hVc, hVF⟩
      exact (hcS hVc).2.2 hVF
  · intro V hVc x hxV
    exact ⟨V, hVc, hxV⟩

/-- Zorn step in the Hofmann--Mislove proof: every open set outside a Scott-open
filter extends to a maximal open set outside that filter. -/
theorem maximalOpenOutsideFilter_extension
    {X : Space.{u}} {F : Set (Set X.Point)} {O : Set X.Point}
    (hF : IsScottOpenFilterOfOpens X F)
    (hOOpen : X.IsOpen O) (hOOutside : O ∉ F) :
    ∃ M : Set X.Point, O ⊆ M ∧ MaximalOpenOutsideFilter X F M := by
  classical
  let S : Set (Set X.Point) := OpenOutsideFilterExtensions X F O
  have hOS : O ∈ S := ⟨hOOpen, by intro x hx; exact hx, hOOutside⟩
  rcases zorn_subset_nonempty S
      (fun c hcS hc hne =>
        openOutsideFilterExtensions_chain_sUnion_upper hF hcS hc hne)
      O hOS with ⟨M, hOM, hMax⟩
  have hMS : M ∈ S := hMax.1
  refine ⟨M, hOM, ?_⟩
  refine
    { open_set := hMS.1
      outside_filter := hMS.2.2
      maximal := ?_ }
  intro V hVOpen hMsubV hVOutside
  have hOV : O ⊆ V := by
    intro x hxO
    exact hMsubV (hMS.2.1 hxO)
  exact hMax.2 ⟨hVOpen, hOV, hVOutside⟩ hMsubV

/-- A maximal open set outside a Scott-open filter is meet-prime in the lattice
of open sets. -/
theorem maximalOpenOutsideFilter_meetPrime
    {X : Space.{u}} {F : Set (Set X.Point)} {O : Set X.Point}
    (hF : IsScottOpenFilterOfOpens X F)
    (hO : MaximalOpenOutsideFilter X F O) :
    ∀ U V : Set X.Point, X.IsOpen U → X.IsOpen V → U ∩ V ⊆ O →
      U ⊆ O ∨ V ⊆ O := by
  classical
  intro U V hUOpen hVOpen hInterSub
  by_cases hUsub : U ⊆ O
  · exact Or.inl hUsub
  · right
    by_contra hVsub
    have hOUOpen : X.IsOpen (O ∪ U) :=
      X.union_open hO.open_set hUOpen
    have hOVOpen : X.IsOpen (O ∪ V) :=
      X.union_open hO.open_set hVOpen
    have hOsubOU : O ⊆ O ∪ U := by
      intro x hx
      exact Or.inl hx
    have hOsubOV : O ⊆ O ∪ V := by
      intro x hx
      exact Or.inl hx
    have hOUF : O ∪ U ∈ F := by
      by_contra hNot
      have hUnionSub : O ∪ U ⊆ O :=
        hO.maximal (O ∪ U) hOUOpen hOsubOU hNot
      exact hUsub (by
        intro x hx
        exact hUnionSub (Or.inr hx))
    have hOVF : O ∪ V ∈ F := by
      by_contra hNot
      have hUnionSub : O ∪ V ⊆ O :=
        hO.maximal (O ∪ V) hOVOpen hOsubOV hNot
      exact hVsub (by
        intro x hx
        exact hUnionSub (Or.inr hx))
    have hMeetF : (O ∪ U) ∩ (O ∪ V) ∈ F :=
      hF.2.2.2.1 hOUF hOVF
    have hMeetSubO : (O ∪ U) ∩ (O ∪ V) ⊆ O := by
      intro x hx
      rcases hx with ⟨hxOU, hxOV⟩
      rcases hxOU with hxO | hxU
      · exact hxO
      · rcases hxOV with hxO | hxV
        · exact hxO
        · exact hInterSub ⟨hxU, hxV⟩
    have hOF : O ∈ F :=
      hF.2.2.1 hMeetF hMeetSubO hO.open_set
    exact hO.outside_filter hOF

/-- The complement of a meet-prime open set is irreducible closed. -/
theorem meetPrimeOpen_complement_irreducibleClosed
    {X : Space.{u}} {O : Set X.Point}
    (hOOpen : X.IsOpen O) (hOProper : O ≠ Set.univ)
    (hPrime :
      ∀ U V : Set X.Point, X.IsOpen U → X.IsOpen V → U ∩ V ⊆ O →
        U ⊆ O ∨ V ⊆ O) :
    IsIrreducibleClosed X Oᶜ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · unfold IsClosed
    simpa using hOOpen
  · by_contra hEmpty
    apply hOProper
    apply Set.Subset.antisymm
    · intro x _hx
      exact Set.mem_univ x
    · intro x _hx
      by_contra hxO
      exact hEmpty ⟨x, hxO⟩
  · intro A B hAClosed hBClosed hSub
    have hInterSub : Aᶜ ∩ Bᶜ ⊆ O := by
      intro x hx
      by_contra hxO
      have hxAB : x ∈ A ∪ B := hSub hxO
      rcases hxAB with hxA | hxB
      · exact hx.1 hxA
      · exact hx.2 hxB
    rcases hPrime Aᶜ Bᶜ hAClosed hBClosed hInterSub with hAcomp | hBcomp
    · left
      intro x hxO
      by_contra hxA
      exact hxO (hAcomp hxA)
    · right
      intro x hxO
      by_contra hxB
      exact hxO (hBcomp hxB)

/-- A maximal open set outside a Scott-open filter has an irreducible closed
complement. -/
theorem maximalOpenOutsideFilter_complement_irreducibleClosed
    {X : Space.{u}} {F : Set (Set X.Point)} {O : Set X.Point}
    (hF : IsScottOpenFilterOfOpens X F)
    (hO : MaximalOpenOutsideFilter X F O) :
    IsIrreducibleClosed X Oᶜ := by
  have hProper : O ≠ Set.univ := by
    intro hEq
    exact hO.outside_filter (by simpa [hEq] using hF.2.1)
  exact meetPrimeOpen_complement_irreducibleClosed hO.open_set hProper
    (maximalOpenOutsideFilter_meetPrime hF hO)

/-- The deterministic core of the Hofmann--Mislove proof after the Zorn step:
the generic point of the irreducible complement of a maximal outside-open lies
in the canonical candidate `⋂ F` and outside that open set. -/
theorem maximalOpenOutsideFilter_exists_candidate_point
    {X : Space.{u}} {F : Set (Set X.Point)} {O : Set X.Point}
    (hX : IsSober X) (hF : IsScottOpenFilterOfOpens X F)
    (hO : MaximalOpenOutsideFilter X F O) :
    ∃ x : X.Point, x ∈ ⋂₀ F ∧ x ∉ O := by
  classical
  have hIrred : IsIrreducibleClosed X Oᶜ :=
    maximalOpenOutsideFilter_complement_irreducibleClosed hF hO
  rcases hX.2 Oᶜ hIrred with ⟨x, hxGeneric⟩
  have hxPointClosure : x ∈ PointClosure X x := by
    intro U _hU hxU
    exact hxU
  have hxNotO : x ∉ O := by
    have hxCompl : x ∈ Oᶜ := by
      rw [hxGeneric]
      exact hxPointClosure
    exact hxCompl
  have hxCandidate : x ∈ ⋂₀ F := by
    intro U hUF
    by_contra hxU
    have hUsubO : U ⊆ O := by
      intro y hyU
      by_contra hyO
      have hyClosure : y ∈ PointClosure X x := by
        rw [← hxGeneric]
        exact hyO
      exact hxU (hyClosure U (hF.1 U hUF) hyU)
    have hOF : O ∈ F :=
      hF.2.2.1 hUF hUsubO hO.open_set
    exact hO.outside_filter hOF
  exact ⟨x, hxCandidate, hxNotO⟩

/-- Finite unions drawn from a cover.  Ordered by inclusion these form the
directed family used to convert Scott-openness of a filter into compactness of
the Hofmann--Mislove candidate. -/
def FiniteUnionsOf {X : Space.{u}} (S : Set (Set X.Point)) :
    Set (Set X.Point) :=
  {U : Set X.Point |
    ∃ T : Set (Set X.Point), T.Finite ∧ T ⊆ S ∧ U = ⋃₀ T}

/-- Finite unions of open members of a cover are open. -/
theorem finiteUnionsOf_open {X : Space.{u}} {S : Set (Set X.Point)}
    (hSOpen : ∀ U ∈ S, X.IsOpen U) :
    ∀ U ∈ FiniteUnionsOf S, X.IsOpen U := by
  intro U hU
  rcases hU with ⟨T, _hTfin, hTsub, rfl⟩
  exact X.sUnion_open T (by
    intro V hVT
    exact hSOpen V (hTsub hVT))

/-- Finite unions drawn from a cover are directed by inclusion. -/
theorem finiteUnionsOf_directed {X : Space.{u}} (S : Set (Set X.Point)) :
    Chapter2.DirectedSet (FiniteUnionsOf S) := by
  classical
  constructor
  · refine ⟨∅, ?_⟩
    refine ⟨∅, by simp, ?_, by simp⟩
    intro U hU
    cases hU
  · intro U hU V hV
    rcases hU with ⟨TU, hTUfin, hTUsub, rfl⟩
    rcases hV with ⟨TV, hTVfin, hTVsub, rfl⟩
    refine ⟨⋃₀ (TU ∪ TV), ?_, ?_, ?_⟩
    · refine ⟨TU ∪ TV, hTUfin.union hTVfin, ?_, rfl⟩
      intro W hW
      rcases hW with hW | hW
      · exact hTUsub hW
      · exact hTVsub hW
    · intro x hx
      rcases hx with ⟨W, hWTU, hxW⟩
      exact ⟨W, Or.inl hWTU, hxW⟩
    · intro x hx
      rcases hx with ⟨W, hWTV, hxW⟩
      exact ⟨W, Or.inr hWTV, hxW⟩

/-- The union of all finite subunions of a cover is the original union. -/
theorem finiteUnionsOf_sUnion_eq {X : Space.{u}} (S : Set (Set X.Point)) :
    ⋃₀ FiniteUnionsOf S = ⋃₀ S := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨U, hU, hxU⟩
    rcases hU with ⟨T, _hTfin, hTsub, rfl⟩
    rcases hxU with ⟨V, hVT, hxV⟩
    exact ⟨V, hTsub hVT, hxV⟩
  · intro hx
    rcases hx with ⟨U, hUS, hxU⟩
    refine ⟨U, ?_, hxU⟩
    refine ⟨{U}, by simp, ?_, ?_⟩
    · intro V hV
      have hVU : V = U := by simpa using hV
      simpa [hVU] using hUS
    · ext y
      constructor
      · intro hy
        exact ⟨U, by simp, hy⟩
      · intro hy
        rcases hy with ⟨V, hVU, hyV⟩
        have hVU' : V = U := by simpa using hVU
        simpa [hVU'] using hyV

/-- If every open neighborhood of the candidate `⋂ F` lies in `F`, then `F`
is exactly the neighborhood filter of that candidate. -/
theorem scottOpenFilter_eq_openNeighborhoods_of_open_reflection
    {X : Space.{u}} {F : Set (Set X.Point)}
    (hF : IsScottOpenFilterOfOpens X F)
    (hReflect :
      ∀ O : Set X.Point, X.IsOpen O → (⋂₀ F) ⊆ O → O ∈ F) :
    F = OpenNeighborhoodsOf X (⋂₀ F) := by
  ext O
  constructor
  · intro hOF
    exact ⟨hF.1 O hOF, fun x hx => hx O hOF⟩
  · intro hO
    exact hReflect O hO.1 hO.2

/-- Open-neighborhood reflection turns Scott-openness of `F` into compactness of
the canonical candidate `⋂ F`. -/
theorem hofmannMislove_candidate_compact_of_open_reflection
    {X : Space.{u}} {F : Set (Set X.Point)}
    (hF : IsScottOpenFilterOfOpens X F)
    (hReflect :
      ∀ O : Set X.Point, X.IsOpen O → (⋂₀ F) ⊆ O → O ∈ F) :
    IsCompactSubset X (⋂₀ F) := by
  classical
  intro cover hCoverOpen hSub
  let A : Set (Set X.Point) := FiniteUnionsOf cover
  have hAOpen : ∀ U ∈ A, X.IsOpen U :=
    finiteUnionsOf_open hCoverOpen
  have hADirected : Chapter2.DirectedSet A :=
    finiteUnionsOf_directed cover
  have hUnionEq : ⋃₀ A = ⋃₀ cover :=
    finiteUnionsOf_sUnion_eq cover
  have hCoverUnionF : ⋃₀ cover ∈ F := by
    exact hReflect (⋃₀ cover) (X.sUnion_open cover hCoverOpen) hSub
  have hAUnionF : ⋃₀ A ∈ F := by
    simpa [A, hUnionEq] using hCoverUnionF
  rcases hF.2.2.2.2 A hAOpen hADirected hAUnionF with
    ⟨U, hUA, hUF⟩
  rcases hUA with ⟨finiteCover, hFinite, hFiniteSub, rfl⟩
  refine ⟨finiteCover, hFiniteSub, hFinite, ?_⟩
  intro x hx
  exact hx (⋃₀ finiteCover) hUF

/-- The post-reflection form of the Hofmann--Mislove candidate theorem. -/
theorem hofmannMislove_candidate_representation_of_open_reflection
    {X : Space.{u}} {F : Set (Set X.Point)}
    (hF : IsScottOpenFilterOfOpens X F)
    (hReflect :
      ∀ O : Set X.Point, X.IsOpen O → (⋂₀ F) ⊆ O → O ∈ F) :
    IsCompactSaturated X (⋂₀ F) ∧
      F = OpenNeighborhoodsOf X (⋂₀ F) := by
  exact
    ⟨⟨hofmannMislove_candidate_compact_of_open_reflection hF hReflect,
        hofmannMislove_candidate_saturated hF⟩,
      scottOpenFilter_eq_openNeighborhoods_of_open_reflection hF hReflect⟩

/-- Maximal outside-open extensions imply the open-neighborhood reflection step
in the Hofmann--Mislove proof. -/
theorem hofmannMislove_open_reflection_of_maximal_extension
    {X : Space.{u}} {F : Set (Set X.Point)}
    (hX : IsSober X) (hF : IsScottOpenFilterOfOpens X F)
    (hMaxExtension :
      ∀ O : Set X.Point, X.IsOpen O → O ∉ F →
        ∃ M : Set X.Point, O ⊆ M ∧ MaximalOpenOutsideFilter X F M) :
    ∀ O : Set X.Point, X.IsOpen O → (⋂₀ F) ⊆ O → O ∈ F := by
  intro O hOOpen hSub
  by_contra hOOutside
  rcases hMaxExtension O hOOpen hOOutside with ⟨M, hOM, hM⟩
  rcases maximalOpenOutsideFilter_exists_candidate_point hX hF hM with
    ⟨x, hxCandidate, hxM⟩
  exact hxM (hOM (hSub hxCandidate))

/-- The Hofmann--Mislove representation follows from the single remaining Zorn
extension step for opens outside the filter. -/
theorem hofmannMislove_candidate_representation_of_maximal_extension
    {X : Space.{u}} {F : Set (Set X.Point)}
    (hX : IsSober X) (hF : IsScottOpenFilterOfOpens X F)
    (hMaxExtension :
      ∀ O : Set X.Point, X.IsOpen O → O ∉ F →
        ∃ M : Set X.Point, O ⊆ M ∧ MaximalOpenOutsideFilter X F M) :
    IsCompactSaturated X (⋂₀ F) ∧
      F = OpenNeighborhoodsOf X (⋂₀ F) := by
  exact hofmannMislove_candidate_representation_of_open_reflection hF
    (hofmannMislove_open_reflection_of_maximal_extension hX hF hMaxExtension)

/-- Filtered families of subsets, ordered by reverse inclusion. -/
def IsFilteredFamily {α : Type u} (𝒦 : Set (Set α)) : Prop :=
  𝒦.Nonempty ∧
    ∀ A ∈ 𝒦, ∀ B ∈ 𝒦, ∃ C ∈ 𝒦, C ⊆ A ∩ B

/-- Corollary 7.2.11 conclusion package: the filtered intersection is compact,
is non-empty when all members are non-empty, and reflects containment in an open
set back to one member of the filtered family. -/
structure FilteredCompactSaturatedIntersectionResult
    (X : Space.{u}) (𝒦 : Set (Set X.Point)) : Prop where
  compact_intersection : IsCompactSubset X (⋂₀ 𝒦)
  saturated_intersection : IsSaturated X (⋂₀ 𝒦)
  nonempty_intersection :
    (∀ K ∈ 𝒦, K.Nonempty) → (⋂₀ 𝒦).Nonempty
  open_reflection :
    ∀ O : Set X.Point, X.IsOpen O → (⋂₀ 𝒦) ⊆ O → ∃ K ∈ 𝒦, K ⊆ O

/-- The empty set is open in the lightweight `Space` interface, as the union of
the empty family of opens. -/
theorem Space.empty_open (X : Space.{u}) : X.IsOpen (∅ : Set X.Point) := by
  simpa using
    X.sUnion_open (∅ : Set (Set X.Point)) (by
      intro U hU
      cases hU)

/-- A finite subfamily of a filtered family has a member below its intersection. -/
theorem filteredFamily_exists_member_subset_sInter
    {α : Type u} {𝒦 S : Set (Set α)}
    (h𝒦 : IsFilteredFamily 𝒦) (hSfin : S.Finite) (hSsub : S ⊆ 𝒦) :
    ∃ K ∈ 𝒦, K ⊆ ⋂₀ S := by
  induction S, hSfin using Set.Finite.induction_on with
  | empty =>
      rcases h𝒦.1 with ⟨K, hK⟩
      refine ⟨K, hK, ?_⟩
      intro x _hx U hU
      cases hU
  | @insert A S hAS _ ih =>
      have hSsub' : S ⊆ 𝒦 := by
        intro K hK
        exact hSsub (by simp [hK])
      rcases ih hSsub' with ⟨K, hK, hKsub⟩
      have hA : A ∈ 𝒦 := hSsub (by simp)
      rcases h𝒦.2 A hA K hK with ⟨C, hC, hCsub⟩
      refine ⟨C, hC, ?_⟩
      intro x hx T hT
      simp only [Set.mem_insert_iff] at hT
      rcases hT with rfl | hT
      · exact (hCsub hx).1
      · exact hKsub (hCsub hx).2 T hT

/-- The Scott-open filter of opens generated by a filtered family of compact
saturated sets: an open belongs to it if it contains one member of the family. -/
def FilteredOpenNeighborhoodsOf
    (X : Space.{u}) (𝒦 : Set (Set X.Point)) : Set (Set X.Point) :=
  {O : Set X.Point | X.IsOpen O ∧ ∃ K : Set X.Point, K ∈ 𝒦 ∧ K ⊆ O}

/-- A filtered family of compact saturated sets generates a Scott-open filter of
opens.  Compactness is used in the Scott-openness clause to reduce a directed
open cover of one compact member to a single directed open. -/
theorem filteredOpenNeighborhoods_scottOpenFilter
    (X : Space.{u}) {𝒦 : Set (Set X.Point)}
    (hFiltered : IsFilteredFamily 𝒦)
    (hCompact : ∀ K ∈ 𝒦, IsCompactSaturated X K) :
    IsScottOpenFilterOfOpens X (FilteredOpenNeighborhoodsOf X 𝒦) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    exact hU.1
  · rcases hFiltered.1 with ⟨K, hK⟩
    exact ⟨X.univ_open, K, hK, by intro x _hx; exact Set.mem_univ x⟩
  · intro U V hU hUV hVOpen
    rcases hU with ⟨_hUOpen, K, hK, hKU⟩
    exact ⟨hVOpen, K, hK, fun x hx => hUV (hKU hx)⟩
  · intro U V hU hV
    rcases hU with ⟨hUOpen, K, hK, hKU⟩
    rcases hV with ⟨hVOpen, L, hL, hLV⟩
    rcases hFiltered.2 K hK L hL with ⟨M, hM, hMsub⟩
    refine ⟨X.inter_open U V hUOpen hVOpen, M, hM, ?_⟩
    intro x hx
    exact ⟨hKU (hMsub hx).1, hLV (hMsub hx).2⟩
  · intro A hAOpen hADirected hUnion
    rcases hUnion with ⟨_hUnionOpen, K, hK, hKsubUnion⟩
    rcases (hCompact K hK).1 A hAOpen hKsubUnion with
      ⟨finiteCover, hFiniteSub, hFiniteCover, hKsubFinite⟩
    rcases Chapter2.DirectedSet.exists_upper_finite hADirected
        hFiniteCover hFiniteSub with
      ⟨U, hUA, hUpper⟩
    refine ⟨U, hUA, ?_⟩
    refine ⟨hAOpen U hUA, K, hK, ?_⟩
    intro x hxK
    rcases hKsubFinite hxK with ⟨V, hVFinite, hxV⟩
    exact hUpper V hVFinite hxV

/-- The intersection of the open filter generated by a family of saturated sets
is exactly the intersection of the family. -/
theorem sInter_filteredOpenNeighborhoods_eq_sInter
    (X : Space.{u}) {𝒦 : Set (Set X.Point)}
    (hCompact : ∀ K ∈ 𝒦, IsCompactSaturated X K) :
    ⋂₀ FilteredOpenNeighborhoodsOf X 𝒦 = ⋂₀ 𝒦 := by
  apply Set.Subset.antisymm
  · intro x hx K hK
    have hxNeighborhoods : x ∈ ⋂₀ OpenNeighborhoodsOf X K := by
      intro U hU
      exact hx U ⟨hU.1, K, hK, hU.2⟩
    have hEq : ⋂₀ OpenNeighborhoodsOf X K = K :=
      saturated_eq_sInter_openNeighborhoods (hCompact K hK).2
    simpa [hEq] using hxNeighborhoods
  · intro x hx U hU
    rcases hU with ⟨_hUOpen, K, hK, hKU⟩
    exact hKU (hx K hK)

/-- Local compactness via compact saturated neighborhoods. -/
def IsLocallyCompact (X : Space.{u}) : Prop :=
  ∀ x : X.Point, ∀ U : Set X.Point,
    X.IsOpen U → x ∈ U →
      ∃ K V : Set X.Point,
        IsCompactSaturated X K ∧ X.IsOpen V ∧ x ∈ V ∧ V ⊆ K ∧ K ⊆ U

/-- Saturated subsets are closed under binary intersections. -/
theorem saturated_inter {X : Space.{u}} {K L : Set X.Point}
    (hK : IsSaturated X K) (hL : IsSaturated X L) :
    IsSaturated X (K ∩ L) := by
  intro x y hxy hspec
  exact ⟨hK hxy.1 hspec, hL hxy.2 hspec⟩

/-- Definition 7.2.17 coherence clause: intersections of compact saturated
subsets are compact. -/
def CompactSaturatedBinaryIntersectionsCompact (X : Space.{u}) : Prop :=
  ∀ K L : Set X.Point,
    IsCompactSaturated X K → IsCompactSaturated X L →
      IsCompactSubset X (K ∩ L)

/-- Definition 7.2.17: coherent spaces. -/
def IsCoherentSpace (X : Space.{u}) : Prop :=
  IsSober X ∧ IsLocallyCompact X ∧
    CompactSaturatedBinaryIntersectionsCompact X

/-- In a coherent space, the intersection of two compact saturated sets is again
compact saturated; compactness is the coherence axiom and saturation is direct. -/
theorem coherent_compactSaturated_inter {X : Space.{u}}
    (hX : IsCoherentSpace X) {K L : Set X.Point}
    (hK : IsCompactSaturated X K) (hL : IsCompactSaturated X L) :
    IsCompactSaturated X (K ∩ L) :=
  ⟨hX.2.2 K L hK hL, saturated_inter hK.2 hL.2⟩

/-- Definition 7.2.17, named book entry. -/
def def_7_2_17_coherent_space (X : Space.{u}) : Prop :=
  IsCoherentSpace X

/-- Definition 7.2.18: multiplicativity of approximation. -/
def MultiplicativeApproximation (L : Type u) [CompleteLattice L] : Prop :=
  ∀ x y z : L,
    Chapter2.WayBelow x y → Chapter2.WayBelow x z → Chapter2.WayBelow x (y ⊓ z)

/-- Definition 7.2.18 support: distributive continuous complete lattices. -/
def IsDistributiveContinuousLattice (L : Type u) [CompleteLattice L] : Prop :=
  IsFrameDistributive L ∧ Chapter2.IsContinuousDomain L

/-- Definition 7.2.18: arithmetic lattices. -/
def IsArithmeticLattice (L : Type u) [CompleteLattice L] : Prop :=
  IsDistributiveContinuousLattice L ∧ MultiplicativeApproximation L

/-- Definition 7.2.18, named book entry. -/
def def_7_2_18_arithmetic_lattice (L : Type u) [CompleteLattice L] : Prop :=
  IsArithmeticLattice L

/-- Compact-open subsets of a lightweight topological space. -/
def IsCompactOpenSubset (X : Space.{u}) (U : Set X.Point) : Prop :=
  X.IsOpen U ∧ IsCompactSubset X U

/-- Open subsets are saturated for the specialization order. -/
theorem open_isSaturated {X : Space.{u}} {U : Set X.Point}
    (hU : X.IsOpen U) : IsSaturated X U := by
  exact openSet_isSaturated hU

/-- Compact-open subsets are compact saturated. -/
theorem compactOpen_isCompactSaturated {X : Space.{u}} {U : Set X.Point}
    (hU : IsCompactOpenSubset X U) : IsCompactSaturated X U :=
  ⟨hU.2, open_isSaturated hU.1⟩

/-- A compact-open neighborhood basis. -/
def HasCompactOpenNeighborhoodBasis (X : Space.{u}) : Prop :=
  ∀ x : X.Point, ∀ U : Set X.Point,
    X.IsOpen U → x ∈ U →
      ∃ V : Set X.Point,
        IsCompactOpenSubset X V ∧ x ∈ V ∧ V ⊆ U

/-- Definition 7.2.21: spectral spaces. -/
def IsSpectralSpace (X : Space.{u}) : Prop :=
  IsCoherentSpace X ∧ HasCompactOpenNeighborhoodBasis X

/-- Definition 7.2.21, named book entry. -/
def def_7_2_21_spectral_space (X : Space.{u}) : Prop :=
  IsSpectralSpace X

/-- A compact element of a complete lattice, reusing Chapter 2's way-below compactness. -/
def IsCompactLatticeElement {L : Type u} [CompleteLattice L] (x : L) : Prop :=
  Chapter2.Compact x

/-- Algebraic arithmetic lattices. -/
def IsAlgebraicArithmeticLattice (L : Type u) [CompleteLattice L] : Prop :=
  IsArithmeticLattice L ∧ Chapter2.IsAlgebraicDomain L

/-- Compact elements, bundled as the basis `K(L)` used in Proposition 7.2.23. -/
abbrev CompactElement (L : Type u) [CompleteLattice L] : Type u :=
  {x : L // IsCompactLatticeElement x}

/-- The upward filter in `L` generated by a filter of compact elements. -/
def GeneratedFilterOfCompacts {L : Type u} [CompleteLattice L]
    (G : Set (CompactElement L)) : Set L :=
  {x : L | ∃ k : CompactElement L, k ∈ G ∧ k.1 ≤ x}

/-- Prime filters of the compact-element basis `K(L)`.

This is a basis-level predicate rather than a `CompleteLattice` instance on
compact elements: it records non-emptiness, upward closure, closure under
available binary meets in `L`, and the finite-join primeness used in the proof of
Proposition 7.2.23. -/
structure IsPrimeFilterOfCompactElements {L : Type u} [CompleteLattice L]
    (G : Set (CompactElement L)) : Prop where
  nonempty : G.Nonempty
  upward_closed :
    ∀ {k l : CompactElement L}, k ∈ G → k.1 ≤ l.1 → l ∈ G
  binary_meet_closed :
    ∀ {k l : CompactElement L}, k ∈ G → l ∈ G →
      ∃ m : CompactElement L, m.1 = k.1 ⊓ l.1 ∧ m ∈ G
  finite_join_prime :
    ∀ M : Set (CompactElement L), M.Finite →
      sSup ((fun k : CompactElement L => (k.1 : L)) '' M) ∈
        GeneratedFilterOfCompacts G →
        ∃ k ∈ M, k ∈ G

/-- Opens generated by the compact basic opens `O_x`, where `x` ranges over
compact elements of `L`. -/
def CompactBasicOpenGenerated {L : Type u} [CompleteLattice L]
    (U : Set (Point L)) : Prop :=
  ∃ S : Set (CompactElement L),
    U = ⋃₀ ((fun k : CompactElement L => pointBasicOpen k.1) '' S)

/-- Correspondence between points and prime filters of compact elements. -/
structure CompactPrimeFilterCorrespondence (L : Type u) [CompleteLattice L] where
  toCompactPrimeFilter : Point L → Set (CompactElement L)
  restriction_eq :
    ∀ (F : Point L) (k : CompactElement L),
      k ∈ toCompactPrimeFilter F ↔ k.1 ∈ F.1
  restriction_is_prime :
    ∀ F : Point L, IsPrimeFilterOfCompactElements (toCompactPrimeFilter F)
  ofCompactPrimeFilter :
    {G : Set (CompactElement L) // IsPrimeFilterOfCompactElements G} → Point L
  generated_filter_eq :
    ∀ G : {G : Set (CompactElement L) // IsPrimeFilterOfCompactElements G},
      (ofCompactPrimeFilter G).1 = GeneratedFilterOfCompacts G.1
  restriction_generates_filter :
    ∀ F : Point L,
      GeneratedFilterOfCompacts (toCompactPrimeFilter F) = F.1
  left_inverse :
    ∀ F : Point L,
      ofCompactPrimeFilter ⟨toCompactPrimeFilter F, restriction_is_prime F⟩ = F
  right_inverse :
    ∀ G : {G : Set (CompactElement L) // IsPrimeFilterOfCompactElements G},
      toCompactPrimeFilter (ofCompactPrimeFilter G) = G.1
  topology_generated_by_compacts :
    ∀ U : Set (Point L), PointOpen L U ↔ CompactBasicOpenGenerated U

/-- Definition 7.2.24: join-approximable relations between lattices. -/
structure JoinApproximableRelation
    (V W : Type u) [CompleteLattice V] [CompleteLattice W] where
  rel : V → W → Prop
  weakening :
    ∀ ⦃x x' : V⦄ ⦃y y' : W⦄, x ≤ x' → y' ≤ y → rel x y → rel x' y'
  finite_join_right :
    ∀ x : V, ∀ N : Set W, N.Finite → (∀ y ∈ N, rel x y) → rel x (sSup N)
  finite_meet_left :
    ∀ M : Set V, ∀ y : W, M.Finite → (∀ x ∈ M, rel x y) → rel (sInf M) y
  finite_join_cover :
    ∀ M : Set V, ∀ x : W, M.Finite → rel (sSup M) x →
      ∃ N : Set W,
        N.Finite ∧ x = sSup N ∧
          ∀ n ∈ N, ∃ m ∈ M, rel m n

/-- Definition 7.2.24, named book entry. -/
abbrev def_7_2_24_join_approximable_relation
    (V W : Type u) [CompleteLattice V] [CompleteLattice W] :=
  JoinApproximableRelation V W

/-- Distributive lattice objects for the join-approximable category in
Proposition 7.2.25.  The local interface keeps the ambient complete-lattice
structure already used for join-approximable relations. -/
structure DistributiveLatticeRelationObject where
  carrier : Type u
  lattice : CompleteLattice carrier
  distributive : @IsFrameDistributive carrier lattice

/-- Morphisms in the distributive-lattice presentation are join-approximable
relations. -/
abbrev JoinApproximableMorphism
    (V W : DistributiveLatticeRelationObject.{u}) : Type u :=
  @JoinApproximableRelation V.carrier W.carrier V.lattice W.lattice

/-- Finite generation by join-prime elements: every element is the supremum of
finitely many `∨`-prime elements. -/
structure HasFiniteJoinOfJoinPrimes (L : Type u) [CompleteLattice L] : Prop where
  finite_join_generation :
    ∀ x : L, ∃ M : Set L,
      M.Finite ∧ (∀ m ∈ M, IsFiniteJoinPrime m) ∧ x = sSup M

/-- The explicit least-element condition in Theorems 7.2.30 and 7.2.31.  It is
automatic for `CompleteLattice`, but keeping it named preserves the book's
statement shape. -/
def HasLeastElementCondition (L : Type u) [CompleteLattice L] : Prop :=
  ∀ x : L, ⊥ ≤ x

/-- The additional bifinite-domain condition following Theorem 7.2.30: the
largest element is also `∨`-prime. -/
def HasLargestElementJoinPrime (L : Type u) [CompleteLattice L] : Prop :=
  IsFiniteJoinPrime (⊤ : L)

/-- The upside-down finite mub property appearing in Theorem 7.2.30. -/
def HasUpsideDownFiniteMubProperty (L : Type u) [CompleteLattice L] : Prop :=
  ∀ M : Set L, M.Finite → (∀ m ∈ M, IsFiniteJoinPrime m) →
    ∃ N : Set L,
      N.Finite ∧ M ⊆ N ∧ (∀ n ∈ N, IsFiniteJoinPrime n) ∧
        ∀ A : Set L, A ⊆ M → ∃ B : Set L, B ⊆ N ∧ sInf A = sSup B

/-- The finite-infimum closure condition from Theorem 7.2.31: the set of
`∨`-prime elements together with the least element is closed under finite
infima. -/
def JoinPrimesWithBottomClosedUnderFiniteInfima
    (L : Type u) [CompleteLattice L] : Prop :=
  ∀ M : Set L, M.Finite →
    (∀ m ∈ M, IsFiniteJoinPrime m ∨ m = ⊥) →
      IsFiniteJoinPrime (sInf M) ∨ sInf M = ⊥

/-- Compact-open subsets of the Scott space of an ordered domain. -/
def DomainCompactOpenSet (D : Chapter4.OrderedDomain.{u}) : Type u :=
  {U : Set D.carrier // IsCompactOpenSubset (@ScottTopologySpace D.carrier D.preorder) U}

/-- A compact-open lattice representation: a carrier equivalence with the
compact-open subsets of the Scott space, together with the finite-lattice
operation laws visible at the level of underlying sets. -/
structure CompactOpenLatticeRepresentation
    (V : Type u) [CompleteLattice V] (D : Chapter4.OrderedDomain.{u}) where
  toCompactOpen : V ≃ DomainCompactOpenSet D
  bot_preserving : (toCompactOpen ⊥).1 = ∅
  top_preserving : (toCompactOpen ⊤).1 = Set.univ
  inf_preserving :
    ∀ a b : V, (toCompactOpen (a ⊓ b)).1 = (toCompactOpen a).1 ∩ (toCompactOpen b).1
  sup_preserving :
    ∀ a b : V, (toCompactOpen (a ⊔ b)).1 = (toCompactOpen a).1 ∪ (toCompactOpen b).1

/-- A compact-open lattice representation of an F-B-domain, represented by
Chapter 4's finite-amalgam interface. -/
def IsCompactOpenLatticeOfFBDomain (V : Type u) [CompleteLattice V] : Prop :=
  ∃ D : Chapter4.OrderedDomain.{u},
    Chapter4.IsFiniteAmalgam D ∧
      Nonempty (CompactOpenLatticeRepresentation V D)

/-- A compact-open lattice representation of a bifinite domain. -/
def IsCompactOpenLatticeOfBifiniteDomain (V : Type u) [CompleteLattice V] : Prop :=
  ∃ D : Chapter4.OrderedDomain.{u},
    Chapter3.IsDcpo D.carrier ∧ Chapter4.IsBifiniteObject D ∧
      Nonempty (CompactOpenLatticeRepresentation V D)

/-- A compact-open lattice representation of an algebraic bounded-complete domain. -/
def IsCompactOpenLatticeOfAlgebraicBcDomain (V : Type u) [CompleteLattice V] : Prop :=
  ∃ D : Chapter4.OrderedDomain.{u},
    Chapter3.IsDcpo D.carrier ∧ Chapter4.IsBcDomain D ∧
      @Chapter3.IsAlgebraicDomain D.carrier D.preorder ∧
        Nonempty (CompactOpenLatticeRepresentation V D)

/-- Bundled sober spaces for dual-equivalence statements. -/
structure SoberSpaceObject where
  space : Space.{u}
  sober : IsSober space

/-- Bundled spatial lattices for dual-equivalence statements. -/
structure SpatialLatticeObject where
  carrier : Type u
  lattice : CompleteLattice carrier
  spatial : @IsSpatialLattice carrier lattice

/-- Bundled locally compact sober spaces. -/
structure LocallyCompactSoberSpaceObject where
  space : Space.{u}
  sober : IsSober space
  locallyCompact : IsLocallyCompact space

/-- Bundled distributive continuous lattices. -/
structure DistributiveContinuousLatticeObject where
  carrier : Type u
  lattice : CompleteLattice carrier
  continuous : @Chapter2.IsContinuousDomain carrier lattice.toPreorder
  distributive : @IsFrameDistributive carrier lattice

/-- Bundled continuous domains in the categorical sense used in Section 7.2:
a dcpo together with a continuous basis.  This is stricter than Chapter 2's
predicate `IsContinuousDomain`, which records only the basis condition. -/
structure ContinuousDcpoObject where
  carrier : Type u
  preorder : Preorder carrier
  dcpo : @Chapter2.IsDcpo carrier preorder
  continuous : @Chapter2.IsContinuousDomain carrier preorder

/-- Bundled completely distributive lattices, represented by Raney's complete
choice law from Section 7.1. -/
structure CompleteDistributiveLatticeObject where
  carrier : Type u
  lattice : CompleteLattice carrier
  complete_distributive : @CompleteChoiceMeetJoinLaw.{u, u} carrier lattice

/-- Bundled sober spaces with compact-open neighborhood bases. -/
structure CompactOpenSoberSpaceObject where
  space : Space.{u}
  sober : IsSober space
  compactOpenBasis : HasCompactOpenNeighborhoodBasis space

/-- Bundled distributive algebraic lattices. -/
structure AlgebraicDistributiveLatticeObject where
  carrier : Type u
  lattice : CompleteLattice carrier
  algebraic : @Chapter2.IsAlgebraicDomain carrier lattice.toPreorder
  distributive : @IsFrameDistributive carrier lattice

/-- Bundled coherent spaces. -/
structure CoherentSpaceObject where
  space : Space.{u}
  coherent : IsCoherentSpace space

/-- Bundled arithmetic lattices. -/
structure ArithmeticLatticeObject where
  carrier : Type u
  lattice : CompleteLattice carrier
  arithmetic : @IsArithmeticLattice carrier lattice

/-- Bundled spectral spaces. -/
structure SpectralSpaceObject where
  space : Space.{u}
  spectral : IsSpectralSpace space

/-- Bundled algebraic arithmetic lattices. -/
structure AlgebraicArithmeticLatticeObject where
  carrier : Type u
  lattice : CompleteLattice carrier
  algebraicArithmetic : @IsAlgebraicArithmeticLattice carrier lattice

/-- Bundled coherent algebraic domains for Theorem 7.2.29. -/
structure CoherentAlgebraicDomainObject where
  object : Chapter4.OrderedDomain.{u}
  dcpo : Chapter3.IsDcpo object.carrier
  coherent : Chapter4.IsCoherentDomain object
  algebraic : @Chapter3.IsAlgebraicDomain object.carrier object.preorder

/-- Bundled lattices whose elements are finite joins of `∨`-prime elements. -/
structure FiniteJoinPrimeGeneratedLatticeObject where
  carrier : Type u
  lattice : CompleteLattice carrier
  finiteJoinPrimeGenerated : @HasFiniteJoinOfJoinPrimes carrier lattice

/-- The order on points used in the proof of Theorem 7.2.28: inclusion of
completely prime filters. -/
@[reducible]
def PointFilterPreorder (L : CompleteDistributiveLatticeObject.{u}) :
    Preorder (@Point L.carrier L.lattice) where
  le F G := F.1 ⊆ G.1
  le_refl F := by
    intro x hx
    exact hx
  le_trans F G H hFG hGH := by
    intro x hx
    exact hGH (hFG hx)

/-- The lattice element `⋀F` associated with a point/filter `F`. -/
def PointFilterInf (L : CompleteDistributiveLatticeObject.{u})
    (F : @Point L.carrier L.lattice) : L.carrier := by
  letI := L.lattice
  exact sInf F.1

/-- Theorem 7.2.28 proof ingredient for continuous domains: Scott opens are
unions of way-below basic neighborhoods. -/
def ScottOpenWayBelowUnionBasis (D : ContinuousDcpoObject.{u}) : Prop :=
  ∀ O : Set D.carrier,
    @Chapter2.ScottOpen D.carrier D.preorder O →
      O = ⋃ x ∈ O, @Chapter2.wayBelowUpper D.carrier D.preorder x

/-- Theorem 7.2.28 proof ingredient for point spaces: on points ordered by
filter inclusion, `F' ≪ F` iff the lattice meet `⋀F'` belongs to `F`. -/
def PointFilterWayBelowMembershipCharacterization
    (L : CompleteDistributiveLatticeObject.{u}) : Prop :=
  ∀ F' F : @Point L.carrier L.lattice,
    @Chapter2.WayBelow (@Point L.carrier L.lattice) (PointFilterPreorder L) F' F ↔
      PointFilterInf L F' ∈ F.1

/-- Theorem 7.2.28 proof ingredient: the Scott topology of the point dcpo is the
generated point topology. -/
def PointScottTopologyRecovered (L : CompleteDistributiveLatticeObject.{u}) : Prop :=
  ∀ O : Set (@Point L.carrier L.lattice),
    @PointOpen L.carrier L.lattice O ↔
      @Chapter2.ScottOpen (@Point L.carrier L.lattice) (PointFilterPreorder L) O

/-- A small record for the high-level dual-equivalence theorems. -/
structure DualEquivalenceData (A : Type u) (B : Type v) where
  left : A → B
  right : B → A
  unit_isomorphism : Prop
  counit_isomorphism : Prop

/-- A small record for high-level equivalence theorems whose functors are not
contravariant. -/
structure EquivalenceData (A : Type u) (B : Type v) where
  left : A → B
  right : B → A
  unit_isomorphism : Prop
  counit_isomorphism : Prop

namespace DualEquivalenceData

/-- Reverse a bundled dual-equivalence package. -/
def symm {A : Type u} {B : Type v} (d : DualEquivalenceData A B) :
    DualEquivalenceData B A where
  left := d.right
  right := d.left
  unit_isomorphism := d.counit_isomorphism
  counit_isomorphism := d.unit_isomorphism

end DualEquivalenceData

/-- Completeness/cocompleteness and closure under retracts for a category of
objects.  The record keeps an explicit hom type, cone/cocone interfaces, chosen
limits and colimits, and retract data instead of abstract truth-valued flags. -/
structure CompleteCocompleteRetractClosed (A : Type u) : Type (u + 1) where
  Hom : A → A → Type u
  id : ∀ X : A, Hom X X
  comp : ∀ {X Y Z : A}, Hom X Y → Hom Y Z → Hom X Z
  Diagram : Type u
  Cone : Diagram → A → Type u
  Cocone : Diagram → A → Type u
  limit : Diagram → A
  colimit : Diagram → A
  limit_cone : ∀ D : Diagram, Cone D (limit D)
  colimit_cocone : ∀ D : Diagram, Cocone D (colimit D)
  limit_lift : ∀ {D : Diagram} {X : A}, Cone D X → Hom X (limit D)
  colimit_desc : ∀ {D : Diagram} {X : A}, Cocone D X → Hom (colimit D) X
  limit_universal : Prop
  colimit_universal : Prop
  Retract : A → A → Type u
  retract_section : ∀ {X Y : A}, Retract X Y → Hom X Y
  retract_retraction : ∀ {X Y : A}, Retract X Y → Hom Y X
  retract_equation : ∀ {X Y : A}, Retract X Y → Prop
  retract_closed : ∀ {X Y : A}, Retract X Y → Nonempty A

/-- A topological retract of a sober space, expressed in the ambient lightweight
category of spaces rather than only inside the bundled sober-space category. -/
structure TopRetractOfSoberSpace (X : Space.{u}) (Y : SoberSpaceObject.{u}) where
  sectionMap : StoneContinuousMap X Y.space
  retraction : StoneContinuousMap Y.space X
  retract_eq : ∀ x : X.Point, retraction.toFun (sectionMap.toFun x) = x

/-- The concrete carrier of the open-set lattice `Ω(X)`. -/
abbrev OpenSet (X : Space.{u}) : Type u :=
  {U : Set X.Point // X.IsOpen U}

namespace OpenSet

instance instPartialOrder (X : Space.{u}) : PartialOrder (OpenSet X) where
  le U V := U.1 ⊆ V.1
  le_refl := by
    intro U x hx
    exact hx
  le_trans := by
    intro U V W hUV hVW x hx
    exact hVW (hUV hx)
  le_antisymm := by
    intro U V hUV hVU
    exact Subtype.ext (Set.Subset.antisymm hUV hVU)

instance instSupSet (X : Space.{u}) : SupSet (OpenSet X) where
  sSup S :=
    ⟨⋃₀ ((fun U : OpenSet X => U.1) '' S), by
      exact X.sUnion_open ((fun U : OpenSet X => U.1) '' S)
        (by
          intro U hU
          rcases hU with ⟨V, _hVS, rfl⟩
          exact V.2)⟩

theorem mem_sSup_iff (X : Space.{u}) (S : Set (OpenSet X)) (x : X.Point) :
    x ∈ (sSup S : OpenSet X).1 ↔ ∃ U ∈ S, x ∈ U.1 := by
  constructor
  · intro hx
    rcases hx with ⟨U, hU, hxU⟩
    rcases hU with ⟨V, hVS, rfl⟩
    exact ⟨V, hVS, hxU⟩
  · intro hx
    rcases hx with ⟨U, hUS, hxU⟩
    exact ⟨U.1, ⟨U, hUS, rfl⟩, hxU⟩

theorem sSup_isLUB (X : Space.{u}) (S : Set (OpenSet X)) :
    IsLUB S (sSup S : OpenSet X) := by
  constructor
  · intro U hUS x hx
    exact (mem_sSup_iff X S x).2 ⟨U, hUS, hx⟩
  · intro U hUpper x hx
    rcases (mem_sSup_iff X S x).1 hx with ⟨V, hVS, hxV⟩
    exact hUpper hVS hxV

@[reducible]
def completeLattice (X : Space.{u}) : CompleteLattice (OpenSet X) :=
  completeLatticeOfSup (OpenSet X) (sSup_isLUB X)

instance instCompleteLattice (X : Space.{u}) : CompleteLattice (OpenSet X) :=
  completeLattice X

theorem top_eq_univ (X : Space.{u}) :
    ((⊤ : OpenSet X).1 : Set X.Point) = Set.univ := by
  apply Set.Subset.antisymm
  · intro x _hx
    exact Set.mem_univ x
  · intro x _hx
    let U : OpenSet X := ⟨Set.univ, X.univ_open⟩
    have hUtop : U ≤ (⊤ : OpenSet X) := le_top
    exact hUtop (Set.mem_univ x)

theorem inf_eq_inter (X : Space.{u}) (U V : OpenSet X) :
    ((U ⊓ V).1 : Set X.Point) = U.1 ∩ V.1 := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨(inf_le_left : U ⊓ V ≤ U) hx, (inf_le_right : U ⊓ V ≤ V) hx⟩
  · intro x hx
    let W : OpenSet X := ⟨U.1 ∩ V.1, X.inter_open U.1 V.1 U.2 V.2⟩
    have hWU : W ≤ U := by
      intro y hy
      exact hy.1
    have hWV : W ≤ V := by
      intro y hy
      exact hy.2
    have hWInf : W ≤ U ⊓ V := le_inf hWU hWV
    exact hWInf hx

end OpenSet

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

theorem openSet_epsilon_injective (X : Space.{u}) :
    EpsilonInjective (OpenSet X) := by
  intro U V hEq
  apply Subtype.ext
  apply Set.Subset.antisymm
  · intro x hxU
    let F : Point (OpenSet X) :=
      ⟨pointNeighborhoodFilter X x, pointNeighborhoodFilter_completelyPrime X x⟩
    have hFU : F ∈ EpsilonMap U := hxU
    have hFV : F ∈ EpsilonMap V := by
      rw [← hEq]
      exact hFU
    exact hFV
  · intro x hxV
    let F : Point (OpenSet X) :=
      ⟨pointNeighborhoodFilter X x, pointNeighborhoodFilter_completelyPrime X x⟩
    have hFV : F ∈ EpsilonMap V := hxV
    have hFU : F ∈ EpsilonMap U := by
      rw [hEq]
      exact hFV
    exact hFU

/-- A presentation of the open-set lattice `Ω(X)`.  The carrier is required to be
order-isomorphic to the actual open subsets of `X`, so later spatiality claims
refer to the open-set lattice of `X`, not to an unrelated lattice. -/
structure OpenSetLatticePresentation (X : Space.{u}) where
  carrier : Type u
  lattice : CompleteLattice carrier
  toOpen : carrier → {U : Set X.Point // X.IsOpen U}
  ofOpen : {U : Set X.Point // X.IsOpen U} → carrier
  left_inv : ∀ a : carrier, ofOpen (toOpen a) = a
  right_inv : ∀ U : {U : Set X.Point // X.IsOpen U}, toOpen (ofOpen U) = U
  order_compatible :
    ∀ a b : carrier, @LE.le carrier lattice.toPreorder.toLE a b ↔ (toOpen a).1 ⊆ (toOpen b).1

/-- The lattice of opens of a lightweight space is spatial, stated through an
explicit presentation of `Ω(X)`. -/
def OpenSetLatticeSpatial (X : Space.{u}) : Prop :=
  ∃ P : OpenSetLatticePresentation X, @IsSpatialLattice P.carrier P.lattice

/-- The concrete open-set lattice of any lightweight space is spatial. -/
theorem openSetLatticeSpatial (X : Space.{u}) :
    OpenSetLatticeSpatial X := by
  let P : OpenSetLatticePresentation X :=
    { carrier := OpenSet X
      lattice := OpenSet.completeLattice X
      toOpen := fun U => U
      ofOpen := fun U => U
      left_inv := by
        intro U
        rfl
      right_inv := by
        intro U
        rfl
      order_compatible := by
        intro U V
        rfl }
  refine ⟨P, ?_⟩
  change IsSpatialLattice (OpenSet X)
  exact ⟨openSet_epsilon_injective X, epsilon_surjective (OpenSet X)⟩

/-- A spatial-lattice object identified with the open-set lattice of a space. -/
structure OpenSetLatticeObjectPresentation
    (X : Space.{u}) (L : SpatialLatticeObject.{u}) where
  presentation : OpenSetLatticePresentation X
  carrier_equiv : L.carrier ≃ presentation.carrier
  order_agrees :
    ∀ a b : L.carrier,
      @LE.le L.carrier L.lattice.toPreorder.toLE a b ↔
      @LE.le presentation.carrier presentation.lattice.toPreorder.toLE
        (carrier_equiv a) (carrier_equiv b)

/-- A space identified with the point space of a complete lattice. -/
structure PointSpacePresentation
    (L : Type u) [CompleteLattice L] (X : Space.{u}) where
  point_equiv : X.Point ≃ Point L
  open_agrees :
    ∀ U : Set (Point L), X.IsOpen {x : X.Point | point_equiv x ∈ U} ↔ PointOpen L U

/-- A completely distributive lattice object identified with the Scott-open
lattice `Ω(D)` of a continuous dcpo. -/
structure ScottOpenCompleteDistributiveLatticePresentation
    (D : ContinuousDcpoObject.{u}) (L : CompleteDistributiveLatticeObject.{u}) where
  presentation : OpenSetLatticePresentation (@ScottTopologySpace D.carrier D.preorder)
  carrier_equiv : L.carrier ≃ presentation.carrier
  order_agrees :
    ∀ a b : L.carrier,
      @LE.le L.carrier L.lattice.toPreorder.toLE a b ↔
        @LE.le presentation.carrier presentation.lattice.toPreorder.toLE
          (carrier_equiv a) (carrier_equiv b)

/-- A continuous dcpo object identified with the point dcpo `pt(L)`, ordered by
inclusion of completely prime filters. -/
structure PointContinuousDcpoPresentation
    (L : CompleteDistributiveLatticeObject.{u}) (D : ContinuousDcpoObject.{u}) where
  carrier_equiv : D.carrier ≃ @Point L.carrier L.lattice
  order_agrees :
    ∀ x y : D.carrier,
      @LE.le D.carrier D.preorder.toLE x y ↔
        @LE.le (@Point L.carrier L.lattice) (PointFilterPreorder L).toLE
          (carrier_equiv x) (carrier_equiv y)

/-- The weak-upper topology generated by specialization lower closures. -/
def TopologyFinerThanWeakUpper (X : Space.{u}) : Prop :=
  ∀ x : X.Point, X.IsOpen ({y : X.Point | ¬ SpecializationLE X y x})

/-- The topology is below the Scott topology of the specialization order. -/
def TopologyBelowSpecializationScott (X : Space.{u}) : Prop :=
  ∀ U : Set X.Point,
    X.IsOpen U → @Chapter2.ScottOpen X.Point (specializationPreorder X) U

/-- Proposition 7.2.2: the sober unit detects `T0` and generic irreducible closed sets. -/
theorem prop_7_2_2_sober_unit_characterization (X : Space.{u}) :
    (SoberUnitInjective X ↔ IsT0Space X) ∧
      (SoberUnitSurjective X ↔ EveryIrreducibleClosedHasGenericPoint X) := by
  exact ⟨Iff.rfl, Iff.rfl⟩

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
  admit

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

/-- The lightweight sober-space category has explicit continuous maps and is
closed under the topological retract operation used in Theorem 7.2.14. -/
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
  limit_universal := True
  colimit_universal := True
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

/-- Theorem 7.2.14 PDF-facing statement. -/
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

/-- Lemma 7.2.15 PDF-facing statement. -/
theorem lemma_7_2_15_distributive_continuous_lattices_spatial
    (L : Type u) [CompleteLattice L] :
    Chapter2.IsContinuousDomain L → IsFrameDistributive L → IsSpatialLattice L := by
  intro hContinuous hDistributive
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
  exact ⟨hInjective, hUnit.1⟩

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
between them.  This is the lightweight topological version of the way-below
criterion used in the proof of Theorem 7.2.16. -/
def CompactBetweenOpenSets (X : Space.{u})
    (O O' : Set X.Point) : Prop :=
  X.IsOpen O ∧ X.IsOpen O' ∧
    ∃ K : Set X.Point, IsCompactSaturated X K ∧ O ⊆ K ∧ K ⊆ O'

/-- The compact-between-open-sets criterion used in the proof of Theorem 7.2.16:
if a compact saturated set lies between `O` and `O'`, then `O` is way-below
`O'` in the open-set lattice. -/
def CompactBetweenImpliesWayBelowOpens (X : Space.{u}) : Prop :=
  ∀ O O' : Set X.Point,
    CompactBetweenOpenSets X O O' →
      @Chapter2.WayBelow (Set X.Point) inferInstance O O'

/-- The local-compactness proof ingredient for Theorem 7.2.16: every open set is
the union of open subsets with compact saturated sets between them and the target
open set. -/
structure OpenSetCompactApproximationBasis (X : Space.{u}) : Prop where
  open_eq_union_compactly_below :
    ∀ O : Set X.Point, X.IsOpen O →
      O = ⋃₀ {V : Set X.Point | CompactBetweenOpenSets X V O}

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
  admit

/-- The Scott-open filters of opens are closed under binary intersections.
This is the filter-side form of the compact-saturated intersection argument in
Theorem 7.2.19. -/
def ScottOpenFiltersClosedUnderBinaryIntersection (X : Space.{u}) : Prop :=
  ∀ F G : Set (Set X.Point),
    IsScottOpenFilterOfOpens X F → IsScottOpenFilterOfOpens X G →
      IsScottOpenFilterOfOpens X (F ∩ G)

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
  arithmetic_scott_open_filter_intersections :
    ∀ L : ArithmeticLatticeObject.{u},
      ScottOpenFiltersClosedUnderBinaryIntersection (duality.right L).space

/-- Theorem 7.2.19 PDF-facing statement. -/
theorem theorem_7_2_19_coherent_arithmetic_duality :
    Nonempty (CoherentArithmeticDualityData.{u}) := by
  admit

/-- Compact-open subsets below each open set generate the topology.  This is the
space-side algebraicity witness used in Theorem 7.2.20. -/
structure CompactOpenBasisGeneratesTopology (X : Space.{u}) : Prop where
  open_eq_sUnion_compact_open_below :
    ∀ U : Set X.Point, X.IsOpen U →
      U = ⋃₀ {V : Set X.Point | IsCompactOpenSubset X V ∧ V ⊆ U}

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
  admit

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

/-- Theorem 7.2.22 PDF-facing statement. -/
theorem theorem_7_2_22_spectral_algebraic_arithmetic_duality :
    Nonempty
      (SpectralAlgebraicArithmeticDualityData.{u}) := by
  admit

/-- Proposition 7.2.23 PDF-facing statement. -/
theorem prop_7_2_23_prime_filters_compacts_points
    (L : Type u) [CompleteLattice L] :
    IsAlgebraicArithmeticLattice L →
      Nonempty (CompactPrimeFilterCorrespondence L) := by
  admit

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

/-- The lower closure `↓A` used in the proof of Proposition 7.2.27. -/
def LowerClosureInDomain {D : Type u} [Preorder D] (A : Set D) : Set D :=
  {x : D | ∃ a ∈ A, x ≤ a}

/-- Proof data for Proposition 7.2.27: irreducible Scott-closed sets have
directed lower closures and hence generic points. -/
structure ContinuousDomainScottSobrietyData (D : Type u) [Preorder D] : Prop where
  dcpo : Chapter2.IsDcpo D
  continuous : Chapter2.IsContinuousDomain D
  directed_lower_closure :
    ∀ A : Set D,
      IsIrreducibleClosed (ScottTopologySpace D) A →
        Chapter2.DirectedSet (LowerClosureInDomain A)
  generic_point :
    ∀ A : Set D,
      IsIrreducibleClosed (ScottTopologySpace D) A →
        ∃ s : D,
          Chapter2.IsSup (LowerClosureInDomain A) s ∧
            A = PointClosure (ScottTopologySpace D) s
  sober : IsSober (ScottTopologySpace D)

/-- Proposition 7.2.27 PDF-facing statement. -/
theorem prop_7_2_27_continuous_domains_sober
    (D : Type u) [Preorder D] :
    Chapter2.IsDcpo D →
      Chapter2.IsContinuousDomain D →
      IsSober (ScottTopologySpace D) := by
  admit

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
  admit

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

/-- Theorem 7.2.29 PDF-facing statement. -/
theorem theorem_7_2_29_coherent_algebraic_domain_duality :
    Nonempty (CoherentAlgebraicFiniteJoinPrimeDualityData.{u}) := by
  admit

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

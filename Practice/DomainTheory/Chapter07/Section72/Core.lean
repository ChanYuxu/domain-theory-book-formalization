import Practice.DomainTheory.Chapter07.Section71
import Practice.DomainTheory.Chapter04.Section43

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.2: sober and spatial foundations

This module follows a coherent dependency cluster inside the textbook section.
The stable public import remains `Practice.DomainTheory.Chapter07.Section72`.
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

/-- An irreducible closed set that meets two open sets also meets their
intersection.  This is the open-set form of irreducibility used in the
sobriety proof for continuous domains. -/
theorem irreducibleClosed_exists_mem_open_inter
    {X : Space.{u}} {C U V : Set X.Point}
    (hC : IsIrreducibleClosed X C)
    (hU : X.IsOpen U) (hV : X.IsOpen V)
    (hCU : ∃ x : X.Point, x ∈ C ∧ x ∈ U)
    (hCV : ∃ x : X.Point, x ∈ C ∧ x ∈ V) :
    ∃ x : X.Point, x ∈ C ∧ x ∈ U ∧ x ∈ V := by
  by_contra hNoInter
  have hClosedU : IsClosed X Uᶜ := by
    unfold IsClosed
    simpa using hU
  have hClosedV : IsClosed X Vᶜ := by
    unfold IsClosed
    simpa using hV
  have hSubset : C ⊆ Uᶜ ∪ Vᶜ := by
    intro x hxC
    by_cases hxU : x ∈ U
    · right
      intro hxV
      exact hNoInter ⟨x, hxC, hxU, hxV⟩
    · exact Or.inl hxU
  rcases hC.2.2 Uᶜ Vᶜ hClosedU hClosedV hSubset with hCUcomp | hCVcomp
  · rcases hCU with ⟨x, hxC, hxU⟩
    exact (hCUcomp hxC) hxU
  · rcases hCV with ⟨x, hxC, hxV⟩
    exact (hCVcomp hxC) hxV

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
  Function.Injective (stoneUnitPoint X)

/-- The soberification unit is surjective exactly when irreducible closed sets have
generic points. -/
def SoberUnitSurjective (X : Space.{u}) : Prop :=
  Function.Surjective (stoneUnitPoint X)

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
  exact irreducibleClosed_exists_mem_open_inter hC hU hV hCU hCV

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

instance (L : SpatialLatticeObject.{u}) : CompleteLattice L.carrier := L.lattice

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

instance (L : DistributiveContinuousLatticeObject.{u}) : CompleteLattice L.carrier :=
  L.lattice

/-- Bundled continuous domains in the categorical sense used in Section 7.2:
a dcpo together with a continuous basis.  This is stricter than Chapter 2's
predicate `IsContinuousDomain`, which records only the basis condition. -/
structure ContinuousDcpoObject where
  carrier : Type u
  preorder : Preorder carrier
  antisymm : ∀ {x y : carrier}, preorder.le x y → preorder.le y x → x = y
  dcpo : @Chapter2.IsDcpo carrier preorder
  continuous : @Chapter2.IsContinuousDomain carrier preorder

instance (D : ContinuousDcpoObject.{u}) : Preorder D.carrier := D.preorder

/-- The partial order carried by a continuous dcpo object.  It is installed
locally where APIs require `[PartialOrder]`, so existing definitions that use
the object's explicit `preorder` remain definitionally stable. -/
@[reducible]
def ContinuousDcpoObject.partialOrder (D : ContinuousDcpoObject.{u}) :
    PartialOrder D.carrier where
  toPreorder := D.preorder
  le_antisymm := fun _ _ => D.antisymm

/-- Bundled completely distributive lattices, represented by Raney's complete
choice law from Section 7.1. -/
structure CompleteDistributiveLatticeObject where
  carrier : Type u
  lattice : CompleteLattice carrier
  complete_distributive : @CompleteChoiceMeetJoinLaw.{u, u} carrier lattice

instance (L : CompleteDistributiveLatticeObject.{u}) : CompleteLattice L.carrier :=
  L.lattice

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

instance (L : AlgebraicDistributiveLatticeObject.{u}) : CompleteLattice L.carrier :=
  L.lattice

/-- Bundled coherent spaces. -/
structure CoherentSpaceObject where
  space : Space.{u}
  coherent : IsCoherentSpace space

/-- Bundled arithmetic lattices. -/
structure ArithmeticLatticeObject where
  carrier : Type u
  lattice : CompleteLattice carrier
  arithmetic : @IsArithmeticLattice carrier lattice

instance (L : ArithmeticLatticeObject.{u}) : CompleteLattice L.carrier := L.lattice

/-- Bundled spectral spaces. -/
structure SpectralSpaceObject where
  space : Space.{u}
  spectral : IsSpectralSpace space

/-- Bundled algebraic arithmetic lattices. -/
structure AlgebraicArithmeticLatticeObject where
  carrier : Type u
  lattice : CompleteLattice carrier
  algebraicArithmetic : @IsAlgebraicArithmeticLattice carrier lattice

instance (L : AlgebraicArithmeticLatticeObject.{u}) : CompleteLattice L.carrier :=
  L.lattice

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

instance (L : FiniteJoinPrimeGeneratedLatticeObject.{u}) : CompleteLattice L.carrier :=
  L.lattice

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

/-- Object-level evidence used while constructing the high-level dualities.

This is deliberately not a categorical dual equivalence: it contains no
morphism actions, category or functor laws, naturality, or natural
isomorphisms. Numbered source claims that currently return a structure built
from this record must therefore remain marked `interface-only` in the review
metadata. -/
structure DualEquivalenceData (A : Type u) (B : Type v) where
  left : A → B
  right : B → A
  unit_isomorphism : Prop
  unit_isomorphism_holds : unit_isomorphism
  counit_isomorphism : Prop
  counit_isomorphism_holds : counit_isomorphism

/-- A small record for high-level equivalence theorems whose functors are not
contravariant. -/
structure EquivalenceData (A : Type u) (B : Type v) where
  left : A → B
  right : B → A
  unit_isomorphism : Prop
  unit_isomorphism_holds : unit_isomorphism
  counit_isomorphism : Prop
  counit_isomorphism_holds : counit_isomorphism

namespace DualEquivalenceData

/-- Reverse a bundled dual-equivalence package. -/
def symm {A : Type u} {B : Type v} (d : DualEquivalenceData A B) :
    DualEquivalenceData B A where
  left := d.right
  right := d.left
  unit_isomorphism := d.counit_isomorphism
  unit_isomorphism_holds := d.counit_isomorphism_holds
  counit_isomorphism := d.unit_isomorphism
  counit_isomorphism_holds := d.unit_isomorphism_holds

end DualEquivalenceData

/-- A lightweight object-level prototype for limit, colimit, and retract data.

`Diagram` has no indexing category, `Cone` and `Cocone` have no naturality or
commutativity laws, and the lift/desc data have no factorization or uniqueness
laws. Consequently this structure does not by itself express categorical
completeness or cocompleteness. -/
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

/-- The Stone unit is injective on every `T0` space. -/
theorem stoneUnitPoint_injective_of_t0
    (X : Space.{u}) (hX : IsT0Space X) :
    Function.Injective (stoneUnitPoint X) := by
  intro x y hxy
  by_contra hne
  rcases hX x y hne with ⟨U, hU, hsep⟩
  have hFilters :
      pointNeighborhoodFilter X x = pointNeighborhoodFilter X y :=
    congrArg Subtype.val hxy
  let O : OpenSet X := ⟨U, hU⟩
  rcases hsep with ⟨hxU, hyU⟩ | ⟨hyU, hxU⟩
  · have hxO : O ∈ pointNeighborhoodFilter X x := hxU
    have hyO : O ∈ pointNeighborhoodFilter X y := by
      rw [← hFilters]
      exact hxO
    exact hyU hyO
  · have hyO : O ∈ pointNeighborhoodFilter X y := hyU
    have hxO : O ∈ pointNeighborhoodFilter X x := by
      rw [hFilters]
      exact hyO
    exact hxU hxO

/-- Injectivity of the Stone unit separates distinct points by an open set. -/
theorem t0_of_stoneUnitPoint_injective
    (X : Space.{u}) (hη : Function.Injective (stoneUnitPoint X)) :
    IsT0Space X := by
  intro x y hxy
  by_contra hsep
  apply hxy
  apply hη
  apply Subtype.ext
  ext U
  constructor
  · intro hxU
    by_contra hyU
    exact hsep ⟨U.1, U.2, Or.inl ⟨hxU, hyU⟩⟩
  · intro hyU
    by_contra hxU
    exact hsep ⟨U.1, U.2, Or.inr ⟨hyU, hxU⟩⟩

/-- The injectivity half of Proposition 7.2.2. -/
theorem stoneUnitPoint_injective_iff_t0 (X : Space.{u}) :
    Function.Injective (stoneUnitPoint X) ↔ IsT0Space X := by
  exact ⟨t0_of_stoneUnitPoint_injective X, stoneUnitPoint_injective_of_t0 X⟩

/-- Surjectivity of the Stone unit gives a generic point for every irreducible
closed set. -/
theorem everyIrreducibleClosedHasGenericPoint_of_stoneUnitPoint_surjective
    (X : Space.{u}) (hη : Function.Surjective (stoneUnitPoint X)) :
    EveryIrreducibleClosedHasGenericPoint X := by
  intro C hC
  let meetingFilter : Set (OpenSet X) :=
    {U : OpenSet X | (C ∩ U.1).Nonempty}
  have hMeetingFilter : IsCompletelyPrimeFilter meetingFilter := by
    constructor
    · constructor
      · rcases hC.2.1 with ⟨x, hxC⟩
        refine ⟨x, hxC, ?_⟩
        change x ∈ (⊤ : OpenSet X).1
        rw [OpenSet.top_eq_univ X]
        exact Set.mem_univ x
      · constructor
        · intro U V hU hUV
          rcases hU with ⟨x, hxC, hxU⟩
          exact ⟨x, hxC, hUV hxU⟩
        · intro U V hU hV
          rcases irreducibleClosed_exists_mem_open_inter hC U.2 V.2 hU hV with
            ⟨x, hxC, hxU, hxV⟩
          exact ⟨x, hxC, by
            rw [OpenSet.inf_eq_inter X U V]
            exact ⟨hxU, hxV⟩⟩
    · intro S hSup
      rcases hSup with ⟨x, hxC, hxSup⟩
      rcases (OpenSet.mem_sSup_iff X S x).1 hxSup with ⟨U, hUS, hxU⟩
      exact ⟨U, hUS, ⟨x, hxC, hxU⟩⟩
  let F : Point (OpenSet X) := ⟨meetingFilter, hMeetingFilter⟩
  rcases hη F with ⟨x, hx⟩
  have hFilters : pointNeighborhoodFilter X x = meetingFilter :=
    congrArg Subtype.val hx
  have hOpenMeeting (U : OpenSet X) :
      x ∈ U.1 ↔ (C ∩ U.1).Nonempty := by
    change U ∈ pointNeighborhoodFilter X x ↔ U ∈ meetingFilter
    rw [hFilters]
  refine ⟨x, Set.Subset.antisymm ?_ ?_⟩
  · intro y hyC
    intro U hU hyU
    exact (hOpenMeeting ⟨U, hU⟩).2 ⟨y, hyC, hyU⟩
  · intro y hyClosure
    by_contra hyC
    let U : OpenSet X := ⟨Cᶜ, hC.1⟩
    have hyU : y ∈ U.1 := hyC
    have hxU : x ∈ U.1 := hyClosure U.1 U.2 hyU
    rcases (hOpenMeeting U).1 hxU with ⟨z, hzC, hzU⟩
    exact hzU hzC

/-- Generic points for irreducible closed sets make the Stone unit surjective. -/
theorem stoneUnitPoint_surjective_of_everyIrreducibleClosedHasGenericPoint
    (X : Space.{u}) (hX : EveryIrreducibleClosedHasGenericPoint X) :
    Function.Surjective (stoneUnitPoint X) := by
  intro F
  let S : Set (OpenSet X) := {U : OpenSet X | U ∉ F.1}
  let N : OpenSet X := sSup S
  let C : Set X.Point := N.1ᶜ
  have hMeet (U : OpenSet X) : (C ∩ U.1).Nonempty ↔ U ∈ F.1 := by
    constructor
    · intro hCU
      rcases hCU with ⟨x, hxC, hxU⟩
      by_contra hUF
      have hUS : U ∈ S := hUF
      have hxN : x ∈ N.1 := by
        change x ∈ (sSup S : OpenSet X).1
        exact (OpenSet.mem_sSup_iff X S x).2 ⟨U, hUS, hxU⟩
      exact hxC hxN
    · intro hUF
      by_contra hCU
      have hUN : U ≤ N := by
        intro x hxU
        by_contra hxN
        exact hCU ⟨x, hxN, hxU⟩
      have hNF : N ∈ F.1 := F.2.1.2.1 hUF hUN
      change sSup S ∈ F.1 at hNF
      rcases F.2.2 S hNF with ⟨V, hVS, hVF⟩
      exact hVS hVF
  have hCclosed : IsClosed X C := by
    unfold IsClosed
    simpa [C] using N.2
  have hCnonempty : C.Nonempty := by
    rcases (hMeet (⊤ : OpenSet X)).2 F.2.1.1 with ⟨x, hxC, _hxTop⟩
    exact ⟨x, hxC⟩
  have hCirreducible : IsIrreducibleClosed X C := by
    refine ⟨hCclosed, hCnonempty, ?_⟩
    intro A B hA hB hCAB
    by_cases hCA : C ⊆ A
    · exact Or.inl hCA
    · apply Or.inr
      by_contra hCB
      rcases Set.not_subset.mp hCA with ⟨x, hxC, hxA⟩
      rcases Set.not_subset.mp hCB with ⟨y, hyC, hyB⟩
      let OA : OpenSet X := ⟨Aᶜ, hA⟩
      let OB : OpenSet X := ⟨Bᶜ, hB⟩
      have hOAF : OA ∈ F.1 := (hMeet OA).1 ⟨x, hxC, hxA⟩
      have hOBF : OB ∈ F.1 := (hMeet OB).1 ⟨y, hyC, hyB⟩
      have hInfF : OA ⊓ OB ∈ F.1 := F.2.1.2.2 hOAF hOBF
      rcases (hMeet (OA ⊓ OB)).2 hInfF with ⟨z, hzC, hzInf⟩
      have hzCompl : z ∈ Aᶜ ∩ Bᶜ := by
        rw [← OpenSet.inf_eq_inter X OA OB]
        exact hzInf
      rcases hCAB hzC with hzA | hzB
      · exact hzCompl.1 hzA
      · exact hzCompl.2 hzB
  rcases hX C hCirreducible with ⟨x, hCx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  ext U
  change (x ∈ U.1) ↔ U ∈ F.1
  constructor
  · intro hxU
    have hxx : x ∈ PointClosure X x := by
      change SpecializationLE X x x
      intro V _hV hxV
      exact hxV
    have hxC : x ∈ C := by
      rw [hCx]
      exact hxx
    exact (hMeet U).1 ⟨x, hxC, hxU⟩
  · intro hUF
    rcases (hMeet U).2 hUF with ⟨y, hyC, hyU⟩
    have hyClosure : y ∈ PointClosure X x := by
      rw [← hCx]
      exact hyC
    exact hyClosure U.1 U.2 hyU

/-- The surjectivity half of Proposition 7.2.2. -/
theorem stoneUnitPoint_surjective_iff_generic_points (X : Space.{u}) :
    Function.Surjective (stoneUnitPoint X) ↔
      EveryIrreducibleClosedHasGenericPoint X := by
  exact
    ⟨everyIrreducibleClosedHasGenericPoint_of_stoneUnitPoint_surjective X,
      stoneUnitPoint_surjective_of_everyIrreducibleClosedHasGenericPoint X⟩

/-- For a sober space, the Stone unit `x |-> F_x` is a bijection onto the
completely prime filters of the open-set lattice. -/
theorem stoneUnitPoint_bijective_of_sober
    (X : Space.{u}) (hX : IsSober X) :
    Function.Bijective (stoneUnitPoint X) := by
  constructor
  · intro x y hxy
    by_contra hne
    rcases hX.1 x y hne with ⟨U, hU, hsep⟩
    have hFilters :
        pointNeighborhoodFilter X x = pointNeighborhoodFilter X y :=
      congrArg Subtype.val hxy
    let O : OpenSet X := ⟨U, hU⟩
    rcases hsep with ⟨hxU, hyU⟩ | ⟨hyU, hxU⟩
    · have hxO : O ∈ pointNeighborhoodFilter X x := hxU
      have hyO : O ∈ pointNeighborhoodFilter X y := by
        rw [← hFilters]
        exact hxO
      exact hyU hyO
    · have hyO : O ∈ pointNeighborhoodFilter X y := hyU
      have hxO : O ∈ pointNeighborhoodFilter X x := by
        rw [hFilters]
        exact hyO
      exact hxU hxO
  · intro F
    let S : Set (OpenSet X) := {U : OpenSet X | U ∉ F.1}
    let N : OpenSet X := sSup S
    let C : Set X.Point := N.1ᶜ
    have hMeet (U : OpenSet X) : (C ∩ U.1).Nonempty ↔ U ∈ F.1 := by
      constructor
      · intro hCU
        rcases hCU with ⟨x, hxC, hxU⟩
        by_contra hUF
        have hUS : U ∈ S := hUF
        have hxN : x ∈ N.1 := by
          change x ∈ (sSup S : OpenSet X).1
          exact (OpenSet.mem_sSup_iff X S x).2 ⟨U, hUS, hxU⟩
        exact hxC hxN
      · intro hUF
        by_contra hCU
        have hUN : U ≤ N := by
          intro x hxU
          by_contra hxN
          exact hCU ⟨x, hxN, hxU⟩
        have hNF : N ∈ F.1 := F.2.1.2.1 hUF hUN
        change sSup S ∈ F.1 at hNF
        rcases F.2.2 S hNF with ⟨V, hVS, hVF⟩
        exact hVS hVF
    have hCclosed : IsClosed X C := by
      unfold IsClosed
      simpa [C] using N.2
    have hCnonempty : C.Nonempty := by
      rcases (hMeet (⊤ : OpenSet X)).2 F.2.1.1 with ⟨x, hxC, _hxTop⟩
      exact ⟨x, hxC⟩
    have hCirreducible : IsIrreducibleClosed X C := by
      refine ⟨hCclosed, hCnonempty, ?_⟩
      intro A B hA hB hCAB
      by_cases hCA : C ⊆ A
      · exact Or.inl hCA
      · apply Or.inr
        by_contra hCB
        rcases Set.not_subset.mp hCA with ⟨x, hxC, hxA⟩
        rcases Set.not_subset.mp hCB with ⟨y, hyC, hyB⟩
        let OA : OpenSet X := ⟨Aᶜ, hA⟩
        let OB : OpenSet X := ⟨Bᶜ, hB⟩
        have hOAF : OA ∈ F.1 :=
          (hMeet OA).1 ⟨x, hxC, hxA⟩
        have hOBF : OB ∈ F.1 :=
          (hMeet OB).1 ⟨y, hyC, hyB⟩
        have hInfF : OA ⊓ OB ∈ F.1 := F.2.1.2.2 hOAF hOBF
        rcases (hMeet (OA ⊓ OB)).2 hInfF with ⟨z, hzC, hzInf⟩
        have hzCompl : z ∈ Aᶜ ∩ Bᶜ := by
          rw [← OpenSet.inf_eq_inter X OA OB]
          exact hzInf
        rcases hCAB hzC with hzA | hzB
        · exact hzCompl.1 hzA
        · exact hzCompl.2 hzB
    rcases hX.2 C hCirreducible with ⟨x, hCx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    ext U
    change (x ∈ U.1) ↔ U ∈ F.1
    constructor
    · intro hxU
      have hxx : x ∈ PointClosure X x := by
        change SpecializationLE X x x
        intro V _hV hxV
        exact hxV
      have hxC : x ∈ C := by
        rw [hCx]
        exact hxx
      exact (hMeet U).1 ⟨x, hxC, hxU⟩
    · intro hUF
      rcases (hMeet U).2 hUF with ⟨y, hyC, hyU⟩
      have hyClosure : y ∈ PointClosure X x := by
        rw [← hCx]
        exact hyC
      exact hyClosure U.1 U.2 hyU

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


end Chapter7
end AbramskyJung

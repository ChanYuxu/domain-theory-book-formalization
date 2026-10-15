import Practice.DomainTheory.Chapter02.Section22_AbstractBases

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 2: Section 2.3

Book-facing declarations are kept in source order. Reusable order-theoretic
interfaces remain in `Practice.DomainTheory.Order` and
`Practice.DomainTheory.Topology`.
-/

universe u v w

namespace AbramskyJung
namespace Chapter2

section NumberedCoverageTopology

variable {α : Type u} [Preorder α]

/-- Definition 2.3.1: membership in the Scott interior of a set. -/
def ScottInteriorMem (A : Set α) (x : α) : Prop :=
  ∃ O : Set α, ScottOpen O ∧ O ⊆ A ∧ x ∈ O

/-- Definition 2.3.1: Scott neighborhoods. -/
def ScottNeighborhood (x : α) (O : Set α) : Prop :=
  ScottOpen O ∧ x ∈ O

/-- Proposition 2.3.2(2), local preorder form: the Scott topology is T0 under
the explicit antisymmetry hypothesis used by this file's preorder encoding. -/
theorem prop_2_3_2_2_scott_T0 {x y : α}
    (hanti : ∀ ⦃a b : α⦄, a ≤ b → b ≤ a → a = b)
    (hxy : x ≠ y) :
    (∃ O : Set α, ScottOpen O ∧ ((x ∈ O ∧ y ∉ O) ∨ (y ∈ O ∧ x ∉ O))) := by
  classical
  by_cases hle : x ≤ y
  · have hnot : ¬ y ≤ x := by
      intro hyx
      exact hxy (hanti hle hyx)
    let O : Set α := (lowerClosure ({x} : Set α))ᶜ
    have hO : ScottOpen O := by
      simpa [O, ScottOpen] using scottClosed_principal_ideal x
    have hyO : y ∈ O := by
      intro hy
      rcases hy with ⟨z, hz, hyz⟩
      have hzx : z = x := by simpa using hz
      exact hnot (by simpa [hzx] using hyz)
    have hxO : x ∉ O := by
      intro hx
      exact hx ⟨x, by simp, le_rfl⟩
    exact ⟨O, hO, Or.inr ⟨hyO, hxO⟩⟩
  · let O : Set α := (lowerClosure ({y} : Set α))ᶜ
    have hO : ScottOpen O := by
      simpa [O, ScottOpen] using scottClosed_principal_ideal y
    have hxO : x ∈ O := by
      intro hx
      rcases hx with ⟨z, hz, hxz⟩
      have hzy : z = y := by simpa using hz
      exact hle (by simpa [hzy] using hxz)
    have hyO : y ∉ O := by
      intro hy
      exact hy ⟨y, by simp, le_rfl⟩
    exact ⟨O, hO, Or.inl ⟨hxO, hyO⟩⟩

/-- Proposition 2.3.2(3): Scott topology is Hausdorff exactly for the trivial
order. -/
theorem prop_2_3_2_3_scott_hausdorff_trivial_order :
    (∀ x y : α, x ≠ y →
      ∃ U V : Set α, ScottOpen U ∧ ScottOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V) ↔
    (∀ x y : α, x ≤ y → x = y) := by
  constructor
  · intro hHaus x y hxy
    by_contra hne
    rcases hHaus x y hne with ⟨U, V, hU, hV, hxU, hyV, hdis⟩
    have hyU : y ∈ U := scottOpen_upper hU hxU hxy
    exact Set.disjoint_left.mp hdis hyU hyV
  · intro htriv x y hxy
    have hsingleton : ∀ z : α, ScottOpen ({z} : Set α) := by
      intro z
      constructor
      · intro a b hb hab haz
        exact hb ((htriv a b hab).symm.trans haz)
      · intro A s hA hAs hs hsz
        rcases hA.1 with ⟨a, ha⟩
        have has : a ≤ s := hs.1 ha
        exact hAs ha ((htriv a s has).trans hsz)
    exact ⟨{x}, {y}, hsingleton x, hsingleton y, by simp, by simp,
      Set.disjoint_singleton.mpr hxy⟩

/-- Proposition 2.3.3: directed suprema are characterized by Scott neighborhoods. -/
theorem prop_2_3_3_sup_iff_neighborhoods
    {A : Set α} {x : α} (hA : DirectedSet A) :
    IsSup A x ↔
      IsUpperBound A x ∧
        ∀ O : Set α, ScottNeighborhood x O → ∃ a ∈ A, a ∈ O := by
  constructor
  · intro hx
    constructor
    · exact hx.1
    · intro O hO
      by_contra hnone
      have hAcompl : A ⊆ Oᶜ := by
        intro a ha haO
        exact hnone ⟨a, ha, haO⟩
      have hxcompl : x ∈ Oᶜ := hO.1.2 hA hAcompl hx
      exact hxcompl hO.2
  · intro h
    constructor
    · exact h.1
    · intro y hy
      apply prop_2_3_2_open_to_order
      intro O hO hxO
      rcases h.2 O ⟨hO, hxO⟩ with ⟨a, ha, haO⟩
      exact scottOpen_upper hO haO (hy ha)

/-- Proposition 2.3.4, preorder/existing-suprema form: order-theoretic and
topological Scott-continuity coincide for the unbundled Scott topologies. -/
theorem prop_2_3_4_scottContinuous_iff_topological
    {β : Type v} [Preorder β] {f : α → β} :
    ScottContinuous f ↔ TopologicallyScottContinuous f := by
  constructor
  · exact prop_2_3_4_forward
  · intro hf
    have hmono : Monotone f := by
      intro x y hxy
      apply prop_2_3_2_open_to_order
      intro O hO hfxO
      exact prop_2_3_2_order_to_open hxy (f ⁻¹' O) (hf O hO) hfxO
    constructor
    · exact hmono
    · intro A x hA hx
      constructor
      · intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        exact hmono (hx.1 ha)
      · intro y hy
        apply prop_2_3_2_open_to_order
        intro O hO hfxO
        rcases (prop_2_3_3_sup_iff_neighborhoods hA).1 hx |>.2
            (f ⁻¹' O) ⟨hf O hO, hfxO⟩ with
          ⟨a, ha, hfaO⟩
        exact scottOpen_upper hO hfaO (hy ⟨a, ha, rfl⟩)

/-- In a continuous domain, `↑↑x` is Scott-open. -/
theorem scottOpen_wayBelowUpper
    (hcont : IsContinuousDomain α) (x : α) :
    ScottOpen (wayBelowUpper x) := by
  constructor
  · intro a b hb hab hxa
    exact hb (prop_2_2_2_2 le_rfl hxa hab)
  · intro A s hA hAs hs hxs
    rcases cor_2_2_16_wayBelow_directed_sup hcont hA hs hxs with
      ⟨a, ha, hxa⟩
    exact hAs ha hxa

/-- Proposition 2.3.5: approximation equals membership in the Scott interior of a
principal upper set in continuous domains. -/
theorem prop_2_3_5_wayBelow_iff_scottInterior
    (hcont : IsContinuousDomain α) {x y : α} :
    x ≪ y ↔ ScottInteriorMem (upperClosure ({x} : Set α)) y := by
  have hWayBelowOpen : ScottOpen (wayBelowUpper x) :=
    scottOpen_wayBelowUpper hcont x
  constructor
  · intro hxy
    exact ⟨wayBelowUpper x, hWayBelowOpen, (by
      intro z hz
      exact ⟨x, by simp, prop_2_2_2_1 hz⟩), hxy⟩
  · intro hy
    rcases hy with ⟨O, hO, hOsub, hyO⟩
    intro A s hA hs hys
    have hsO : s ∈ O := scottOpen_upper hO hyO hys
    rcases (prop_2_3_3_sup_iff_neighborhoods hA).1 hs |>.2 O ⟨hO, hsO⟩ with
      ⟨a, ha, haO⟩
    rcases hOsub haO with ⟨z, hz, hza⟩
    have hzx : z = x := by simpa using hz
    exact ⟨a, ha, by simpa [hzx] using hza⟩

/-- Proposition 2.3.5: approximation equals membership in `↑↑x`. -/
theorem prop_2_3_5_wayBelow_iff_wayBelowUpper
    {x y : α} :
    x ≪ y ↔ y ∈ wayBelowUpper x := by
  rfl

/-- Proposition 2.3.6(2): every Scott-open set is supported by basis elements. -/
theorem prop_2_3_6_open_supported_by_basis
    {B O : Set α} (hB : IsBasis B) (hO : ScottOpen O) :
    O = ⋃ x ∈ O ∩ B, wayBelowUpper x := by
  ext y
  constructor
  · intro hy
    have hdir : DirectedSet (Approximants B y) := (hB y).1
    have hsup : IsSup (Approximants B y) y := (hB y).2
    by_contra hnot
    have hcomp : Approximants B y ⊆ Oᶜ := by
      intro b hb hbO
      have hyInUnion : y ∈ ⋃ x ∈ O ∩ B, wayBelowUpper x := by
        rw [Set.mem_iUnion]
        refine ⟨b, ?_⟩
        rw [Set.mem_iUnion]
        exact ⟨⟨hbO, hb.1⟩, hb.2⟩
      exact hnot hyInUnion
    have hyComp : y ∈ Oᶜ := hO.2 hdir hcomp hsup
    exact hyComp hy
  · intro hy
    rw [Set.mem_iUnion] at hy
    rcases hy with ⟨x, hxrest⟩
    rw [Set.mem_iUnion] at hxrest
    rcases hxrest with ⟨hxOB, hxy⟩
    exact scottOpen_upper hO hxOB.1 (prop_2_2_2_1 hxy)

namespace AbstractBasis

variable (B : AbstractBasis.{u})

/-- Proposition 2.3.7: the observable open
`{A : Idl(B) | ∃ x ∈ M, x ∈ A}` generated by a set of abstract-basis elements. -/
def observableOpen (M : Set B.carrier) : Set B.Ideal :=
  {A : B.Ideal | ∃ x ∈ M, x ∈ A.1}

/-- Proposition 2.3.7: all Scott-opens of an ideal completion arise from subsets
of the basis. -/
theorem prop_2_3_7_ideal_completion_opens (M : Set B.carrier) :
    ScottOpen (B.observableOpen M) ∧
      ∀ O : Set B.Ideal, ScottOpen O → ∃ M : Set B.carrier, O = B.observableOpen M := by
  constructor
  · constructor
    · intro A C hC hAC hA
      rcases hA with ⟨x, hxM, hxA⟩
      exact hC ⟨x, hxM, hAC hxA⟩
    · intro A s hA hAcompl hs hsobs
      rcases hsobs with ⟨x, hxM, hxs⟩
      let U : B.Ideal := ⟨{y : B.carrier | ∃ I ∈ A, y ∈ I.1}, B.directedUnionIdeal hA⟩
      have hUupper : IsUpperBound A U := by
        intro I hI y hyI
        exact ⟨I, hI, hyI⟩
      have hsU : s ≤ U := hs.2 U hUupper
      rcases hsU hxs with ⟨I, hI, hxI⟩
      exact hAcompl hI ⟨x, hxM, hxI⟩
  · intro O hO
    let M : Set B.carrier := {x | B.principalIdeal x ∈ O}
    refine ⟨M, ?_⟩
    ext A
    constructor
    · intro hAO
      have hBasis : IsBasis (Set.range B.principalIdeal) :=
        prop_2_2_4_1 B.principalIdealBasisRaw
      have hcover := prop_2_3_6_open_supported_by_basis
        (α := B.Ideal) hBasis hO
      rw [hcover] at hAO
      rw [Set.mem_iUnion] at hAO
      rcases hAO with ⟨I, hrest⟩
      rw [Set.mem_iUnion] at hrest
      rcases hrest with ⟨hIOBasis, hIA⟩
      rcases hIOBasis.2 with ⟨x, rfl⟩
      rcases (B.prop_2_2_22_2_ideal_wayBelow
          (A := B.principalIdeal x) (A' := A)).1 hIA with
        ⟨y, hyA, hx_y⟩
      have hyO : B.principalIdeal y ∈ O :=
        scottOpen_upper hO hIOBasis.1 hx_y
      exact ⟨y, hyO, hyA⟩
    · intro hAobs
      rcases hAobs with ⟨x, hxM, hxA⟩
      have hxA_le : B.principalIdeal x ≤ A := by
        intro y hy
        exact A.property.1 hxA hy
      exact scottOpen_upper hO hxM hxA_le

end AbstractBasis

/-- Definition 2.3.1 topology law: arbitrary unions of Scott-open sets are
Scott-open. -/
theorem scottOpen_iUnion
    {ι : Type v} {U : ι → Set α} (hU : ∀ i : ι, ScottOpen (U i)) :
    ScottOpen (Set.iUnion U) := by
  constructor
  · intro x y hy hxy hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨i, hxi⟩
    exact hy (by
      rw [Set.mem_iUnion]
      exact ⟨i, scottOpen_upper (hU i) hxi hxy⟩)
  · intro A s hA hAs hs hsU
    rw [Set.mem_iUnion] at hsU
    rcases hsU with ⟨i, hsi⟩
    have hsComp : s ∈ (U i)ᶜ := (hU i).2 hA (by
      intro a ha hai
      exact hAs ha (by
        rw [Set.mem_iUnion]
        exact ⟨i, hai⟩)) hs
    exact hsComp hsi

/-- The Scott topology packaged as mathlib's `TopologicalSpace`.  The unbundled
`ScottOpen` predicate remains the source-facing definition, while this bridge
allows later library code to use the standard topology API. -/
@[reducible]
def scottTopologicalSpace : TopologicalSpace α where
  IsOpen := ScottOpen
  isOpen_univ := scottOpen_univ
  isOpen_inter := fun _ _ => scottOpen_inter
  isOpen_sUnion := by
    intro S hS
    have hOpen : ScottOpen (⋃ U : S, (U.1 : Set α)) :=
      scottOpen_iUnion (fun U : S => hS U.1 U.2)
    have hEq : (⋃ U : S, (U.1 : Set α)) = ⋃₀ S := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨U, hxU⟩
        exact Set.mem_sUnion_of_mem hxU U.2
      · intro hx
        rcases Set.mem_sUnion.mp hx with ⟨U, hUS, hxU⟩
        rw [Set.mem_iUnion]
        exact ⟨⟨U, hUS⟩, hxU⟩
    simpa [hEq] using hOpen

theorem isOpen_scottTopologicalSpace_iff {O : Set α} :
    @IsOpen α scottTopologicalSpace O ↔ ScottOpen O :=
  Iff.rfl

/-- Proposition 2.3.6, full iff form: in a continuous domain with basis `B`,
Scott openness is equivalent to each of the two way-below union descriptions
given in the book. -/
theorem prop_2_3_6_scottOpen_iff_supported
    (hcont : IsContinuousDomain α) {B O : Set α} (hB : IsBasis B) :
    ScottOpen O ↔
      O = ⋃ x ∈ O, wayBelowUpper x ∧
        O = ⋃ x ∈ O ∩ B, wayBelowUpper x := by
  constructor
  · intro hO
    exact ⟨prop_2_3_6_open_supported_by_wayBelow hcont hO,
      prop_2_3_6_open_supported_by_basis hB hO⟩
  · rintro ⟨hO, _⟩
    rw [hO]
    constructor
    · intro a b hb hab ha
      rw [Set.mem_iUnion] at ha
      rcases ha with ⟨x, ha⟩
      rw [Set.mem_iUnion] at ha
      rcases ha with ⟨hxO, hxa⟩
      exact hb (by
        rw [Set.mem_iUnion]
        refine ⟨x, ?_⟩
        rw [Set.mem_iUnion]
        exact ⟨hxO, scottOpen_upper (scottOpen_wayBelowUpper hcont x) hxa hab⟩)
    · intro A s hA hAs hs hsUnion
      rw [Set.mem_iUnion] at hsUnion
      rcases hsUnion with ⟨x, hsUnion⟩
      rw [Set.mem_iUnion] at hsUnion
      rcases hsUnion with ⟨hxO, hxs⟩
      have hsComp : s ∈ (wayBelowUpper x)ᶜ :=
        (scottOpen_wayBelowUpper hcont x).2 hA (by
          intro a ha hax
          exact hAs ha (by
            rw [Set.mem_iUnion]
            refine ⟨x, ?_⟩
            rw [Set.mem_iUnion]
            exact ⟨hxO, hax⟩)) hs
      exact hsComp hxs

/-- The first point in an interpolating sequence between `y` and `x`. -/
noncomputable def wayBelowInterpSeed
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    {z : α // y ≪ z} :=
  ⟨Classical.choose (wayBelow_interpolation hcont hyx),
    (Classical.choose_spec (wayBelow_interpolation hcont hyx)).1⟩

theorem wayBelowInterpSeed_wayBelow_target
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    (wayBelowInterpSeed hcont hyx).1 ≪ x :=
  (Classical.choose_spec (wayBelow_interpolation hcont hyx)).2

/-- One interpolation step, keeping the lower endpoint `y` fixed. -/
noncomputable def wayBelowInterpStep
    (hcont : IsContinuousDomain α) {y : α} (p : {z : α // y ≪ z}) :
    {z : α // y ≪ z} :=
  ⟨Classical.choose (wayBelow_interpolation hcont p.2),
    (Classical.choose_spec (wayBelow_interpolation hcont p.2)).1⟩

theorem wayBelowInterpStep_wayBelow_prev
    (hcont : IsContinuousDomain α) {y : α} (p : {z : α // y ≪ z}) :
    (wayBelowInterpStep hcont p).1 ≪ p.1 :=
  (Classical.choose_spec (wayBelow_interpolation hcont p.2)).2

/-- The interpolating sequence used in Lemma 2.3.8. -/
noncomputable def wayBelowInterpPoint
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    Nat → {z : α // y ≪ z}
  | 0 => wayBelowInterpSeed hcont hyx
  | n + 1 => wayBelowInterpStep hcont (wayBelowInterpPoint hcont hyx n)

/-- Values of the interpolating sequence. -/
noncomputable def wayBelowInterpSeq
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    Nat → α :=
  fun n => (wayBelowInterpPoint hcont hyx n).1

theorem wayBelowInterpSeq_source_wayBelow
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) (n : Nat) :
    y ≪ wayBelowInterpSeq hcont hyx n := by
  exact (wayBelowInterpPoint hcont hyx n).2

theorem wayBelowInterpSeq_zero_wayBelow_target
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    wayBelowInterpSeq hcont hyx 0 ≪ x := by
  exact wayBelowInterpSeed_wayBelow_target hcont hyx

theorem wayBelowInterpSeq_succ_wayBelow
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) (n : Nat) :
    wayBelowInterpSeq hcont hyx (n + 1) ≪ wayBelowInterpSeq hcont hyx n := by
  exact wayBelowInterpStep_wayBelow_prev hcont (wayBelowInterpPoint hcont hyx n)

theorem wayBelowInterpSeq_succ_le
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) (n : Nat) :
    wayBelowInterpSeq hcont hyx (n + 1) ≤ wayBelowInterpSeq hcont hyx n :=
  prop_2_2_2_1 (wayBelowInterpSeq_succ_wayBelow hcont hyx n)

theorem wayBelowInterpSeq_le_of_le
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x)
    {m n : Nat} (hmn : m ≤ n) :
    wayBelowInterpSeq hcont hyx n ≤ wayBelowInterpSeq hcont hyx m := by
  induction hmn with
  | refl => exact le_rfl
  | step hmn ih =>
      exact le_trans (wayBelowInterpSeq_succ_le hcont hyx _) ih

/-- The filter generated by the interpolating sequence. -/
noncomputable def interpolatingFilter
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) : Set α :=
  Set.iUnion fun n : Nat => wayBelowUpper (wayBelowInterpSeq hcont hyx n)

theorem interpolatingFilter_scottOpen
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    ScottOpen (interpolatingFilter hcont hyx) := by
  exact scottOpen_iUnion (fun n =>
    scottOpen_wayBelowUpper hcont (wayBelowInterpSeq hcont hyx n))

theorem interpolatingFilter_isFilter
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    IsFilter (interpolatingFilter hcont hyx) := by
  constructor
  · intro a b ha hab
    rw [interpolatingFilter, Set.mem_iUnion] at ha ⊢
    rcases ha with ⟨n, hna⟩
    exact ⟨n, prop_2_2_2_2 le_rfl hna hab⟩
  · constructor
    · refine ⟨x, ?_⟩
      rw [interpolatingFilter, Set.mem_iUnion]
      exact ⟨0, wayBelowInterpSeq_zero_wayBelow_target hcont hyx⟩
    · intro a ha b hb
      rw [interpolatingFilter, Set.mem_iUnion] at ha hb
      rcases ha with ⟨m, hma⟩
      rcases hb with ⟨n, hnb⟩
      let k : Nat := Nat.max m n + 1
      have hmk : m ≤ k := Nat.le_trans (Nat.le_max_left m n) (Nat.le_succ _)
      have hnk : n ≤ k := Nat.le_trans (Nat.le_max_right m n) (Nat.le_succ _)
      refine ⟨wayBelowInterpSeq hcont hyx k, ?_, ?_, ?_⟩
      · rw [interpolatingFilter, Set.mem_iUnion]
        exact ⟨k + 1, wayBelowInterpSeq_succ_wayBelow hcont hyx k⟩
      · exact le_trans (wayBelowInterpSeq_le_of_le hcont hyx hmk)
          (prop_2_2_2_1 hma)
      · exact le_trans (wayBelowInterpSeq_le_of_le hcont hyx hnk)
          (prop_2_2_2_1 hnb)

theorem interpolatingFilter_mem_target
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    x ∈ interpolatingFilter hcont hyx := by
  rw [interpolatingFilter, Set.mem_iUnion]
  exact ⟨0, wayBelowInterpSeq_zero_wayBelow_target hcont hyx⟩

theorem interpolatingFilter_subset_open
    (hcont : IsContinuousDomain α) {O : Set α} (hO : ScottOpen O)
    {y x : α} (hyO : y ∈ O) (hyx : y ≪ x) :
    interpolatingFilter hcont hyx ⊆ O := by
  intro z hz
  rw [interpolatingFilter, Set.mem_iUnion] at hz
  rcases hz with ⟨n, hnz⟩
  have hy_seq : y ≤ wayBelowInterpSeq hcont hyx n :=
    prop_2_2_2_1 (wayBelowInterpSeq_source_wayBelow hcont hyx n)
  have hseq_z : wayBelowInterpSeq hcont hyx n ≤ z := prop_2_2_2_1 hnz
  exact scottOpen_upper hO (scottOpen_upper hO hyO hy_seq) hseq_z

/-- Lemma 2.3.8: Scott-open sets in continuous domains are unions of Scott-open
filters. -/
theorem lemma_2_3_8_scott_open_union_filters
    (hcont : IsContinuousDomain α) {O : Set α} (hO : ScottOpen O) :
    ∃ F : Set (Set α),
      (∀ V ∈ F, ScottOpen V ∧ IsFilter V) ∧ O = ⋃₀ F := by
  let F : Set (Set α) :=
    {V | ∃ x ∈ O, ∃ y ∈ O, ∃ hyx : y ≪ x, V = interpolatingFilter hcont hyx}
  refine ⟨F, ?_, ?_⟩
  · intro V hV
    rcases hV with ⟨x, hxO, y, hyO, hyx, rfl⟩
    exact ⟨interpolatingFilter_scottOpen hcont hyx,
      interpolatingFilter_isFilter hcont hyx⟩
  · ext x
    constructor
    · intro hxO
      have hcover := congrArg (fun S : Set α => x ∈ S)
        (prop_2_3_6_open_supported_by_wayBelow hcont hO)
      have hxUnion : x ∈ ⋃ y ∈ O, wayBelowUpper y := by
        simpa using hcover.mp hxO
      rw [Set.mem_iUnion] at hxUnion
      rcases hxUnion with ⟨y, hyrest⟩
      rw [Set.mem_iUnion] at hyrest
      rcases hyrest with ⟨hyO, hyx⟩
      exact ⟨interpolatingFilter hcont hyx,
        ⟨x, hxO, y, hyO, hyx, rfl⟩,
        interpolatingFilter_mem_target hcont hyx⟩
    · intro hxF
      rcases hxF with ⟨V, hVF, hxV⟩
      rcases hVF with ⟨x₀, _hx₀O, y, hyO, hyx₀, rfl⟩
      exact interpolatingFilter_subset_open hcont hO hyO hyx₀ hxV

end NumberedCoverageTopology

end Chapter2
end AbramskyJung
